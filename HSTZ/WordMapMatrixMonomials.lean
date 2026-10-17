import HSTZ.WordMapPairOrbits
import Mathlib.Algebra.MvPolynomial.Funext

/-! Rectangular `wordMap` monomials and finite polynomial separation.
Reuses `wordMap` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0) and Mathlib's
`MvPolynomial`. No full intertwiner-span or attachment coefficient statement is proved here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def wordPairMonomial {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    MvPolynomial (Fin d × Fin e) ℂ := ∏ i, MvPolynomial.X (a i,b i)

theorem wordPairMonomial_eq {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    wordPairMonomial a b = MvPolynomial.monomial (wordPairExponent a b) 1 := by
  classical
  simpa only [wordPairMonomial,wordPairExponent,MvPolynomial.X] using
    (MvPolynomial.monomial_sum_one (R := ℂ) Finset.univ
      (fun i => Finsupp.single (a i,b i) 1)).symm

theorem wordPairMonomial_eval {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (a : Fin n → Fin d) (b : Fin n → Fin e) :
    MvPolynomial.eval (fun j => L j.1 j.2) (wordPairMonomial a b) =
      wordMap L (Pi.single a 1) b := by
  classical
  simp [wordPairMonomial,wordMap_single]

theorem wordPairMonomial_eq_iff {n d e : ℕ}
    (a c : Fin n → Fin d) (b z : Fin n → Fin e) :
    wordPairMonomial a b = wordPairMonomial c z ↔
      ∃ g : Equiv.Perm (Fin n), c ∘ g = a ∧ z ∘ g = b := by
  rw [wordPairMonomial_eq,wordPairMonomial_eq]
  exact (MvPolynomial.monomial_left_injective (one_ne_zero : (1 : ℂ) ≠ 0)).eq_iff.trans
    (wordPairExponent_eq_iff a c b z)

def wordMatrixPolynomial {n d e : ℕ}
    (C : (Fin n → Fin d) → (Fin n → Fin e) → ℂ) :
    MvPolynomial (Fin d × Fin e) ℂ :=
  ∑ a, ∑ b, MvPolynomial.C (C a b) * wordPairMonomial a b

theorem wordMatrixPolynomial_eval {n d e : ℕ}
    (C : (Fin n → Fin d) → (Fin n → Fin e) → ℂ) (L : Fin d → Fin e → ℂ) :
    MvPolynomial.eval (fun j => L j.1 j.2) (wordMatrixPolynomial C) =
      ∑ a, ∑ b, C a b * wordMap L (Pi.single a 1) b := by
  classical
  simp [wordMatrixPolynomial,wordPairMonomial_eval]

theorem wordMatrixPolynomial_coeff {n d e : ℕ}
    (C : (Fin n → Fin d) → (Fin n → Fin e) → ℂ) (p : (Fin d × Fin e) →₀ ℕ) :
    (wordMatrixPolynomial C).coeff p =
      ∑ a, ∑ b, if wordPairExponent a b = p then C a b else 0 := by
  classical
  simp [wordMatrixPolynomial,wordPairMonomial_eq,MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul,MvPolynomial.coeff_monomial]

theorem wordMatrixPolynomial_zero {n d e : ℕ}
    (C : (Fin n → Fin d) → (Fin n → Fin e) → ℂ)
    (h : ∀ L : Fin d → Fin e → ℂ,
      ∑ a, ∑ b, C a b * wordMap L (Pi.single a 1) b = 0) :
    wordMatrixPolynomial C = 0 := by
  apply MvPolynomial.funext
  intro x
  have he := wordMatrixPolynomial_eval C (fun i j => x (i,j))
  simpa only [Prod.eta, map_zero] using he.trans (h (fun i j => x (i,j)))

theorem wordMap_orbit_coefficient_sum_zero {n d e : ℕ}
    (C : (Fin n → Fin d) → (Fin n → Fin e) → ℂ)
    (h : ∀ L : Fin d → Fin e → ℂ,
      ∑ a, ∑ b, C a b * wordMap L (Pi.single a 1) b = 0)
    (p : (Fin d × Fin e) →₀ ℕ) :
    (∑ a, ∑ b, if wordPairExponent a b = p then C a b else 0) = 0 := by
  rw [← wordMatrixPolynomial_coeff,wordMatrixPolynomial_zero C h]
  simp
end
end HSTZ
#print axioms HSTZ.wordPairMonomial_eq
#print axioms HSTZ.wordPairMonomial_eval
#print axioms HSTZ.wordPairMonomial_eq_iff
#print axioms HSTZ.wordMatrixPolynomial_eval
#print axioms HSTZ.wordMatrixPolynomial_coeff
#print axioms HSTZ.wordMatrixPolynomial_zero
#print axioms HSTZ.wordMap_orbit_coefficient_sum_zero
