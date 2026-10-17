import HSTZ.WordMapMatrixMonomials
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The span of rectangular `wordMap`s, from simultaneous orbits and polynomial
separation. Uses word interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0)
and Mathlib's finite fiber sums, dual annihilators and span images. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- The finite matrix coefficients of a full position-group map. -/
def wordCoefficientMap (n d e : ℕ) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n e) →ₗ[ℂ]
      ((Fin n → Fin d) → (Fin n → Fin e) → ℂ) where
  toFun F a b := F (Pi.single a 1) b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem wordCoefficientMap_injective (n d e : ℕ) :
    Function.Injective (wordCoefficientMap n d e) := by
  classical
  intro F G h
  have hs : ∀ a, F.toLinearMap (Pi.single a 1) = G.toLinearMap (Pi.single a 1) := by
    intro a
    funext b
    exact congrFun (congrFun h a) b
  apply Representation.IntertwiningMap.toLinearMap_injective
  apply LinearMap.ext
  intro x
  have hx : x = ∑ a, x a • (Pi.single a (1 : ℂ) : WordSpace n d) := by
    ext a
    simp [Pi.single_apply]
  rw [hx,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_smul,map_smul,hs a]

/-- Polynomial annihilation of all `wordMap`s annihilates every intertwiner. -/
theorem wordMap_weighted_intertwiner_zero {n d e : ℕ}
    (C : (Fin n → Fin d) → (Fin n → Fin e) → ℂ)
    (h : ∀ L : Fin d → Fin e → ℂ,
      ∑ a, ∑ b, C a b * wordMap L (Pi.single a 1) b = 0)
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e)) :
    (∑ a, ∑ b, C a b * F (Pi.single a 1) b) = 0 := by
  classical
  let q : ((Fin n → Fin d) × (Fin n → Fin e)) → (Fin d × Fin e) →₀ ℕ :=
    fun w => wordPairExponent w.1 w.2
  let S := Finset.univ.image q
  have hm : ∀ w ∈ Finset.univ, q w ∈ S := fun w hw => Finset.mem_image_of_mem q hw
  have hf := Finset.sum_fiberwise_of_maps_to hm
    (fun w => C w.1 w.2 * F (Pi.single w.1 1) w.2)
  have hz : ∀ p ∈ S, (∑ w ∈ Finset.univ with q w = p,
      C w.1 w.2 * F (Pi.single w.1 1) w.2) = 0 := by
    intro p hp
    obtain ⟨v,hv,hvp⟩ := Finset.mem_image.mp hp
    have hc : (∑ w ∈ Finset.univ with q w = p, C w.1 w.2) = 0 := by
      rw [Finset.sum_filter,Fintype.sum_prod_type]
      exact wordMap_orbit_coefficient_sum_zero C h p
    calc
      _ = ∑ w ∈ Finset.univ with q w = p,
          C w.1 w.2 * F (Pi.single v.1 1) v.2 := by
        apply Finset.sum_congr rfl
        intro w hw
        congr 1
        exact wordIntertwiner_coefficient_eq F w.1 v.1 w.2 v.2
          ((Finset.mem_filter.mp hw).2.trans hvp.symm)
      _ = (∑ w ∈ Finset.univ with q w = p, C w.1 w.2) *
          F (Pi.single v.1 1) v.2 := (Finset.sum_mul _ _ _).symm
      _ = 0 := by rw [hc,zero_mul]
  rw [Fintype.sum_prod_type] at hf
  rw [← hf]
  exact Finset.sum_eq_zero hz

private theorem coefficient_dual_expansion {n d e : ℕ}
    (phi : Module.Dual ℂ ((Fin n → Fin d) → (Fin n → Fin e) → ℂ))
    (x : (Fin n → Fin d) → (Fin n → Fin e) → ℂ) :
    phi x = ∑ a, ∑ b, phi (Pi.single a (Pi.single b 1)) * x a b := by
  classical
  have hx : x = ∑ a, ∑ b, x a b •
      (Pi.single a (Pi.single b (1 : ℂ)) :
        (Fin n → Fin d) → (Fin n → Fin e) → ℂ) := by
    ext a b
    simp [Finset.sum_apply,Pi.single_apply,Pi.smul_apply,smul_eq_mul,ite_apply]
  conv_lhs => rw [hx]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact mul_comm _ _

/-- Every full position-group intertwiner lies in the complex span of the
rectangular tensor-power `wordMap`s, including degree zero and empty alphabets. -/
theorem wordIntertwiner_mem_wordMap_span {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e)) :
    F ∈ Submodule.span ℂ (Set.range (fun L : Fin d → Fin e → ℂ => wordMap (n := n) L)) := by
  classical
  let K := wordCoefficientMap n d e
  let S := Set.range (fun L : Fin d → Fin e → ℂ => wordMap (n := n) L)
  apply (Submodule.apply_mem_span_image_iff_mem_span (f := K)
    (wordCoefficientMap_injective n d e)).mp
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
    (Submodule.span ℂ (K '' S)) (K F)).mp
  intro phi hphi
  let C := fun a b => phi (Pi.single a (Pi.single b 1))
  have hC : ∀ L : Fin d → Fin e → ℂ,
      ∑ a, ∑ b, C a b * wordMap L (Pi.single a 1) b = 0 := by
    intro L
    have hmem : K (wordMap (n := n) L) ∈ Submodule.span ℂ (K '' S) :=
      Submodule.subset_span ⟨wordMap L,⟨L,rfl⟩,rfl⟩
    have hz := (Submodule.mem_dualAnnihilator phi).mp hphi _ hmem
    rw [coefficient_dual_expansion] at hz
    exact hz
  rw [coefficient_dual_expansion]
  exact wordMap_weighted_intertwiner_zero C hC F

end
end HSTZ
#print axioms HSTZ.wordCoefficientMap_injective
#print axioms HSTZ.wordMap_weighted_intertwiner_zero
#print axioms HSTZ.wordIntertwiner_mem_wordMap_span
