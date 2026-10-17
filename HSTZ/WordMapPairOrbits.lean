import HSTZ.IntertwiningCompat
import OAI.RepresentationTheory.Saxl.YoungRule

import OAI.RepresentationTheory.Saxl.StaircaseTensor

/-! Rectangular pair-word orbits, toward the span of `wordMap`s. Uses
`mergeWords` and `perm_of_equal_content` adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Covers the full position group and
all degrees and alphabets. No `wordMap` span, attachment matrix coefficient or
common flag is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- Multiplicities of the rectangular matrix-entry coordinates. -/
def wordPairExponent {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    (Fin d × Fin e) →₀ ℕ := ∑ i, Finsupp.single (a i,b i) 1

theorem wordPairExponent_apply {n d e : ℕ}
    (a : Fin n → Fin d) (b : Fin n → Fin e) (j : Fin d × Fin e) :
    wordPairExponent a b j =
      (Finset.univ.filter (fun i => (a i,b i)=j)).card := by
  classical
  simp [wordPairExponent,Finsupp.single_apply,eq_comm]

theorem wordPairExponent_move {n d e : ℕ}
    (a : Fin n → Fin d) (b : Fin n → Fin e) (g : Equiv.Perm (Fin n)) :
    wordPairExponent (a ∘ g) (b ∘ g) = wordPairExponent a b := by
  exact Equiv.sum_comp g (fun i => Finsupp.single (a i,b i) 1)

/-- Equal pair content is exactly a simultaneous position orbit. -/
theorem wordPairExponent_eq_iff {n d e : ℕ}
    (a c : Fin n → Fin d) (b z : Fin n → Fin e) :
    wordPairExponent a b = wordPairExponent c z ↔
      ∃ g : Equiv.Perm (Fin n), c ∘ g = a ∧ z ∘ g = b := by
  classical
  constructor
  · intro h
    have hc : ∀ j, (Finset.univ.filter (fun i => mergeWords a b i=j)).card =
        (Finset.univ.filter (fun i => mergeWords c z i=j)).card := by
      intro j
      have he := congrArg (fun q : (Fin d × Fin e) →₀ ℕ => q (finProdFinEquiv.symm j)) h
      rw [wordPairExponent_apply,wordPairExponent_apply] at he
      simpa only [mergeWords,Equiv.apply_eq_iff_eq_symm_apply] using he
    obtain ⟨g,hg⟩ := perm_of_equal_content (mergeWords a b) (mergeWords c z) hc
    refine ⟨g,?_,?_⟩
    · funext i
      simpa only [mergeWords,Function.comp_apply,Equiv.symm_apply_apply] using
        congrArg (fun v : Fin (d*e) => (finProdFinEquiv.symm v).1) (congrFun hg i)
    · funext i
      simpa only [mergeWords,Function.comp_apply,Equiv.symm_apply_apply] using
        congrArg (fun v : Fin (d*e) => (finProdFinEquiv.symm v).2) (congrFun hg i)
  · rintro ⟨g,ha,hb⟩
    rw [← ha,← hb,wordPairExponent_move]

/-- The coefficients of a full-group intertwiner are constant on orbits. -/
theorem wordIntertwiner_coefficient_move {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (a : Fin n → Fin d) (b : Fin n → Fin e) (g : Equiv.Perm (Fin n)) :
    F (Pi.single (a ∘ g) 1) (b ∘ g) = F (Pi.single a 1) b := by
  have he := congrFun (F.map_action g⁻¹ (Pi.single a 1)) (b ∘ g)
  rw [wordRep_single] at he
  simpa [wordRep,Function.comp_assoc] using he

theorem wordIntertwiner_coefficient_eq {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (a c : Fin n → Fin d) (b z : Fin n → Fin e)
    (h : wordPairExponent a b = wordPairExponent c z) :
    F (Pi.single a 1) b = F (Pi.single c 1) z := by
  obtain ⟨g,ha,hb⟩ := (wordPairExponent_eq_iff a c b z).mp h
  rw [← ha,← hb]
  exact wordIntertwiner_coefficient_move F c z g

end
end HSTZ
#print axioms HSTZ.wordPairExponent_apply
#print axioms HSTZ.wordPairExponent_move
#print axioms HSTZ.wordPairExponent_eq_iff
#print axioms HSTZ.wordIntertwiner_coefficient_move
#print axioms HSTZ.wordIntertwiner_coefficient_eq
