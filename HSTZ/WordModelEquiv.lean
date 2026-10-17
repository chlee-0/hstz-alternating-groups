import HSTZ.FinsuppAction
import HSTZ.IntertwiningCompat
import OAI.RepresentationTheory.Saxl.Basic

import HSTZ.CyclicSpan
import HSTZ.PairWords
import OAI.RepresentationTheory.Saxl.SpechtDuality

/-! Coordinates connecting HSTZ finite `Finsupp` words with the Pi-indexed word model `OAI.Saxl.wordRep`
imported from OpenAI's `math` repository. Position movement, coefficients and cyclic
spaces are identified; no witness support or common-flag hypothesis is assumed. -/
namespace HSTZ
open scoped Classical

def positionWordLettersEquiv (n d : ℕ) :
    PositionWord (Fin n) (Fin d) ≃ (Fin n → Fin d) where
  toFun := PositionWord.letters
  invFun := fun a => ⟨a⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def wordModelEquiv (n d : ℕ) :
    (PositionWord (Fin n) (Fin d) →₀ ℂ) ≃ₗ[ℂ] OAI.Saxl.WordSpace n d :=
  Finsupp.domLCongr (positionWordLettersEquiv n d) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin n → Fin d)

@[simp] theorem wordModelEquiv_apply (n d : ℕ)
    (f : PositionWord (Fin n) (Fin d) →₀ ℂ) (a : Fin n → Fin d) :
    wordModelEquiv n d f a = f ⟨a⟩ := by
  simp [wordModelEquiv,Finsupp.domLCongr_apply,Finsupp.domCongr_apply,
    positionWordLettersEquiv]

@[simp] theorem wordModelEquiv_single (n d : ℕ)
    (w : PositionWord (Fin n) (Fin d)) (c : ℂ) :
    wordModelEquiv n d (Finsupp.single w c) = Pi.single w.letters c := by
  simp [wordModelEquiv,positionWordLettersEquiv]

noncomputable def wordModelIntertwiner (n d : ℕ) : Representation.IntertwiningMap
    (finsuppAction ℂ (Equiv.Perm (Fin n)) (PositionWord (Fin n) (Fin d)))
    (OAI.Saxl.wordRep n d) where
  toLinearMap := (wordModelEquiv n d).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    funext a
    change wordModelEquiv n d
      (finsuppAction ℂ (Equiv.Perm (Fin n)) _ g f) a =
        (wordModelEquiv n d f) (a ∘ g)
    rw [wordModelEquiv_apply,finsuppAction_apply,wordModelEquiv_apply]
    congr 1

theorem wordModelIntertwiner_bijective (n d : ℕ) :
    Function.Bijective (wordModelIntertwiner n d) := (wordModelEquiv n d).bijective

noncomputable def wordModelInverseIntertwiner (n d : ℕ) : Representation.IntertwiningMap
    (OAI.Saxl.wordRep n d)
    (finsuppAction ℂ (Equiv.Perm (Fin n)) (PositionWord (Fin n) (Fin d))) where
  toLinearMap := (wordModelEquiv n d).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply (wordModelEquiv n d).injective
    change wordModelEquiv n d ((wordModelEquiv n d).symm (_)) = _
    rw [LinearEquiv.apply_symm_apply]
    have h := (wordModelIntertwiner n d).map_action g ((wordModelEquiv n d).symm f)
    change wordModelEquiv n d
      (finsuppAction ℂ (Equiv.Perm (Fin n))
        (PositionWord (Fin n) (Fin d)) g ((wordModelEquiv n d).symm f)) =
      OAI.Saxl.wordRep n d g (wordModelEquiv n d ((wordModelEquiv n d).symm f)) at h
    exact h.symm

theorem wordModel_cyclic_image (n d : ℕ) (f : PositionWord (Fin n) (Fin d) →₀ ℂ) :
    (cyclicSpan (finsuppAction ℂ (Equiv.Perm (Fin n)) _) f).map
      (wordModelEquiv n d).toLinearMap =
        (OAI.Saxl.cyclic (OAI.Saxl.wordRep n d) (wordModelEquiv n d f)).toSubmodule :=
  cyclicSpan_image (wordModelIntertwiner n d) f

/-- The imported polytabloid, in the original word coordinates. -/
noncomputable def wordPolytabloid {n : ℕ} {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau n mu) : PositionWord (Fin n) (Fin (mu.colLen 0)) →₀ ℂ :=
  (wordModelEquiv n (mu.colLen 0)).symm (OAI.Saxl.polytabloid t)

theorem wordPolytabloid_coefficient {n : ℕ} {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau n mu) : wordPolytabloid t ⟨OAI.Saxl.rowWord t⟩ = 1 := by
  have h := congrFun ((wordModelEquiv n (mu.colLen 0)).apply_symm_apply
    (OAI.Saxl.polytabloid t)) (OAI.Saxl.rowWord t)
  rw [wordModelEquiv_apply,OAI.Saxl.polytabloid_rowWord] at h
  exact h

theorem wordPolytabloid_ne_zero {n : ℕ} {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau n mu) : wordPolytabloid t ≠ 0 := by
  intro h
  have hc := wordPolytabloid_coefficient t
  rw [h] at hc
  exact zero_ne_one hc

/-- Restriction of the inverse coordinates to the prescribed-vector span. -/
noncomputable def wordModelInverseCyclicMap (n d : ℕ)
    (f : PositionWord (Fin n) (Fin d) →₀ ℂ) : Representation.IntertwiningMap
      (OAI.Saxl.cyclic (OAI.Saxl.wordRep n d) (wordModelEquiv n d f)).toRepresentation
      (cyclicSubrepresentation
        (finsuppAction ℂ (Equiv.Perm (Fin n)) _) f).toRepresentation where
  toLinearMap := ((wordModelEquiv n d).symm.toLinearMap.domRestrict
      (OAI.Saxl.cyclic (OAI.Saxl.wordRep n d) (wordModelEquiv n d f)).toSubmodule).codRestrict
    (cyclicSpan (finsuppAction ℂ (Equiv.Perm (Fin n)) _) f) (fun x => by
      have h := cyclicSpan_apply_mem (wordModelInverseIntertwiner n d)
        (wordModelEquiv n d f) x.property
      change (wordModelEquiv n d).symm x.val ∈
        cyclicSpan (finsuppAction ℂ (Equiv.Perm (Fin n)) _)
          ((wordModelEquiv n d).symm (wordModelEquiv n d f)) at h
      rw [LinearEquiv.symm_apply_apply] at h
      exact h)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (wordModelInverseIntertwiner n d).map_action g x.val

theorem wordModelInverseCyclicMap_injective (n d : ℕ)
    (f : PositionWord (Fin n) (Fin d) →₀ ℂ) :
    Function.Injective (wordModelInverseCyclicMap n d f) := by
  intro x y h
  apply Subtype.ext
  apply (wordModelEquiv n d).symm.injective
  exact congrArg Subtype.val h

/-- Transport a given Specht-support map to the original word orbit.
The nonzero native-model support map is an explicit hypothesis. -/
theorem wordModel_support_embedding {n d : ℕ} {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau n mu) (f : PositionWord (Fin n) (Fin d) →₀ ℂ)
    (F : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (OAI.Saxl.cyclic (OAI.Saxl.wordRep n d) (wordModelEquiv n d f)).toRepresentation)
    (hF : F ≠ 0) :
    ∃ Q : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation
        (finsuppAction ℂ (Equiv.Perm (Fin n)) _) f).toRepresentation,
        Function.Injective Q := by
  letI := OAI.Saxl.specht_irreducible t
  have hi := (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF
  exact ⟨(wordModelInverseCyclicMap n d f).comp F,
    (wordModelInverseCyclicMap_injective n d f).comp hi⟩

theorem wordModel_filter_coefficient (n d : ℕ)
    (S : Set (PositionWord (Fin n) (Fin d)))
    (f : PositionWord (Fin n) (Fin d) →₀ ℂ) (a : Fin n → Fin d) :
    wordModelEquiv n d (coordinateFilter S f) a =
      if (⟨a⟩ : PositionWord (Fin n) (Fin d)) ∈ S then wordModelEquiv n d f a else 0 := by
  simp

/-- A real prescribed vector and one nonzero column contraction give
a Specht embedding into its original `Finsupp` orbit span. -/
theorem wordModel_contraction_support {n d : ℕ} {mu : YoungDiagram}
    (t : OAI.Saxl.Tableau n mu) (f : PositionWord (Fin n) (Fin d) →₀ ℂ)
    (L : Fin (mu.colLen 0) → Fin d → ℂ)
    (hf : star (wordModelEquiv n d f) = wordModelEquiv n d f)
    (h : dotProduct (OAI.Saxl.wordMap L (OAI.Saxl.polytabloid t))
      (wordModelEquiv n d f) ≠ 0) :
    ∃ Q : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation
        (finsuppAction ℂ (Equiv.Perm (Fin n)) _) f).toRepresentation,
        Function.Injective Q := by
  obtain ⟨F,hF⟩ := OAI.Saxl.hom_to_cyclic_of_pair L (OAI.Saxl.spechtSub t)
    ⟨OAI.Saxl.polytabloid t,OAI.Saxl.mem_cyclic _ _⟩ (wordModelEquiv n d f) hf h
  exact wordModel_support_embedding t f F hF

end HSTZ

#print axioms OAI.Saxl.columnAlt_tabloid
#print axioms OAI.Saxl.specht_detect
#print axioms OAI.Saxl.specht_cyclic_of_ne_zero
#print axioms OAI.Saxl.specht_irreducible
#print axioms HSTZ.wordModelIntertwiner_bijective
#print axioms HSTZ.wordModel_cyclic_image
#print axioms HSTZ.wordPolytabloid_coefficient
#print axioms HSTZ.wordPolytabloid_ne_zero
#print axioms HSTZ.wordModelInverseCyclicMap_injective
#print axioms HSTZ.wordModel_support_embedding
#print axioms OAI.Saxl.spechtSelfDual
#print axioms OAI.Saxl.hom_to_cyclic_of_pair
#print axioms HSTZ.wordModel_filter_coefficient
#print axioms HSTZ.wordModel_contraction_support
