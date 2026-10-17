import HSTZ.WitnessMarkedLetters
import OAI.RepresentationTheory.Saxl.CoordinateSector

/-! Unequal-alphabet paired word and common-mask coordinate filter. Adapted from
`sameHighProjection` in OpenAI's `math` repository (commit adc7f1241, Apache-2.0),
using the witness masks. No rotated generator or shuffle phase is identified. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

def witnessCommonMask (n d e k b : ℕ) (w : Fin n → Fin (d*e)) : Prop :=
  ∀ i, witnessRowMarked k b (@splitLeft n d e w i).val ↔
    witnessColumnMarked k (@splitRight n d e w i).val

theorem witnessCommonMask_perm (n d e k b : ℕ)
    (g : Equiv.Perm (Fin n)) (w : Fin n → Fin (d*e)) :
    witnessCommonMask n d e k b (w ∘ g) ↔ witnessCommonMask n d e k b w := by
  constructor
  · intro hw i
    have hh := hw (g.symm i)
    simpa only [splitLeft,splitRight,Function.comp_apply,Equiv.apply_symm_apply] using hh
  · intro hw i
    exact hw (g i)

def witnessMaskProjection (n d e k b : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*e)) (wordRep n (d*e)) where
  toLinearMap := coordinateProjection (witnessCommonMask n d e k b)
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    classical
    funext w
    change (if witnessCommonMask n d e k b w then z (w ∘ g) else 0) =
      (if witnessCommonMask n d e k b (w ∘ g) then z (w ∘ g) else 0)
    rw [propext (witnessCommonMask_perm n d e k b g w)]

theorem witnessMaskProjection_apply (n d e k b : ℕ)
    (z : WordSpace n (d*e)) (w : Fin n → Fin (d*e)) :
    witnessMaskProjection n d e k b z w =
      if witnessCommonMask n d e k b w then z w else 0 := by
  classical
  exact coordinateProjection_apply (witnessCommonMask n d e k b) z w

theorem witnessMaskProjection_nonzero_iff (n d e k b : ℕ)
    (z : WordSpace n (d*e)) (w : Fin n → Fin (d*e)) :
    witnessMaskProjection n d e k b z w ≠ 0 ↔
      witnessCommonMask n d e k b w ∧ z w ≠ 0 := by
  classical
  rw [witnessMaskProjection_apply]
  by_cases h : witnessCommonMask n d e k b w <;> simp [h]

theorem witnessMaskProjection_idempotent (n d e k b : ℕ)
    (z : WordSpace n (d*e)) :
    witnessMaskProjection n d e k b (witnessMaskProjection n d e k b z) =
      witnessMaskProjection n d e k b z := by
  classical
  funext w
  simp only [witnessMaskProjection_apply]
  by_cases h : witnessCommonMask n d e k b w <;> simp [h]

end
end HSTZ
#print axioms HSTZ.witnessCommonMask_perm
#print axioms HSTZ.witnessMaskProjection
#print axioms HSTZ.witnessMaskProjection_apply
#print axioms HSTZ.witnessMaskProjection_nonzero_iff
#print axioms HSTZ.witnessMaskProjection_idempotent
