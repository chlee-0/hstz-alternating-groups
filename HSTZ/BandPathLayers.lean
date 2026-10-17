import HSTZ.IntertwiningCompat
import OAI.RepresentationTheory.Saxl.PathAlternation

import HSTZ.PositionRelabel

namespace HSTZ
open scoped Classical TensorProduct

/-- Full large-alphabet formula, stronger than evaluation on only binary words. -/
theorem bandRow_reindexed (h : ℕ) (w : Fin (2*(h+1)+1) → Fin ((OAI.Saxl.staircase (h+2)).colLen 0)) :
    OAI.Saxl.bandRowWord h 2 (w ∘ (OAI.Saxl.bandPathEquiv h).symm) =
      OAI.Saxl.letterLift (OAI.Saxl.lowLetter h) (OAI.Saxl.PathLayer.rowAlt (h+1)) w := by
  unfold OAI.Saxl.bandRowWord OAI.Saxl.bandRowGroup
  rw [OAI.Saxl.altWord_fiber_relabel,OAI.Saxl.bandRow_path_group,OAI.Saxl.bandRow_path_base,
    ← OAI.Saxl.letterLift_altWord]
  rfl

theorem bandColumn_reindexed (h : ℕ) (w : Fin (2*(h+1)+1) → Fin ((OAI.Saxl.staircase (h+2)).colLen 0)) :
    OAI.Saxl.bandColumnWord h 2 (w ∘ (OAI.Saxl.bandColumnPathEquiv h).symm) =
      OAI.Saxl.letterLift (OAI.Saxl.lowLetter h) (OAI.Saxl.PathLayer.rowAlt (h+1)) w := by
  unfold OAI.Saxl.bandColumnWord OAI.Saxl.bandColumnGroup
  rw [OAI.Saxl.altWord_fiber_relabel,OAI.Saxl.bandColumn_path_group,OAI.Saxl.bandColumn_path_base,
    ← OAI.Saxl.letterLift_altWord]
  rfl

theorem bandRowWord_path (h : ℕ) :
    OAI.Saxl.bandRowWord h 2 = positionRelabel (OAI.Saxl.bandPathEquiv h)
      (OAI.Saxl.letterLift (OAI.Saxl.lowLetter h) (OAI.Saxl.PathLayer.rowAlt (h+1))) := by
  funext w
  have he := bandRow_reindexed h (w ∘ OAI.Saxl.bandPathEquiv h)
  have hw : (w ∘ OAI.Saxl.bandPathEquiv h) ∘ (OAI.Saxl.bandPathEquiv h).symm = w := by
    funext i
    simp
  rw [hw] at he
  exact he

theorem bandColumnWord_path (h : ℕ) :
    OAI.Saxl.bandColumnWord h 2 = positionRelabel (OAI.Saxl.bandPathEquiv h)
      (OAI.Saxl.letterLift (OAI.Saxl.lowLetter h)
        (OAI.Saxl.wordRep _ 2 Fin.revPerm (OAI.Saxl.PathLayer.rowAlt (h+1)))) := by
  funext w
  change OAI.Saxl.bandColumnWord h 2 w =
    OAI.Saxl.letterLift (OAI.Saxl.lowLetter h)
      (OAI.Saxl.wordRep _ 2 Fin.revPerm (OAI.Saxl.PathLayer.rowAlt (h+1)))
        (w ∘ OAI.Saxl.bandPathEquiv h)
  have hl : OAI.Saxl.letterLift (OAI.Saxl.lowLetter h)
      (OAI.Saxl.wordRep _ 2 Fin.revPerm (OAI.Saxl.PathLayer.rowAlt (h+1)))
        (w ∘ OAI.Saxl.bandPathEquiv h) =
      OAI.Saxl.letterLift (OAI.Saxl.lowLetter h) (OAI.Saxl.PathLayer.rowAlt (h+1))
        ((w ∘ OAI.Saxl.bandPathEquiv h) ∘ Fin.revPerm) :=
    congrFun ((OAI.Saxl.letterLift (OAI.Saxl.lowLetter h)).map_action Fin.revPerm
      (OAI.Saxl.PathLayer.rowAlt (h+1))) (w ∘ OAI.Saxl.bandPathEquiv h)
  have he := bandColumn_reindexed h ((w ∘ OAI.Saxl.bandPathEquiv h) ∘ Fin.revPerm)
  have hw : ((w ∘ OAI.Saxl.bandPathEquiv h) ∘ Fin.revPerm) ∘
      (OAI.Saxl.bandColumnPathEquiv h).symm = w := by
    funext i
    simp [OAI.Saxl.bandColumnPathEquiv]
  rw [hw] at he
  exact he.trans hl.symm

end HSTZ
#print axioms HSTZ.bandRow_reindexed
#print axioms HSTZ.bandColumn_reindexed
#print axioms HSTZ.bandRowWord_path
#print axioms HSTZ.bandColumnWord_path
