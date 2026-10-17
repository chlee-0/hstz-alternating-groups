import HSTZ.ContainedPathSourceDual

/-! The explicit path-only dual satisfies alphabet annihilation but kills all
attachment-row evaluations, so it does not give a common ordered basis or a
nonzero product. Uses flag and row interfaces adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
local notation "pi" => containedPath h hh d (witnessPathSize k) m
local notation "theta" => containedWhole h e hh he d (witnessPathSize k) m

 theorem containedPathTargetDual_high_zero (j : Fin ((theta).colLen 0))
    (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
      (witnessDiagram k b delta hp.staircase_bound).colLen 0)) (hj : d≤j.val) :
    containedPathTargetDual hh he k b delta hp j v=0 := by
  unfold containedPathTargetDual
  split_ifs with hi
  · let x : (pi).cells := ⟨(j.val,0),YoungDiagram.mem_iff_lt_colLen.mpr hi⟩
    have hr : j.val < d := containedPath_row_lt hh d (witnessPathSize k) m x
    omega
  · rfl

 theorem containedPathTargetDual_source_zero (j : Fin ((theta).colLen 0))
    (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
      (witnessDiagram k b delta hp.staircase_bound).colLen 0))
    (hv : ¬(((finProdFinEquiv :
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hp.staircase_bound).colLen 0) ≃ Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)).symm v).1.val<2 ∧
      ((finProdFinEquiv :
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hp.staircase_bound).colLen 0) ≃ Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)).symm v).2.val<2)) :
    containedPathTargetDual hh he k b delta hp j v=0 := by
  unfold containedPathTargetDual
  split_ifs with hj
  · exact containedPathSourceDual_zero hh k b delta hp.staircase_bound _ v hv
  · rfl

 theorem containedPathTargetDual_separated :
    witnessFlagSeparated k b delta hp (fun (j : Fin ((theta).colLen 0)) => j.val < d)
      (containedPathTargetDual (d := d) (m := m) hh he k b delta hp) := by
  intro j v hc hm
  by_cases hj : j.val < d
  · apply containedPathTargetDual_source_zero hh he k b delta hp j v
    intro hv
    exact hm ⟨fun _ => hj,fun _ => hv.1⟩
  · exact containedPathTargetDual_high_zero hh he k b delta hp j v (by omega)

 theorem containedPathTargetDual_attachment_zero {t : ℕ}
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hzero : ∀ c, t≤c → e c=0)
    (r : Fin ((containedAttachment e he m).colLen 0))
    (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
      (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :
    containedPathTargetDual hh he k b delta hp
      (containedAttachmentRowLetter hh he hroom hclear hzero r) v=0 := by
  apply containedPathTargetDual_high_zero hh he k b delta hp
  change d≤d+r.val
  omega
end
end
end HSTZ
#print axioms HSTZ.containedPathTargetDual_high_zero
#print axioms HSTZ.containedPathTargetDual_source_zero
#print axioms HSTZ.containedPathTargetDual_separated
#print axioms HSTZ.containedPathTargetDual_attachment_zero
