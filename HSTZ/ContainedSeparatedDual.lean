import HSTZ.ContainedAttachmentMatrixCoefficient
import HSTZ.ContainedPathDualFlags

/-! Extending the path and attachment duals to disjoint target rows preserves both
prescribed coefficients, and the combined dual is flag-separated. Uses `wordMap` and
placement declarations from OpenAI's `math` repository (commit adc7f1241,
Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
local notation "pi" => containedPath h hh d (witnessPathSize k) m
local notation "E" => containedAttachment e he m
local notation "theta" => containedWhole h e hh he d (witnessPathSize k) m
variable (N : Fin ((containedAttachment e he m).colLen 0) → Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)

def containedAttachmentTargetDual : Fin ((theta).colLen 0) → Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ :=
  fun j v => if hr : d ≤ j.val ∧ j.val-d < (E).colLen 0 then
    containedAttachmentMatrixCut
      (D := (witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0)
      (H := (witnessDiagram k b delta hp.staircase_bound).colLen 0) N ⟨j.val-d,hr.2⟩ v else 0

theorem containedAttachmentTargetDual_low_zero (j : Fin ((theta).colLen 0))
    (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) (hj : j.val < d) :
    containedAttachmentTargetDual hh he k b delta hp N j v=0 := by
  unfold containedAttachmentTargetDual
  exact dif_neg (by omega)

theorem containedAttachmentTargetDual_source_zero (j : Fin ((theta).colLen 0))
    (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
    (hv : ¬(2 ≤ ((finProdFinEquiv :
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hp.staircase_bound).colLen 0) ≃
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)).symm v).1.val ∧ ((finProdFinEquiv :
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hp.staircase_bound).colLen 0) ≃
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)).symm v).2.val<2)) :
    containedAttachmentTargetDual hh he k b delta hp N j v=0 := by
  unfold containedAttachmentTargetDual
  split_ifs with hr
  · exact if_neg hv
  · rfl

theorem containedAttachmentTargetDual_attachment
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hzero : ∀ c, t≤c → e c=0) (r : Fin ((E).colLen 0)) (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :
    containedAttachmentTargetDual hh he k b delta hp N
      (containedAttachmentRowLetter hh he hroom hclear hzero r) v =
      containedAttachmentMatrixCut
      (D := (witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0)
      (H := (witnessDiagram k b delta hp.staircase_bound).colLen 0) N r v := by
  unfold containedAttachmentTargetDual
  change (if hr : d≤d+r.val ∧ d+r.val-d < (E).colLen 0 then
    containedAttachmentMatrixCut
      (D := (witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0)
      (H := (witnessDiagram k b delta hp.staircase_bound).colLen 0) N ⟨d+r.val-d,hr.2⟩ v else 0)=_
  have hr : d≤d+r.val ∧ d+r.val-d < (E).colLen 0 := by
    constructor <;> omega
  rw [dif_pos hr]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

theorem containedAttachmentTargetDual_path (r : Fin ((pi).colLen 0)) (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :
    containedAttachmentTargetDual hh he k b delta hp N
      (rowLetterInclusion (containedPath_le_whole h e hh he d (witnessPathSize k) m) r) v=0 := by
  apply containedAttachmentTargetDual_low_zero hh he k b delta hp N
  let x : (pi).cells := ⟨(r.val,0),YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩
  exact containedPath_row_lt hh d (witnessPathSize k) m x

def containedCombinedTargetDual : Fin ((theta).colLen 0) → Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ :=
  fun j v => containedPathTargetDual hh he k b delta hp j v +
    containedAttachmentTargetDual hh he k b delta hp N j v

theorem containedCombinedTargetDual_path (r : Fin ((pi).colLen 0)) (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :
    containedCombinedTargetDual hh he k b delta hp N
      (rowLetterInclusion (containedPath_le_whole h e hh he d (witnessPathSize k) m) r) v =
    containedPathTargetDual hh he k b delta hp
      (rowLetterInclusion (containedPath_le_whole h e hh he d (witnessPathSize k) m) r) v := by
  unfold containedCombinedTargetDual
  rw [containedAttachmentTargetDual_path,add_zero]

theorem containedCombinedTargetDual_attachment
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hzero : ∀ c, t≤c → e c=0) (r : Fin ((E).colLen 0)) (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :
    containedCombinedTargetDual hh he k b delta hp N
      (containedAttachmentRowLetter hh he hroom hclear hzero r) v =
      containedAttachmentMatrixCut
      (D := (witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0)
      (H := (witnessDiagram k b delta hp.staircase_bound).colLen 0) N r v := by
  unfold containedCombinedTargetDual
  rw [containedPathTargetDual_attachment_zero hh he k b delta hp hroom hclear hzero,
    containedAttachmentTargetDual_attachment,zero_add]

theorem containedCombinedTargetDual_separated :
    witnessFlagSeparated k b delta hp (fun (j : Fin ((theta).colLen 0)) => j.val < d)
      (containedCombinedTargetDual (d:=d) (m:=m) hh he k b delta hp N) := by
  intro j v hc hm
  unfold containedCombinedTargetDual
  rw [containedPathTargetDual_separated hh he k b delta hp j v hc hm]
  have hz : containedAttachmentTargetDual hh he k b delta hp N j v=0 := by
    by_cases hj : j.val < d
    · exact containedAttachmentTargetDual_low_zero hh he k b delta hp N j v hj
    · apply containedAttachmentTargetDual_source_zero hh he k b delta hp N j v
      intro hv
      apply hm
      constructor
      · intro hl
        omega
      · intro hlow
        exact False.elim (hj hlow)
  rw [hz,zero_add]

end
end
end HSTZ
#print axioms HSTZ.containedAttachmentTargetDual
#print axioms HSTZ.containedAttachmentTargetDual_low_zero
#print axioms HSTZ.containedAttachmentTargetDual_source_zero
#print axioms HSTZ.containedAttachmentTargetDual_attachment
#print axioms HSTZ.containedAttachmentTargetDual_path
#print axioms HSTZ.containedCombinedTargetDual
#print axioms HSTZ.containedCombinedTargetDual_path
#print axioms HSTZ.containedCombinedTargetDual_attachment
#print axioms HSTZ.containedCombinedTargetDual_separated
