import HSTZ.ContainedWitnessContractionProduct
import OAI.RepresentationTheory.Saxl.PieriRestriction

/-! Row-letter embeddings of the path and attachment factors, and the placed
polytabloids written as letter lifts. Uses declarations from OpenAI's `math`
repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

 theorem containedPath_le_whole (h e : ℕ → ℕ) (hh : Antitone h)
    (he : Antitone e) (d K m : ℕ) :
    containedPath h hh d K m ≤ containedWhole h e hh he d K m := by
  intro x hx
  exact (containedPathCell h e hh he d K m ⟨x,hx⟩).property

section Letters
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m)
    (hzero : ∀ c, t ≤ c → e c=0)

/-- Embedding of attachment row letters into the rows of the contained whole
diagram, `r ↦ d + r`. The domain may be empty. -/
def containedAttachmentRowLetter :
    Fin ((containedAttachment e he m).colLen 0) ↪
      Fin ((containedWhole h e hh he d K m).colLen 0) where
  toFun r := ⟨d+r.val,by
    let x : (containedAttachment e he m).cells :=
      ⟨(r.val,0),YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩
    have ht : 0 < t := containedAttachment_col_lt he m t hzero x
    have hx := (containedAttachmentCell h e hh he d K m x).property
    change (greedy h d K 0+r.val,0) ∈ containedWhole h e hh he d K m at hx
    rw [greedy_eq_depth hroom (by omega) ht] at hx
    exact YoungDiagram.mem_iff_lt_colLen.mp hx⟩
  inj' := by
    intro r s hrs
    apply Fin.ext
    have hv := congrArg Fin.val hrs
    change d+r.val=d+s.val at hv
    omega

theorem containedAttachmentRowLetter_val
    (r : Fin ((containedAttachment e he m).colLen 0)) :
    (containedAttachmentRowLetter hh he hroom hclear hzero r).val=d+r.val := rfl

variable {n : ℕ} (s : Tableau n (containedWhole h e hh he d K m))
local notation "Q" => containedFactorPositions hh he htm hroom hclear hcapacity s
local notation "T" => containedPathPrefixOrder hh htm hroom hclear hcapacity
local notation "A" => canonicalTableau (containedAttachment e he m) rfl

theorem containedFactor_path_rowWord :
    leftWord (Q).symm (rowWord s)=
      rowLetterInclusion (containedPath_le_whole h e hh he d K m) ∘ rowWord T := by
  funext i
  apply Fin.ext
  change (s (Q (.inl i))).val.1=(T i).val.1
  rw [containedFactorPositions_path]

theorem containedFactor_attachment_rowWord :
    rightWord (Q).symm (rowWord s)=
      containedAttachmentRowLetter hh he hroom hclear hzero ∘ rowWord A := by
  funext i
  apply Fin.ext
  change (s (Q (.inr i))).val.1=d+(A i).val.1
  have hc := containedAttachment_col_lt he m t hzero (A i)
  rw [containedFactorPositions_attachment_reserved hh he htm hroom hclear hcapacity s i hc]

theorem containedFactor_path_polytabloid :
    altWord (columnGroup T) (leftWord (Q).symm (rowWord s))=
      letterLift (rowLetterInclusion (containedPath_le_whole h e hh he d K m))
        (polytabloid T) := by
  rw [polytabloid_eq_altWord,letterLift_altWord,containedFactor_path_rowWord]

theorem containedFactor_attachment_polytabloid :
    altWord (columnGroup A) (rightWord (Q).symm (rowWord s))=
      letterLift (containedAttachmentRowLetter hh he hroom hclear hzero)
        (polytabloid A) := by
  rw [polytabloid_eq_altWord,letterLift_altWord,containedFactor_attachment_rowWord]
end Letters
end
end HSTZ
#print axioms HSTZ.containedPath_le_whole
#print axioms HSTZ.containedAttachmentRowLetter
#print axioms HSTZ.containedAttachmentRowLetter_val
#print axioms HSTZ.containedFactor_path_rowWord
#print axioms HSTZ.containedFactor_attachment_rowWord
#print axioms HSTZ.containedFactor_path_polytabloid
#print axioms HSTZ.containedFactor_attachment_polytabloid
