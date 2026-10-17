import HSTZ.WitnessCutCells
import HSTZ.WitnessAttachmentWords

/-! The first-row cycle of the canonical attachment, including length 1.
Uses tableau interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Empty attachments have no origin, but the cell permutation still exists. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def witnessAttachmentCycleForward (b delta r c : ℕ) : ℕ :=
  if r=0 then if c=0 then b+delta-1 else c-1 else c
def witnessAttachmentCycleBackward (b delta r c : ℕ) : ℕ :=
  if r=0 then if c+1=b+delta then 0 else c+1 else c

def witnessAttachmentCycleCell (b delta : ℕ) : Equiv.Perm ((witnessAttachment b delta).cells) where
  toFun x := ⟨(x.val.1,witnessAttachmentCycleForward b delta x.val.1 x.val.2),by
    rcases x with ⟨⟨r,c⟩,hx⟩
    apply (mem_witnessAttachment b delta _ _).mpr
    rcases (mem_witnessAttachment b delta _ _).mp hx with ⟨hr,hc⟩ | ⟨hr,hc⟩
    · left
      exact ⟨hr,by simp only [witnessAttachmentCycleForward,hr,if_true]; split_ifs <;> omega⟩
    · right
      simpa [witnessAttachmentCycleForward,hr] using And.intro hr hc⟩
  invFun x := ⟨(x.val.1,witnessAttachmentCycleBackward b delta x.val.1 x.val.2),by
    rcases x with ⟨⟨r,c⟩,hx⟩
    apply (mem_witnessAttachment b delta _ _).mpr
    rcases (mem_witnessAttachment b delta _ _).mp hx with ⟨hr,hc⟩ | ⟨hr,hc⟩
    · left
      exact ⟨hr,by simp only [witnessAttachmentCycleBackward,hr,if_true]; split_ifs <;> omega⟩
    · right
      simpa [witnessAttachmentCycleBackward,hr] using And.intro hr hc⟩
  left_inv x := by
    rcases x with ⟨⟨r,c⟩,hx⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change witnessAttachmentCycleBackward b delta r
        (witnessAttachmentCycleForward b delta r c)=c
      have hx := (mem_witnessAttachment b delta _ _).mp hx
      unfold witnessAttachmentCycleBackward witnessAttachmentCycleForward
      split_ifs <;> omega
  right_inv x := by
    rcases x with ⟨⟨r,c⟩,hx⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change witnessAttachmentCycleForward b delta r
        (witnessAttachmentCycleBackward b delta r c)=c
      by_cases hr : r=0
      · subst r
        by_cases he : c+1=b+delta
        · simp only [witnessAttachmentCycleBackward,witnessAttachmentCycleForward,
            he,if_pos]
          omega
        · simp [witnessAttachmentCycleBackward,witnessAttachmentCycleForward,he]
      · simp [witnessAttachmentCycleBackward,witnessAttachmentCycleForward,hr]

theorem witnessAttachmentCycleCell_row (b delta : ℕ) (x : (witnessAttachment b delta).cells) :
    (witnessAttachmentCycleCell b delta x).val.1=x.val.1 := rfl

theorem witnessAttachmentCycleCell_column (b delta : ℕ) (x : (witnessAttachment b delta).cells) :
    (witnessAttachmentCycleCell b delta x).val.2=
      witnessAttachmentCycleForward b delta x.val.1 x.val.2 := rfl

/-- Conjugation keeps the canonical tableau and all positions. -/
def witnessAttachmentCyclePositions (b delta : ℕ) : Equiv.Perm (Fin (witnessAttachment b delta).card) :=
  (witnessCanonicalAttachment b delta).trans
    ((witnessAttachmentCycleCell b delta).trans (witnessCanonicalAttachment b delta).symm)

theorem witnessAttachmentCyclePositions_cell (b delta : ℕ) (i : Fin (witnessAttachment b delta).card) :
    witnessCanonicalAttachment b delta (witnessAttachmentCyclePositions b delta i)=
      witnessAttachmentCycleCell b delta (witnessCanonicalAttachment b delta i) := by
  simp only [witnessAttachmentCyclePositions,Equiv.trans_apply,Equiv.apply_symm_apply]

theorem witnessAttachmentCyclePositions_mem (b delta : ℕ) :
    witnessAttachmentCyclePositions b delta ∈ columnGroup (transposeTableau (witnessCanonicalAttachment b delta)) := by
  change ∀ i, (witnessCanonicalAttachment b delta (witnessAttachmentCyclePositions b delta i)).val.1=
    (witnessCanonicalAttachment b delta i).val.1
  intro i
  rw [witnessAttachmentCyclePositions_cell,witnessAttachmentCycleCell_row]

end
end HSTZ
#print axioms HSTZ.witnessAttachmentCycleCell
#print axioms HSTZ.witnessAttachmentCycleCell_row
#print axioms HSTZ.witnessAttachmentCycleCell_column
#print axioms HSTZ.witnessAttachmentCyclePositions_cell
#print axioms HSTZ.witnessAttachmentCyclePositions_mem
