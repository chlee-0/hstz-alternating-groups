import HSTZ.WitnessPathWords

/-! Attachment coordinates under the ordered cut of the witness. The proofs are
new and use interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Width, height and both rotations are kept. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev witnessCanonicalAttachment (b delta : ℕ) :
    Tableau (witnessAttachment b delta).card (witnessAttachment b delta) :=
  canonicalTableau (witnessAttachment b delta) rfl

def witnessAttachmentRowRestriction (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    Fin (witnessAttachment b delta).card →
      Fin ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  fun i => rowWord (transposeTableau t)
    ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
      ((witnessBinaryCut k b delta hk t).symm
        (.inr (witnessComplementOrder k b delta (.inr i)))))

def witnessAttachmentColumnRestriction (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    Fin (witnessAttachment b delta).card → Fin ((witnessDiagram k b delta hk).colLen 0) :=
  fun i => rowWord t
    ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
      ((witnessBinaryCut k b delta hk t).symm
        (.inr (witnessComplementOrder k b delta (.inr i)))))

theorem witness_attachment_row_value (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin (witnessAttachment b delta).card) :
    (witnessAttachmentRowRestriction k b delta hk t i).val=
      witnessRowForward k b (witnessCanonicalAttachment b delta i).val.1
        (k-1+(witnessCanonicalAttachment b delta i).val.2) := by
  change (t ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
    ((witnessBinaryCut k b delta hk t).symm
      (.inr (witnessComplementOrder k b delta (.inr i)))))).val.2=_
  rw [witnessRowRotationPositions_cell,witnessBinaryCut_attachment,witnessCutPosition_attachment]
  rfl

theorem witness_attachment_column_value (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin (witnessAttachment b delta).card) :
    (witnessAttachmentColumnRestriction k b delta hk t i).val=
      (witnessCanonicalAttachment b delta i).val.1 := by
  change (t ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
    ((witnessBinaryCut k b delta hk t).symm
      (.inr (witnessComplementOrder k b delta (.inr i)))))).val.1=_
  rw [witnessColumnRotationPositions_cell,witnessBinaryCut_attachment,witnessCutPosition_attachment]
  have he : k-2-(k-1+(witnessCanonicalAttachment b delta i).val.2)=0 := by omega
  change (if (witnessCanonicalAttachment b delta i).val.1<
    k-2-(k-1+(witnessCanonicalAttachment b delta i).val.2)
    then (witnessCanonicalAttachment b delta i).val.1+2
    else (witnessCanonicalAttachment b delta i).val.1-
      (k-2-(k-1+(witnessCanonicalAttachment b delta i).val.2)))=_
  simp only [he,Nat.not_lt_zero,if_false,Nat.sub_zero]

theorem witness_attachment_row_all (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin (witnessAttachment b delta).card) :
    (witnessAttachmentRowRestriction k b delta hk t i).val=
      if (witnessCanonicalAttachment b delta i).val.1=0 then
        if (witnessCanonicalAttachment b delta i).val.2=0 then 1
        else if (witnessCanonicalAttachment b delta i).val.2<b+1
          then k-2+(witnessCanonicalAttachment b delta i).val.2
          else k-1+(witnessCanonicalAttachment b delta i).val.2
      else k-1+(witnessCanonicalAttachment b delta i).val.2 := by
  rw [witness_attachment_row_value]
  have hx := (mem_witnessAttachment b delta _ _).mp
    (witnessCanonicalAttachment b delta i).property
  by_cases hr : (witnessCanonicalAttachment b delta i).val.1=0
  · simp only [hr,if_true,witnessRowForward]
    unfold witnessFirstRowForward
    split_ifs <;> omega
  · have hr1 : (witnessCanonicalAttachment b delta i).val.1=1 := by
      rcases hx with ⟨h0,_⟩ | ⟨h1,_⟩
      · exact (hr h0).elim
      · exact h1
    simp only [hr,if_false,witnessRowForward]
    unfold witnessRowTailForward
    split_ifs <;> omega

theorem witnessAttachment_positions_empty :
    ¬Nonempty (Fin (witnessAttachment 0 0).card) := by
  rintro ⟨i⟩
  have hz : (witnessAttachment 0 0).card=0 := by
    simpa only [witnessAttachment_card]
  have hi : i.val<0 := lt_of_lt_of_eq i.isLt hz
  omega

end
end HSTZ
#print axioms HSTZ.witness_attachment_row_value
#print axioms HSTZ.witness_attachment_column_value
#print axioms HSTZ.witness_attachment_row_all
#print axioms HSTZ.witnessAttachment_positions_empty
