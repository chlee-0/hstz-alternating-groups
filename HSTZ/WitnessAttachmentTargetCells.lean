import HSTZ.WitnessAttachmentHalfTarget

/-! Complete parity pairing of the target cells, with the odd orphan cell.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The matching is constructed here rather than taken as a hypothesis; row parity gives legality. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem attachmentTargetEven_bound (mu : YoungDiagram) (he : AttachmentEvenRows mu)
    (x : mu.cells) : x.val.2 < 2*(mu.rowLen x.val.1/2) := by
  have hc : x.val.2 < mu.rowLen x.val.1 :=
    YoungDiagram.mem_iff_lt_rowLen.mp x.property
  have hp := he x.val.1
  omega

def attachmentTargetEvenCells (mu : YoungDiagram) (he : AttachmentEvenRows mu) :
    AttachmentTargetPair mu ≃ mu.cells where
  toFun := attachmentTargetPairCell mu
  invFun := fun x => attachmentTargetPairIndex mu x (attachmentTargetEven_bound mu he x)
  left_inv := attachmentTargetPairIndex_cell mu
  right_inv := fun x => attachmentTargetPairCell_index mu x _

theorem attachmentTargetOddCell_unpaired (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) :
    ¬(attachmentTargetOddCell mu a ho).val.2 <
      2*(mu.rowLen (attachmentTargetOddCell mu a ho).val.1/2) := by
  change ¬mu.rowLen a-1 < 2*(mu.rowLen a/2)
  have hp := ho.1
  omega

theorem attachmentTargetUnpaired_eq (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (x : mu.cells)
    (hx : ¬x.val.2 < 2*(mu.rowLen x.val.1/2)) :
    x = attachmentTargetOddCell mu a ho := by
  have hc : x.val.2 < mu.rowLen x.val.1 :=
    YoungDiagram.mem_iff_lt_rowLen.mp x.property
  have hr : x.val.1 = a := by
    by_contra h
    have hp := ho.2 x.val.1 h
    omega
  rw [hr] at hc hx
  have hp := ho.1
  apply Subtype.ext
  apply Prod.ext
  · exact hr
  · change x.val.2 = mu.rowLen a-1
    omega

def attachmentTargetOddCells (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) : AttachmentTargetPair mu ⊕ Fin 1 ≃ mu.cells where
  toFun := fun p => match p with
    | .inl q => attachmentTargetPairCell mu q
    | .inr _ => attachmentTargetOddCell mu a ho
  invFun := fun x => if hx : x.val.2 < 2*(mu.rowLen x.val.1/2) then
    .inl (attachmentTargetPairIndex mu x hx) else .inr 0
  left_inv := by
    intro p
    cases p with
    | inl q =>
      simp only [dif_pos (attachmentTargetPairCell_bound mu q)]
      exact congrArg Sum.inl (attachmentTargetPairIndex_cell mu q)
    | inr j =>
      simp only [dif_neg (attachmentTargetOddCell_unpaired mu a ho)]
      congr 1
      exact Subsingleton.elim _ _
  right_inv := by
    intro x
    dsimp only
    split_ifs with hx
    · exact attachmentTargetPairCell_index mu x hx
    · exact (attachmentTargetUnpaired_eq mu a ho x hx).symm

theorem attachmentTargetEven_card (mu : YoungDiagram) (he : AttachmentEvenRows mu) :
    mu.card = 2*(attachmentTargetHalf mu).card := by
  have hc := Fintype.card_congr (attachmentTargetEvenCells mu he)
  simpa [AttachmentTargetPair, mul_comm] using hc.symm

theorem attachmentTargetOdd_card (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) : mu.card = 2*(attachmentTargetHalf mu).card+1 := by
  have hc := Fintype.card_congr (attachmentTargetOddCells mu a ho)
  simpa [AttachmentTargetPair, mul_comm] using hc.symm

theorem attachmentTargetEven_half_degree (mu : YoungDiagram) (he : AttachmentEvenRows mu)
    (b : ℕ) (hn : mu.card = 2*b) : (attachmentTargetHalf mu).card = b := by
  have hc := attachmentTargetEven_card mu he
  omega

theorem attachmentTargetOdd_half_degree (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (b : ℕ) (hn : mu.card = 2*b+1) :
    (attachmentTargetHalf mu).card = b := by
  have hc := attachmentTargetOdd_card mu a ho
  omega

end
end HSTZ
#print axioms HSTZ.attachmentTargetEvenCells
#print axioms HSTZ.attachmentTargetOddCells
#print axioms HSTZ.attachmentTargetUnpaired_eq
#print axioms HSTZ.attachmentTargetEven_card
#print axioms HSTZ.attachmentTargetOdd_card
#print axioms HSTZ.attachmentTargetEven_half_degree
#print axioms HSTZ.attachmentTargetOdd_half_degree
