import HSTZ.WitnessAttachmentTargetCells

/-! Matches the original caller's target positions to the paper's `H` source order.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The only pair enumeration is the canonical half-target tableau. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem attachmentTargetCaller_card {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    mu.card = n := by
  have hc := Fintype.card_congr t
  simpa using hc.symm

def attachmentTargetEvenHalfTableau {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :
    Tableau b (attachmentTargetHalf mu) :=
  canonicalTableau _ (attachmentTargetEven_half_degree mu he b (by
    rw [attachmentTargetCaller_card t, witnessAttachment_card]; omega))

def attachmentTargetOddHalfTableau {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) : Tableau b (attachmentTargetHalf mu) :=
  canonicalTableau _ (attachmentTargetOdd_half_degree mu a ho b (by
    rw [attachmentTargetCaller_card t, witnessAttachment_card]))

def attachmentTargetEvenOrder (b : ℕ) :
    ((Fin b × Fin 2) ⊕ Fin 0) ≃ (Fin b × Fin 2) where
  toFun := fun p => match p with | .inl q => q | .inr j => Fin.elim0 j
  invFun := Sum.inl
  left_inv := by intro p; cases p with | inl q => rfl | inr j => exact Fin.elim0 j
  right_inv := fun _ => rfl

def attachmentTargetEvenPositions {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :
    WitnessAttachmentColumnOrder b 0 ≃ Fin (witnessAttachment b 0).card :=
  (attachmentTargetEvenOrder b).trans
    ((Equiv.prodCongr (attachmentTargetEvenHalfTableau t he) (Equiv.refl (Fin 2))).trans
      ((attachmentTargetEvenCells mu he).trans t.symm))

def attachmentTargetOddPositions {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) :
    WitnessAttachmentColumnOrder b 1 ≃ Fin (witnessAttachment b 1).card :=
  (Equiv.sumCongr
    (Equiv.prodCongr (attachmentTargetOddHalfTableau t a ho) (Equiv.refl (Fin 2)))
    (Equiv.refl (Fin 1))).trans ((attachmentTargetOddCells mu a ho).trans t.symm)

theorem attachmentTargetEvenPositions_pair {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (j : Fin b) (s : Fin 2) :
    (t (attachmentTargetEvenPositions t he (.inl (j,s)))).val =
      ((attachmentTargetEvenHalfTableau t he j).val.1,
       2*(attachmentTargetEvenHalfTableau t he j).val.2+s.val) := by
  change (t (t.symm (attachmentTargetPairCell mu
    (attachmentTargetEvenHalfTableau t he j,s)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem attachmentTargetOddPositions_pair {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (j : Fin b) (s : Fin 2) :
    (t (attachmentTargetOddPositions t a ho (.inl (j,s)))).val =
      ((attachmentTargetOddHalfTableau t a ho j).val.1,
       2*(attachmentTargetOddHalfTableau t a ho j).val.2+s.val) := by
  change (t (t.symm (attachmentTargetPairCell mu
    (attachmentTargetOddHalfTableau t a ho j,s)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem attachmentTargetOddPositions_single {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (j : Fin 1) :
    (t (attachmentTargetOddPositions t a ho (.inr j))).val = (a,mu.rowLen a-1) := by
  change (t (t.symm (attachmentTargetOddCell mu a ho))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

def attachmentTargetEvenMatching {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :
    Equiv.Perm (Fin (witnessAttachment b 0).card) :=
  (witnessAttachmentColumnOrderFin b 0).symm.trans (attachmentTargetEvenPositions t he)

def attachmentTargetOddMatching {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) : Equiv.Perm (Fin (witnessAttachment b 1).card) :=
  (witnessAttachmentColumnOrderFin b 1).symm.trans (attachmentTargetOddPositions t a ho)

theorem attachmentTargetEvenMatching_order {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (p : WitnessAttachmentColumnOrder b 0) :
    attachmentTargetEvenMatching t he (witnessAttachmentColumnOrderFin b 0 p) =
      attachmentTargetEvenPositions t he p := by
  simp [attachmentTargetEvenMatching]

theorem attachmentTargetOddMatching_order {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (p : WitnessAttachmentColumnOrder b 1) :
    attachmentTargetOddMatching t a ho (witnessAttachmentColumnOrderFin b 1 p) =
      attachmentTargetOddPositions t a ho p := by
  simp [attachmentTargetOddMatching]

end
end HSTZ
#print axioms HSTZ.attachmentTargetEvenPositions
#print axioms HSTZ.attachmentTargetOddPositions
#print axioms HSTZ.attachmentTargetEvenPositions_pair
#print axioms HSTZ.attachmentTargetOddPositions_pair
#print axioms HSTZ.attachmentTargetOddPositions_single
#print axioms HSTZ.attachmentTargetEvenMatching_order
#print axioms HSTZ.attachmentTargetOddMatching_order
