import HSTZ.WitnessAttachmentTargetProducts

/-! Full signed product sums and the surviving identity terms.
Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
A nonzero identity contribution alone does not prove that the full sum does not
cancel. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical

theorem attachmentTargetEvenColumnSum_product {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (ht : mu.colLen 0 ≤ 4) (a : Fin 4) :
    attachmentTargetEvenColumnSum t he (attachmentTargetLetters t ht a) =
      letI := Fintype.ofFinite (attachmentTargetEvenColumnGroup t he)
      ∑ g : attachmentTargetEvenColumnGroup t he,
        signC g.val * (if attachmentTargetEvenPairMatches t he g then (1:ℂ) else 0) := by
  classical
  letI := Fintype.ofFinite (attachmentTargetEvenColumnGroup t he)
  unfold attachmentTargetEvenColumnSum
  apply Finset.sum_congr rfl
  intro g hg
  rw [attachmentTargetEven_term]

theorem attachmentTargetOddColumnSum_product {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) :
    attachmentTargetOddColumnSum t a ho (attachmentTargetOddLetters t a ho ht) =
      letI := Fintype.ofFinite (attachmentTargetOddColumnGroup t a ho)
      ∑ g : attachmentTargetOddColumnGroup t a ho,
        signC g.val * ((if attachmentTargetOddPairMatches t a ho g then (1:ℂ) else 0) *
          attachmentTargetOddLetters t a ho ht
            (rowWord t (attachmentTargetOddMatching t a ho
              (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inr 0))))) 0) := by
  classical
  letI := Fintype.ofFinite (attachmentTargetOddColumnGroup t a ho)
  unfold attachmentTargetOddColumnSum
  apply Finset.sum_congr rfl
  intro g hg
  rw [attachmentTargetOdd_term]

theorem attachmentTargetEvenPairMatches_one {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :
    attachmentTargetEvenPairMatches t he 1 := by
  intro j
  apply Fin.ext
  change (t (attachmentTargetEvenMatching t he
      (witnessAttachmentColumnOrderFin b 0 (.inl (j,0))))).val.1 =
    (t (attachmentTargetEvenMatching t he
      (witnessAttachmentColumnOrderFin b 0 (.inl (j,1))))).val.1
  rw [attachmentTargetEvenMatching_order,attachmentTargetEvenMatching_order,
    attachmentTargetEvenPositions_pair,attachmentTargetEvenPositions_pair]

theorem attachmentTargetOddPairMatches_one {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) : attachmentTargetOddPairMatches t a ho 1 := by
  intro j
  apply Fin.ext
  change (t (attachmentTargetOddMatching t a ho
      (witnessAttachmentColumnOrderFin b 1 (.inl (j,0))))).val.1 =
    (t (attachmentTargetOddMatching t a ho
      (witnessAttachmentColumnOrderFin b 1 (.inl (j,1))))).val.1
  rw [attachmentTargetOddMatching_order,attachmentTargetOddMatching_order,
    attachmentTargetOddPositions_pair,attachmentTargetOddPositions_pair]

theorem attachmentTargetEven_identity_contraction {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (ht : mu.colLen 0 ≤ 4) (a : Fin 4) :
    dotProduct (wordMap (attachmentTargetLetters t ht a) (Pi.single
      (rowWord t ∘ attachmentTargetEvenMatching t he) 1)) (attachmentHTensor b 0) = 1 := by
  have hh := attachmentTargetEven_term t he ht a 1
  rw [if_pos (attachmentTargetEvenPairMatches_one t he)] at hh
  exact hh

theorem attachmentTargetOdd_identity_contraction {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) :
    dotProduct (wordMap (attachmentTargetOddLetters t a ho ht) (Pi.single
      (rowWord t ∘ attachmentTargetOddMatching t a ho) 1)) (attachmentHTensor b 1) =
      attachmentHScale := by
  have hh := attachmentTargetOdd_term t a ho ht 1
  rw [if_pos (attachmentTargetOddPairMatches_one t a ho),one_mul] at hh
  change dotProduct (wordMap (attachmentTargetOddLetters t a ho ht) (Pi.single
    (rowWord t ∘ attachmentTargetOddMatching t a ho) 1)) (attachmentHTensor b 1) =
    attachmentTargetOddLetters t a ho ht
      (rowWord t (attachmentTargetOddMatching t a ho
        (witnessAttachmentColumnOrderFin b 1 (.inr 0)))) 0 at hh
  rw [attachmentTargetOddLetters_single] at hh
  exact hh

theorem attachmentTargetOdd_identity_contraction_ne_zero {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) :
    dotProduct (wordMap (attachmentTargetOddLetters t a ho ht) (Pi.single
      (rowWord t ∘ attachmentTargetOddMatching t a ho) 1)) (attachmentHTensor b 1) ≠ 0 := by
  rw [attachmentTargetOdd_identity_contraction]
  exact attachmentHScale_ne_zero

end
end HSTZ
#print axioms HSTZ.attachmentTargetEvenColumnSum_product
#print axioms HSTZ.attachmentTargetOddColumnSum_product
#print axioms HSTZ.attachmentTargetEvenPairMatches_one
#print axioms HSTZ.attachmentTargetOddPairMatches_one
#print axioms HSTZ.attachmentTargetEven_identity_contraction
#print axioms HSTZ.attachmentTargetOdd_identity_contraction
#print axioms HSTZ.attachmentTargetOdd_identity_contraction_ne_zero
