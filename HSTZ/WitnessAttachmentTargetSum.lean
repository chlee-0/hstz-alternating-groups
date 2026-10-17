import HSTZ.WitnessAttachmentTargetFibers

/-! The target contraction written as a signed sum over the full target column
group, in the given matching. This file does not prove that the sum is nonzero.
Uses `wordRep_single` and the linear `wordMap` from OpenAI's `math` repository
(commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def attachmentTargetEvenColumnSum {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (L : Fin (mu.colLen 0) → Fin 4 → ℂ) : ℂ := by
  classical
  letI := Fintype.ofFinite (attachmentTargetEvenColumnGroup t he)
  exact ∑ g : attachmentTargetEvenColumnGroup t he, signC g.val *
    dotProduct (wordMap L (Pi.single
      ((rowWord t ∘ attachmentTargetEvenMatching t he) ∘ g.val.symm) 1)) (attachmentHTensor b 0)

def attachmentTargetOddColumnSum {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (L : Fin (mu.colLen 0) → Fin 4 → ℂ) : ℂ := by
  classical
  letI := Fintype.ofFinite (attachmentTargetOddColumnGroup t a ho)
  exact ∑ g : attachmentTargetOddColumnGroup t a ho, signC g.val *
    dotProduct (wordMap L (Pi.single
      ((rowWord t ∘ attachmentTargetOddMatching t a ho) ∘ g.val.symm) 1)) (attachmentHTensor b 1)

theorem attachmentTargetEvenContraction_full_sum {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (L : Fin (mu.colLen 0) → Fin 4 → ℂ) :
    dotProduct (wordMap L (attachmentTargetEvenAlternant t he)) (attachmentHTensor b 0) =
      attachmentTargetEvenColumnSum t he L := by
  classical
  letI := Fintype.ofFinite (attachmentTargetEvenColumnGroup t he)
  unfold attachmentTargetEvenColumnSum attachmentTargetEvenAlternant altWord
  change dotProduct ((wordMap L).toLinearMap _) (attachmentHTensor b 0) = _
  rw [map_sum, sum_dotProduct]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_smul, smul_dotProduct, wordRep_single]
  rfl

theorem attachmentTargetOddContraction_full_sum {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (L : Fin (mu.colLen 0) → Fin 4 → ℂ) :
    dotProduct (wordMap L (attachmentTargetOddAlternant t a ho)) (attachmentHTensor b 1) =
      attachmentTargetOddColumnSum t a ho L := by
  classical
  letI := Fintype.ofFinite (attachmentTargetOddColumnGroup t a ho)
  unfold attachmentTargetOddColumnSum attachmentTargetOddAlternant altWord
  change dotProduct ((wordMap L).toLinearMap _) (attachmentHTensor b 1) = _
  rw [map_sum, sum_dotProduct]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_smul, smul_dotProduct, wordRep_single]
  rfl

end
end HSTZ
#print axioms HSTZ.attachmentTargetEvenContraction_full_sum
#print axioms HSTZ.attachmentTargetOddContraction_full_sum
