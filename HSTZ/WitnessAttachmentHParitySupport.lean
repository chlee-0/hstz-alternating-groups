import HSTZ.WitnessAttachmentOddNoncancellation

/-! Unconditional Specht support for the ordinary paper H, for both parity targets.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The nonvanishing of the full contraction is proved here; the original Specht carrier
is kept. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem attachmentHTensor_even_embedding {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (ht : mu.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (attachmentHCyclic b 0).toRepresentation, Function.Injective F := by
  let L := attachmentTargetLetters t ht (0 : Fin 4)
  let x : (spechtSub t).toSubmodule :=
    ⟨wordRep _ _ (attachmentTargetEvenMatching t he).symm (polytabloid t),
      (spechtSub t).apply_mem_toSubmodule (attachmentTargetEvenMatching t he).symm
        (mem_cyclic _ _)⟩
  have hnz : dotProduct (wordMap L x.val) (attachmentHTensor b 0) ≠ 0 := by
    change dotProduct (wordMap L
      (wordRep _ _ (attachmentTargetEvenMatching t he).symm (polytabloid t)))
      (attachmentHTensor b 0) ≠ 0
    rw [attachmentTargetEvenAlternant_original,attachmentTargetEvenContraction_full_sum]
    exact attachmentTargetEvenColumnSum_ne_zero t he ht (0 : Fin 4)
  obtain ⟨F,hF⟩ := hom_to_cyclic_of_pair L (spechtSub t) x (attachmentHTensor b 0)
    (attachmentHTensor_real b 0) hnz
  change Representation.IntertwiningMap (spechtRep t)
    (attachmentHCyclic b 0).toRepresentation at F
  letI := specht_irreducible t
  exact ⟨F,(Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

theorem attachmentHTensor_odd_embedding {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ) (ho : AttachmentOneOddRow mu a)
    (ht : mu.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (attachmentHCyclic b 1).toRepresentation, Function.Injective F := by
  let L := attachmentTargetOddLetters t a ho ht
  let x : (spechtSub t).toSubmodule :=
    ⟨wordRep _ _ (attachmentTargetOddMatching t a ho).symm (polytabloid t),
      (spechtSub t).apply_mem_toSubmodule (attachmentTargetOddMatching t a ho).symm
        (mem_cyclic _ _)⟩
  have hnz : dotProduct (wordMap L x.val) (attachmentHTensor b 1) ≠ 0 := by
    change dotProduct (wordMap L
      (wordRep _ _ (attachmentTargetOddMatching t a ho).symm (polytabloid t)))
      (attachmentHTensor b 1) ≠ 0
    rw [attachmentTargetOddAlternant_original,attachmentTargetOddContraction_full_sum]
    exact attachmentTargetOddColumnSum_ne_zero t a ho ht
  obtain ⟨F,hF⟩ := hom_to_cyclic_of_pair L (spechtSub t) x (attachmentHTensor b 1)
    (attachmentHTensor_real b 1) hnz
  change Representation.IntertwiningMap (spechtRep t)
    (attachmentHCyclic b 1).toRepresentation at F
  letI := specht_irreducible t
  exact ⟨F,(Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

end
end HSTZ
#print axioms HSTZ.attachmentHTensor_even_embedding
#print axioms HSTZ.attachmentHTensor_odd_embedding
