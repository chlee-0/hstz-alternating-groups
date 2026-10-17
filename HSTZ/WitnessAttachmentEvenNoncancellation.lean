import HSTZ.WitnessAttachmentTargetEvenSurvivors

/-! Value of the full column group of the even target, and nonvanishing of the
contraction. Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Every survivor has positive sign, and the identity permutation shows that the
survivor set is nonempty. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical

abbrev AttachmentTargetEvenSurvivors {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :=
  {g : attachmentTargetEvenColumnGroup t he // attachmentTargetEvenPairMatches t he g}

theorem attachmentTargetEvenColumnSum_value {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (ht : mu.colLen 0 ≤ 4) (a : Fin 4) :
    attachmentTargetEvenColumnSum t he (attachmentTargetLetters t ht a) =
      (Nat.card (AttachmentTargetEvenSurvivors t he) : ℂ) := by
  classical
  letI := Fintype.ofFinite (attachmentTargetEvenColumnGroup t he)
  rw [attachmentTargetEvenColumnSum_product]
  calc
    _ = ∑ g : attachmentTargetEvenColumnGroup t he,
        if attachmentTargetEvenPairMatches t he g then (1:ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      by_cases hh : attachmentTargetEvenPairMatches t he g
      · rw [if_pos hh,attachmentTargetEven_survivor_sign t he g hh,one_mul]
      · rw [if_neg hh,mul_zero]
    _ = _ := by
      rw [Finset.sum_boole,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem attachmentTargetEvenColumnSum_ne_zero {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (ht : mu.colLen 0 ≤ 4) (a : Fin 4) :
    attachmentTargetEvenColumnSum t he (attachmentTargetLetters t ht a) ≠ 0 := by
  letI : Nonempty (AttachmentTargetEvenSurvivors t he) :=
    ⟨⟨1,attachmentTargetEvenPairMatches_one t he⟩⟩
  rw [attachmentTargetEvenColumnSum_value]
  exact Nat.cast_ne_zero.mpr (Nat.card_pos.ne')

theorem attachmentTargetEven_original_contraction_ne_zero {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (ht : mu.colLen 0 ≤ 4) (a : Fin 4) :
    dotProduct (wordMap (attachmentTargetLetters t ht a) (polytabloid t))
      (wordRep _ 4 (attachmentTargetEvenMatching t he) (attachmentHTensor b 0)) ≠ 0 := by
  rw [← attachmentTargetEvenContraction_original,attachmentTargetEvenContraction_full_sum]
  exact attachmentTargetEvenColumnSum_ne_zero t he ht a

end
end HSTZ
#print axioms HSTZ.attachmentTargetEvenColumnSum_value
#print axioms HSTZ.attachmentTargetEvenColumnSum_ne_zero
#print axioms HSTZ.attachmentTargetEven_original_contraction_ne_zero
