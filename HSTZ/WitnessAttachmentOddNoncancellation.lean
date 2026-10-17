import HSTZ.WitnessAttachmentOddSurvivors

/-! The full odd target column-group value, and nonvanishing of the original
moved-`H` contraction. Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The survivor sign and singleton fixation handle every surviving term. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical

abbrev AttachmentTargetOddSurvivors {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) :=
  {g : attachmentTargetOddColumnGroup t a ho // attachmentTargetOddPairMatches t a ho g}

theorem attachmentTargetOddColumnSum_value {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) :
    attachmentTargetOddColumnSum t a ho (attachmentTargetOddLetters t a ho ht) =
      (Nat.card (AttachmentTargetOddSurvivors t a ho) : ℂ) * attachmentHScale := by
  classical
  letI := Fintype.ofFinite (attachmentTargetOddColumnGroup t a ho)
  rw [attachmentTargetOddColumnSum_product]
  calc
    _ = ∑ g : attachmentTargetOddColumnGroup t a ho,
        (if attachmentTargetOddPairMatches t a ho g then (1:ℂ) else 0) * attachmentHScale := by
      apply Finset.sum_congr rfl
      intro g hg
      by_cases hh : attachmentTargetOddPairMatches t a ho g
      · rw [if_pos hh,attachmentTargetOdd_survivor_sign t a ho g hh,one_mul,one_mul,
          attachmentTargetOdd_survivor_single t a ho g hh,
          attachmentTargetOddLetters_single,one_mul]
      · simp only [if_neg hh,zero_mul,mul_zero]
    _ = (∑ g : attachmentTargetOddColumnGroup t a ho,
        if attachmentTargetOddPairMatches t a ho g then (1:ℂ) else 0) * attachmentHScale :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by
      rw [Finset.sum_boole,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem attachmentTargetOddColumnSum_ne_zero {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) :
    attachmentTargetOddColumnSum t a ho (attachmentTargetOddLetters t a ho ht) ≠ 0 := by
  letI : Nonempty (AttachmentTargetOddSurvivors t a ho) :=
    ⟨⟨1,attachmentTargetOddPairMatches_one t a ho⟩⟩
  rw [attachmentTargetOddColumnSum_value]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne')) attachmentHScale_ne_zero

theorem attachmentTargetOdd_original_contraction_ne_zero {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) :
    dotProduct (wordMap (attachmentTargetOddLetters t a ho ht) (polytabloid t))
      (wordRep _ 4 (attachmentTargetOddMatching t a ho) (attachmentHTensor b 1)) ≠ 0 := by
  rw [← attachmentTargetOddContraction_original,attachmentTargetOddContraction_full_sum]
  exact attachmentTargetOddColumnSum_ne_zero t a ho ht

end
end HSTZ
#print axioms HSTZ.attachmentTargetOddColumnSum_value
#print axioms HSTZ.attachmentTargetOddColumnSum_ne_zero
#print axioms HSTZ.attachmentTargetOdd_original_contraction_ne_zero
