import HSTZ.WitnessExchangedWords

/-! The exchanged low-row mask on the full ordered complement. Uses interfaces
from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No contraction or global shuffle is inferred. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem witnessComplementRowBase_attachment (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin (witnessAttachment b delta).card) :
    witnessComplementRowBase k b delta hk (witnessComplementOrder k b delta (.inr i))=
      witnessAttachmentRowRestriction k b delta hk t i := by
  exact (congrFun (witness_complement_row_base k b delta hk t)
    (witnessComplementOrder k b delta (.inr i))).symm

theorem witnessAttachmentRow_high_of_ne_origin (k b delta : ℕ) (hk : 5 ≤ k)
    (hr : 0<b+delta) (i : Fin (witnessAttachment b delta).card)
    (hi : i≠witnessAttachmentOriginPosition b delta hr) :
    2≤(witnessComplementRowBase k b delta hk
      (witnessComplementOrder k b delta (.inr i))).val := by
  rw [witnessComplementRowBase_attachment k b delta hk (witnessTableau k b delta hk),
    witness_attachment_row_all]
  have hn : ¬((witnessCanonicalAttachment b delta i).val.1=0 ∧
      (witnessCanonicalAttachment b delta i).val.2=0) := by
    rintro ⟨hrow,hcol⟩
    apply hi
    apply (witnessCanonicalAttachment b delta).injective
    rw [witnessAttachmentOriginPosition_cell]
    apply Subtype.ext
    exact Prod.ext hrow hcol
  split_ifs <;> omega

theorem witnessExchangedRowBase_low_mask (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) (i : Fin (witnessComplementSize k b delta)) :
    (witnessExchangedRowBase k b delta hp.staircase_bound
      (paperWitness_attachment_positive k b delta hp) i).val<2 ↔
      witnessComplementPathMask k b delta i := by
  classical
  let hr := paperWitness_attachment_positive k b delta hp
  obtain ⟨a,rfl⟩ := (witnessComplementOrder k b delta).surjective i
  cases a with
  | inl p =>
    have he := congrFun (witnessExchangedRowBase_path k b delta hp.staircase_bound hr) p
    have hl : (witnessExchangedRowBase k b delta hp.staircase_bound hr
        (witnessComplementOrder k b delta (.inl p))).val<2 := by
      rw [he]
      exact (PathLayer.base p).isLt
    simpa only [witnessComplementPathMask,Equiv.symm_apply_apply,Sum.isLeft_inl,
      Bool.true_eq,iff_true] using hl
  | inr a =>
    have hne : witnessComplementOrder k b delta (.inr a)≠witnessComplementEndpoint k b delta := by
      intro he
      have hh := (witnessComplementOrder k b delta).injective he
      cases hh
    have hh : 2≤(witnessExchangedRowBase k b delta hp.staircase_bound hr
        (witnessComplementOrder k b delta (.inr a))).val := by
      rw [witnessExchangedRowBase_all,if_neg hne]
      by_cases ha : a=witnessAttachmentOriginPosition b delta hr
      · subst a
        rw [if_pos (show witnessComplementOrder k b delta
          (.inr (witnessAttachmentOriginPosition b delta hr))=
          witnessComplementOrigin k b delta hr from rfl),
          witnessComplementEndpoint,witnessComplementRowBase_path]
        exact witnessPathRowBase_endpoint_paper k b delta hp
      · have hno : witnessComplementOrder k b delta (.inr a)≠
            witnessComplementOrigin k b delta hr := by
          intro he
          exact ha (Sum.inr.inj ((witnessComplementOrder k b delta).injective he))
        rw [if_neg hno]
        exact witnessAttachmentRow_high_of_ne_origin k b delta hp.staircase_bound hr a ha
    have hl : ¬(witnessExchangedRowBase k b delta hp.staircase_bound hr
        (witnessComplementOrder k b delta (.inr a))).val<2 := by omega
    simpa only [witnessComplementPathMask,Equiv.symm_apply_apply,Sum.isLeft_inr,
      Bool.false_eq_true,iff_false] using hl

end
end HSTZ
#print axioms HSTZ.witnessComplementRowBase_attachment
#print axioms HSTZ.witnessAttachmentRow_high_of_ne_origin
#print axioms HSTZ.witnessExchangedRowBase_low_mask
