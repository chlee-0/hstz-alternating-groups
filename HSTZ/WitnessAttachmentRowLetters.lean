import HSTZ.WitnessAttachmentCycle
import HSTZ.WitnessSelectedFactors

/-! The row-letter embedding for unequal alphabets and the exchanged attachment
base, keeping the canonical first-row cycle. Uses coordinate and letter
interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem witnessAttachment_width (b delta : ℕ) :
    (witnessAttachment b delta).transpose.colLen 0=b+delta := by
  rw [YoungDiagram.colLen_transpose]
  exact YoungDiagram.rowLen_ofRowLens (w := [b+delta,b])
    (hw := by rw [List.sortedGE_iff_pairwise]; simp) ⟨0,by simp⟩

def witnessAttachmentHighValue (k b delta c : ℕ) : ℕ :=
  if delta=1 ∧ c=b then k+b else k-1+c

def witnessAttachmentRowLetter (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin ((witnessAttachment b delta).transpose.colLen 0) ↪
      Fin ((witnessDiagram k b delta hk).transpose.colLen 0) where
  toFun i := ⟨witnessAttachmentHighValue k b delta i.val,by
    have hi := i.isLt
    replace hi : i.val<b+delta := lt_of_lt_of_eq hi (witnessAttachment_width b delta)
    have hw : (witnessDiagram k b delta hk).transpose.colLen 0=k+b+delta := by
      rw [YoungDiagram.colLen_transpose,witnessDiagram_width]
    apply lt_of_lt_of_eq ?_ hw.symm
    unfold witnessAttachmentHighValue
    split_ifs <;> omega⟩
  inj' := by
    intro i j he
    have hi := i.isLt
    have hj := j.isLt
    replace hi : i.val<b+delta := lt_of_lt_of_eq hi (witnessAttachment_width b delta)
    replace hj : j.val<b+delta := lt_of_lt_of_eq hj (witnessAttachment_width b delta)
    have hv := congrArg (fun x : Fin ((witnessDiagram k b delta hk).transpose.colLen 0) => x.val) he
    change witnessAttachmentHighValue k b delta i.val=witnessAttachmentHighValue k b delta j.val at hv
    apply Fin.ext
    unfold witnessAttachmentHighValue at hv
    split_ifs at hv <;> omega

/-- Raw coordinate arithmetic keeps dependent Fin carriers out of the separator. -/
theorem witness_attachment_cycle_letter_value (k b delta r c : ℕ) (hk : 5 ≤ k) (hd : delta≤1)
    (hx : (r=0 ∧ c<b+delta) ∨ (r=1 ∧ c<b)) (hn : ¬(r=0 ∧ c=0)) :
    (if r=0 then if c=0 then 1 else if c<b+1 then k-2+c else k-1+c else k-1+c)=
      witnessAttachmentHighValue k b delta (witnessAttachmentCycleForward b delta r c) := by
  unfold witnessAttachmentHighValue witnessAttachmentCycleForward
  split_ifs <;> omega

theorem witness_attachment_exchanged_row_base (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    rightWord (witnessComplementOrder k b delta).symm
      (witnessExchangedRowBase k b delta hp.staircase_bound (paperWitness_attachment_positive k b delta hp))=
      witnessAttachmentRowLetter k b delta hp.staircase_bound ∘
        (rowWord (transposeTableau (witnessCanonicalAttachment b delta)) ∘
          witnessAttachmentCyclePositions b delta) := by
  funext i
  apply Fin.ext
  let hr := paperWitness_attachment_positive k b delta hp
  have hk := hp.staircase_bound
  have hd := hp.parity
  have hne : witnessComplementOrder k b delta (.inr i)≠witnessComplementEndpoint k b delta := by
    intro he
    have hh := (witnessComplementOrder k b delta).injective he
    cases hh
  change (witnessExchangedRowBase k b delta hp.staircase_bound hr
    (witnessComplementOrder k b delta (.inr i))).val=
    witnessAttachmentHighValue k b delta
      (witnessCanonicalAttachment b delta (witnessAttachmentCyclePositions b delta i)).val.2
  rw [witnessAttachmentCyclePositions_cell,witnessAttachmentCycleCell_column,
    witnessExchangedRowBase_all,if_neg hne]
  by_cases ho : i=witnessAttachmentOriginPosition b delta hr
  · subst i
    rw [if_pos (show witnessComplementOrder k b delta
      (.inr (witnessAttachmentOriginPosition b delta hr))=witnessComplementOrigin k b delta hr from rfl),
      witnessComplementEndpoint,witnessComplementRowBase_path,witnessAttachmentOriginPosition_cell]
    change (witnessPathRowBase k b delta hp.staircase_bound (witnessPathEndpoint k)).val=
      witnessAttachmentHighValue k b delta (witnessAttachmentCycleForward b delta 0 0)
    have hc : delta=0 ∨ delta=1 := by omega
    rcases hc with rfl | rfl
    · rw [witnessPathRowBase_endpoint_even k b hk (by have hh := hp.positive_remainder; omega)]
      unfold witnessAttachmentHighValue witnessAttachmentCycleForward
      split_ifs <;> omega
    · rw [witnessPathRowBase_endpoint_odd]
      unfold witnessAttachmentHighValue witnessAttachmentCycleForward
      split_ifs <;> omega
  · have hon : witnessComplementOrder k b delta (.inr i)≠witnessComplementOrigin k b delta hr := by
      intro he
      exact ho (Sum.inr.inj ((witnessComplementOrder k b delta).injective he))
    rw [if_neg hon,witnessComplementRowBase_attachment k b delta hp.staircase_bound
      (witnessTableau k b delta hp.staircase_bound),witness_attachment_row_all]
    have hx := (mem_witnessAttachment b delta _ _).mp (witnessCanonicalAttachment b delta i).property
    have hn : ¬((witnessCanonicalAttachment b delta i).val.1=0 ∧
        (witnessCanonicalAttachment b delta i).val.2=0) := by
      rintro ⟨hrow,hcol⟩
      apply ho
      apply (witnessCanonicalAttachment b delta).injective
      rw [witnessAttachmentOriginPosition_cell]
      apply Subtype.ext
      exact Prod.ext hrow hcol
    exact witness_attachment_cycle_letter_value k b delta _ _ hk hd hx hn

theorem witnessSelectedAttachmentRowWord_generator (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessSelectedAttachmentRowWord k b delta hp=
      signC (witnessAttachmentCyclePositions b delta) •
        letterLift (witnessAttachmentRowLetter k b delta hp.staircase_bound)
          (polytabloid (transposeTableau (witnessCanonicalAttachment b delta))) := by
  unfold witnessSelectedAttachmentRowWord
  have hg : fiberGroup (fun i : Fin (witnessAttachment b delta).card =>
      (witnessCanonicalAttachment b delta i).val.1)=
      columnGroup (transposeTableau (witnessCanonicalAttachment b delta)) := rfl
  rw [hg,witness_attachment_exchanged_row_base k b delta hp]
  change altWord _ ((witnessAttachmentRowLetter k b delta hp.staircase_bound ∘
    rowWord (transposeTableau (witnessCanonicalAttachment b delta))) ∘ witnessAttachmentCyclePositions b delta)=_
  rw [altWord_move _ _ ⟨_,witnessAttachmentCyclePositions_mem b delta⟩,
    ← letterLift_altWord,← polytabloid_eq_altWord]

end
end HSTZ
#print axioms HSTZ.witnessAttachment_width
#print axioms HSTZ.witnessAttachmentRowLetter
#print axioms HSTZ.witness_attachment_exchanged_row_base
#print axioms HSTZ.witnessSelectedAttachmentRowWord_generator

#print axioms HSTZ.witness_attachment_cycle_letter_value
