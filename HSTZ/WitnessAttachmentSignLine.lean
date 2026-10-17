import HSTZ.IntertwiningCompat
import HSTZ.WitnessAttachmentAverage
import HSTZ.SpechtSignTransport
import OAI.RepresentationTheory.Saxl.StaircaseSign

/-! The attachment average/sign line.
Reuses the sign-transpose inverse and `alternating_specht_line` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0) on the canonical attachment carriers,
including degree zero. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def witnessAttachmentAverageSpecht (b delta : ℕ) :
    Specht (transposeTableau (witnessCanonicalAttachment b delta)) :=
  ⟨witnessAttachmentRowAverage b delta,witnessAttachmentRowAverage_mem b delta⟩

theorem witnessAttachmentAverageSpecht_ne_zero (b delta : ℕ) :
    witnessAttachmentAverageSpecht b delta ≠ 0 := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  intro hz
  have he := congrArg (fun x : Specht (transposeTableau (witnessCanonicalAttachment b delta)) =>
    x.val (rowWord (transposeTableau (witnessCanonicalAttachment b delta)))) hz
  change witnessAttachmentRowAverage b delta _ = 0 at he
  rw [witnessAttachmentRowAverage_coefficient] at he
  rw [Nat.card_eq_fintype_card] at he
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero he

def witnessAttachmentSignAverage (b delta : ℕ) : Specht (witnessCanonicalAttachment b delta) :=
  spechtSignInverseMap (witnessCanonicalAttachment b delta) (witnessAttachmentAverageSpecht b delta)

theorem witnessAttachmentSignAverage_alternating (b delta : ℕ)
    (h : columnGroup (witnessCanonicalAttachment b delta)) :
    spechtRep (witnessCanonicalAttachment b delta) h.val (witnessAttachmentSignAverage b delta) =
      signC h.val • witnessAttachmentSignAverage b delta := by
  have hf : spechtRep (transposeTableau (witnessCanonicalAttachment b delta)) h.val
      (witnessAttachmentAverageSpecht b delta) = witnessAttachmentAverageSpecht b delta := by
    apply Subtype.ext
    exact witnessAttachmentRowAverage_invariant b delta h
  have he := (spechtSignInverseMap (witnessCanonicalAttachment b delta)).map_action
    h.val (witnessAttachmentAverageSpecht b delta)
  change (spechtSignInverseMap (witnessCanonicalAttachment b delta))
    (signC h.val • spechtRep (transposeTableau (witnessCanonicalAttachment b delta)) h.val
      (witnessAttachmentAverageSpecht b delta)) = _ at he
  rw [hf] at he
  change (spechtSignInverseMap (witnessCanonicalAttachment b delta)).toLinearMap
    (signC h.val • witnessAttachmentAverageSpecht b delta) = _ at he
  rw [map_smul] at he
  exact he.symm

theorem witnessAttachmentSignAverage_ne_zero (b delta : ℕ) :
    witnessAttachmentSignAverage b delta ≠ 0 := by
  intro hz
  apply witnessAttachmentAverageSpecht_ne_zero b delta
  apply (spechtSignEquiv (witnessCanonicalAttachment b delta)).symm.injective
  exact hz.trans (map_zero (spechtSignInverseMap (witnessCanonicalAttachment b delta)).toLinearMap).symm

theorem witnessAttachmentSignAverage_line (b delta : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ (witnessAttachmentSignAverage b delta).val =
      c • polytabloid (witnessCanonicalAttachment b delta) := by
  obtain ⟨c,hc⟩ := alternating_specht_line (witnessCanonicalAttachment b delta)
    (witnessAttachmentSignAverage b delta) (witnessAttachmentSignAverage_alternating b delta)
  refine ⟨c,?_,hc⟩
  intro hc0
  apply witnessAttachmentSignAverage_ne_zero b delta
  apply Subtype.ext
  change (witnessAttachmentSignAverage b delta).val = 0
  simpa only [hc0,zero_smul] using hc

end
end HSTZ
#print axioms HSTZ.witnessAttachmentAverageSpecht_ne_zero
#print axioms HSTZ.witnessAttachmentSignAverage_alternating
#print axioms HSTZ.witnessAttachmentSignAverage_ne_zero
#print axioms HSTZ.witnessAttachmentSignAverage_line
