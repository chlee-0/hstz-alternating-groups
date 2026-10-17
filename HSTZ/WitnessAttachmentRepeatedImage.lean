import HSTZ.WitnessAttachmentRepeated
import HSTZ.ProjectionLift

/-! The repeated canonical generator embeds in the sign-twisted attachment
cyclic carrier. Uses image and finite-group Maschke interfaces adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). No parity target support is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem witnessAttachmentRepeatedWord_coefficient (b delta : ℕ) :
    witnessAttachmentRepeatedWord b delta
      (mergeWords (rowWord (witnessCanonicalAttachment b delta))
        (rowWord (witnessCanonicalAttachment b delta))) = 1 := by
  simp only [witnessAttachmentRepeatedWord,wordTensor_tmul,splitLeft_merge,splitRight_merge,polytabloid_rowWord,mul_one]

theorem witnessAttachmentRepeatedWord_ne_zero (b delta : ℕ) :
    witnessAttachmentRepeatedWord b delta ≠ 0 := by
  intro hz
  have he := witnessAttachmentRepeatedWord_coefficient b delta
  rw [hz] at he
  exact zero_ne_one he

def witnessAttachmentRepeatedCyclic (b delta : ℕ) :
    Subrepresentation (wordRep (witnessAttachment b delta).card
      ((witnessAttachment b delta).colLen 0 * (witnessAttachment b delta).colLen 0)) :=
  cyclicSubrepresentation (wordRep _ _) (witnessAttachmentRepeatedWord b delta)
def witnessAttachmentSignCyclic (b delta : ℕ) :
    Subrepresentation (signTwist (wordRep (witnessAttachment b delta).card
      ((witnessAttachment b delta).transpose.colLen 0 * (witnessAttachment b delta).colLen 0))) :=
  cyclicSubrepresentation (signTwist (wordRep _ _)) (witnessCanonicalAttachmentPair b delta)

def witnessAttachmentRepeatedImageCyclic (b delta : ℕ) :
    Subrepresentation (wordRep (witnessAttachment b delta).card
      ((witnessAttachment b delta).colLen 0 * (witnessAttachment b delta).colLen 0)) :=
  cyclicSubrepresentation (wordRep _ _)
    ((witnessAttachmentRepeatedMap b delta).toLinearMap (witnessCanonicalAttachmentPair b delta))

theorem witnessAttachmentRepeatedCyclic_image_le (b delta : ℕ) :
    (witnessAttachmentRepeatedCyclic b delta).toSubmodule ≤
      (witnessAttachmentRepeatedImageCyclic b delta).toSubmodule := by
  have hm : witnessAttachmentRepeatedWord b delta ∈
      (witnessAttachmentRepeatedImageCyclic b delta).toSubmodule := by
    exact (congrArg (fun S : Submodule ℂ (WordSpace (witnessAttachment b delta).card
      ((witnessAttachment b delta).colLen 0 * (witnessAttachment b delta).colLen 0)) =>
      witnessAttachmentRepeatedWord b delta ∈ S)
      (cyclicSpan_image (witnessAttachmentRepeatedMap b delta)
        (witnessCanonicalAttachmentPair b delta))).mp
      (witnessAttachmentRepeatedWord_mem_image b delta)
  exact (cyclicSpan_le_iff (wordRep (witnessAttachment b delta).card
    ((witnessAttachment b delta).colLen 0 * (witnessAttachment b delta).colLen 0))
    (witnessAttachmentRepeatedWord b delta) (witnessAttachmentRepeatedImageCyclic b delta)).mpr hm

end
end HSTZ
#print axioms HSTZ.witnessAttachmentRepeatedCyclic_image_le
#print axioms HSTZ.witnessAttachmentRepeatedWord_coefficient
#print axioms HSTZ.witnessAttachmentRepeatedWord_ne_zero
