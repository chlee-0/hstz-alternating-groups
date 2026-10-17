import HSTZ.IntertwiningCompat
import HSTZ.WitnessAttachmentHCyclic
import HSTZ.WitnessSelectedAttachmentSupport

/-! Inverse of the binary attachment carrier transport, and the selected consumer.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The full position action, the binary image equality and the selected sign action
are kept explicit. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private def wordCarrierIsoInclusion {n d : ℕ} (P Q : Subrepresentation (wordRep n d))
    (h : P.toSubmodule = Q.toSubmodule) :
    Representation.IntertwiningMap P.toRepresentation Q.toRepresentation where
  toLinearMap := Submodule.inclusion h.le
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

private theorem wordCarrierIsoInclusion_bijective {n d : ℕ}
    (P Q : Subrepresentation (wordRep n d)) (h : P.toSubmodule = Q.toSubmodule) :
    Function.Bijective (wordCarrierIsoInclusion P Q h) := by
  constructor
  · intro x y hh
    exact Subtype.ext (congrArg (fun z : Q.toSubmodule => z.val) hh)
  · intro z
    refine ⟨⟨z.val,?_⟩,rfl⟩
    rw [h]
    exact z.property

private def attachmentBinaryHIncl (b delta : ℕ) :=
  wordCarrierIsoInclusion
    (cyclicSubrepresentation (wordRep (witnessAttachment b delta).card 4)
      (witnessAttachmentBinaryRepeatedWord b delta))
    (attachmentHCyclic b delta) (attachmentHCyclic_eq b delta)

private theorem attachmentBinaryHIncl_bijective (b delta : ℕ) :
    Function.Bijective (attachmentBinaryHIncl b delta) :=
  wordCarrierIsoInclusion_bijective _ _ _

abbrev witnessAttachmentRepeatedHMap (b delta : ℕ) :=
  (attachmentBinaryHIncl b delta).comp (witnessAttachmentBinaryRepeatedCyclicMap b delta)

theorem witnessAttachmentRepeatedHMap_bijective (b delta : ℕ) :
    Function.Bijective (witnessAttachmentRepeatedHMap b delta).toLinearMap :=
  (attachmentBinaryHIncl_bijective b delta).comp
    (witnessAttachmentBinaryRepeatedCyclicMap_bijective b delta)

private def attachmentRepeatedHEquiv (b delta : ℕ) :
    (witnessAttachmentRepeatedCyclic b delta).toSubmodule ≃ₗ[ℂ]
      (attachmentHCyclic b delta).toSubmodule :=
  LinearEquiv.ofBijective (witnessAttachmentRepeatedHMap b delta).toLinearMap
    (witnessAttachmentRepeatedHMap_bijective b delta)

def witnessAttachmentHRepeatedInverse (b delta : ℕ) :
    Representation.IntertwiningMap (attachmentHCyclic b delta).toRepresentation
      (witnessAttachmentRepeatedCyclic b delta).toRepresentation where
  toLinearMap := (attachmentRepeatedHEquiv b delta).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply (attachmentRepeatedHEquiv b delta).injective
    change attachmentRepeatedHEquiv b delta
      ((attachmentRepeatedHEquiv b delta).symm ((attachmentHCyclic b delta).toRepresentation g x)) =
      attachmentRepeatedHEquiv b delta ((witnessAttachmentRepeatedCyclic b delta).toRepresentation g
        ((attachmentRepeatedHEquiv b delta).symm x))
    rw [LinearEquiv.apply_symm_apply]
    have he := (witnessAttachmentRepeatedHMap b delta).map_action g
      ((attachmentRepeatedHEquiv b delta).symm x)
    change attachmentRepeatedHEquiv b delta
      ((witnessAttachmentRepeatedCyclic b delta).toRepresentation g
        ((attachmentRepeatedHEquiv b delta).symm x)) =
      (attachmentHCyclic b delta).toRepresentation g
        (attachmentRepeatedHEquiv b delta ((attachmentRepeatedHEquiv b delta).symm x)) at he
    rw [he,LinearEquiv.apply_symm_apply]

theorem witnessAttachmentHRepeatedInverse_injective (b delta : ℕ) :
    Function.Injective (witnessAttachmentHRepeatedInverse b delta).toLinearMap :=
  (attachmentRepeatedHEquiv b delta).symm.injective

theorem witnessSelectedAttachmentH_embedding (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    ∃ F : Representation.IntertwiningMap (attachmentHCyclic b delta).toRepresentation
      (signTwist (witnessAttachmentCyclic k b delta hp).toRepresentation),
      Function.Injective F.toLinearMap := by
  obtain ⟨J,hJ⟩ := witnessSelectedAttachmentRepeated_embedding k b delta hp
  exact ⟨J.comp (witnessAttachmentHRepeatedInverse b delta),
    hJ.comp (witnessAttachmentHRepeatedInverse_injective b delta)⟩


end
end HSTZ
#print axioms HSTZ.witnessAttachmentRepeatedHMap
#print axioms HSTZ.witnessAttachmentRepeatedHMap_bijective
#print axioms HSTZ.witnessAttachmentHRepeatedInverse
#print axioms HSTZ.witnessAttachmentHRepeatedInverse_injective
#print axioms HSTZ.witnessSelectedAttachmentH_embedding
