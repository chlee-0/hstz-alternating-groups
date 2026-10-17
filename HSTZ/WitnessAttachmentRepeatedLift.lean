import HSTZ.WitnessAttachmentRepeatedImage

/-! Injective inclusion of the repeated attachment cyclic space into the repeated
image cyclic space. Follows the shape of `staircaseCyclicInclusion` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0), using `Submodule.inclusion`.
The private word-carrier wrapper only packages the existing inclusion. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private def wordCarrierInclusion {n d : ℕ} (P Q : Subrepresentation (wordRep n d))
    (h : P.toSubmodule ≤ Q.toSubmodule) :
    Representation.IntertwiningMap P.toRepresentation Q.toRepresentation where
  toLinearMap := Submodule.inclusion h
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

private theorem wordCarrierInclusion_injective {n d : ℕ}
    (P Q : Subrepresentation (wordRep n d)) (h : P.toSubmodule ≤ Q.toSubmodule) :
    Function.Injective (wordCarrierInclusion P Q h) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z : Q.toSubmodule => z.val) he)

def witnessAttachmentRepeatedImageIncl (b delta : ℕ) :
    Representation.IntertwiningMap (witnessAttachmentRepeatedCyclic b delta).toRepresentation
      (witnessAttachmentRepeatedImageCyclic b delta).toRepresentation :=
  wordCarrierInclusion (witnessAttachmentRepeatedCyclic b delta)
    (witnessAttachmentRepeatedImageCyclic b delta) (witnessAttachmentRepeatedCyclic_image_le b delta)

theorem witnessAttachmentRepeatedImageIncl_injective (b delta : ℕ) :
    Function.Injective (witnessAttachmentRepeatedImageIncl b delta) :=
  wordCarrierInclusion_injective _ _ _

end
end HSTZ
#print axioms HSTZ.witnessAttachmentRepeatedImageIncl
#print axioms HSTZ.witnessAttachmentRepeatedImageIncl_injective
