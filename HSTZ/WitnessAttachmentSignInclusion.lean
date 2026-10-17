import HSTZ.WitnessAttachmentRepeatedImage

/-! Signed cyclic inclusion. Reuses the `signTwist` orbit action and the
`staircaseCyclicInclusion` packaging from OpenAI's `math` repository (commit adc7f1241, Apache-2.0);
the source and target submodules and the full position group are kept. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem wordSignCyclic_le {n d : ℕ} (v : WordSpace n d) :
    cyclicSpan (signTwist (wordRep n d)) v ≤ cyclicSpan (wordRep n d) v := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,rfl⟩
  exact Submodule.smul_mem _ (signC g) (orbit_mem_cyclicSpan (wordRep n d) v g)

theorem witnessAttachmentSignCyclic_le (b delta : ℕ) :
    (witnessAttachmentSignCyclic b delta).toSubmodule ≤
      (witnessCanonicalAttachmentCyclic b delta).toSubmodule :=
  wordSignCyclic_le (witnessCanonicalAttachmentPair b delta)

private def wordSignedCarrierInclusion {n d : ℕ}
    (P : Subrepresentation (signTwist (wordRep n d))) (Q : Subrepresentation (wordRep n d))
    (h : P.toSubmodule ≤ Q.toSubmodule) :
    Representation.IntertwiningMap P.toRepresentation (signTwist Q.toRepresentation) where
  toLinearMap := Submodule.inclusion h
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

private theorem wordSignedCarrierInclusion_injective {n d : ℕ}
    (P : Subrepresentation (signTwist (wordRep n d))) (Q : Subrepresentation (wordRep n d))
    (h : P.toSubmodule ≤ Q.toSubmodule) :
    Function.Injective (wordSignedCarrierInclusion P Q h) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z : Q.toSubmodule => z.val) he)

def witnessAttachmentSignCyclicIncl (b delta : ℕ) :
    Representation.IntertwiningMap (witnessAttachmentSignCyclic b delta).toRepresentation
      (signTwist (witnessCanonicalAttachmentCyclic b delta).toRepresentation) :=
  wordSignedCarrierInclusion _ _ (witnessAttachmentSignCyclic_le b delta)

theorem witnessAttachmentSignCyclicIncl_injective (b delta : ℕ) :
    Function.Injective (witnessAttachmentSignCyclicIncl b delta) :=
  wordSignedCarrierInclusion_injective _ _ (witnessAttachmentSignCyclic_le b delta)

end
end HSTZ
#print axioms HSTZ.witnessAttachmentSignCyclic_le
#print axioms HSTZ.witnessAttachmentSignCyclicIncl
#print axioms HSTZ.witnessAttachmentSignCyclicIncl_injective
