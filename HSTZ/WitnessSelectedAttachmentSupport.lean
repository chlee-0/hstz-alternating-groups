import HSTZ.WitnessAttachmentMaschke
import HSTZ.WitnessAttachmentSignInclusion

/-! The sign-twisted native attachment map, and an injective embedding of the
repeated attachment cyclic space into the sign twist of the attachment cyclic space.
Built from the Maschke lift, the native attachment cyclic encoding and
`signTwistMap`. Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev witnessNativeAttachmentSignCyclicMap (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  (signTwistMap (witnessNativeAttachmentCyclicMap k b delta hp)).comp
    (witnessAttachmentSignCyclicIncl b delta)

private theorem signedComp_injective {n : ℕ} {U V W : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ (Equiv.Perm (Fin n)) U}
    {sigma : Representation ℂ (Equiv.Perm (Fin n)) V}
    {tau : Representation ℂ (Equiv.Perm (Fin n)) W}
    (f : Representation.IntertwiningMap sigma tau)
    (j : Representation.IntertwiningMap rho (signTwist sigma))
    (hf : Function.Injective f) (hj : Function.Injective j) :
    Function.Injective ((signTwistMap f).comp j).toLinearMap := hf.comp hj

theorem witnessNativeAttachmentSignCyclicMap_injective (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    Function.Injective (witnessNativeAttachmentSignCyclicMap k b delta hp).toLinearMap :=
  signedComp_injective (witnessNativeAttachmentCyclicMap k b delta hp)
    (witnessAttachmentSignCyclicIncl b delta)
    (witnessNativeAttachmentCyclicMap_bijective k b delta hp).1
    (witnessAttachmentSignCyclicIncl_injective b delta)

/-- The lift `i` and its composite `J` with the native sign map; `i` satisfies the
image equation. -/
theorem witnessSelectedAttachmentRepeated_lift (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    ∃ i : Representation.IntertwiningMap
        (witnessAttachmentRepeatedCyclic b delta).toRepresentation
        (witnessAttachmentSignCyclic b delta).toRepresentation,
      Function.Injective i ∧
      (∀ y, witnessAttachmentRepeatedCyclicImageMap b delta (i y) =
        witnessAttachmentRepeatedImageIncl b delta y) ∧
      ∃ J : Representation.IntertwiningMap
          (witnessAttachmentRepeatedCyclic b delta).toRepresentation
          (signTwist (witnessAttachmentCyclic k b delta hp).toRepresentation),
        Function.Injective J.toLinearMap ∧
        ∀ y, J.toLinearMap y =
          (witnessNativeAttachmentSignCyclicMap k b delta hp).toLinearMap (i y) := by
  obtain ⟨i,hi,he⟩ := witnessAttachmentRepeated_embedding b delta
  refine ⟨i,hi,he,(witnessNativeAttachmentSignCyclicMap k b delta hp).comp i,?_,?_⟩
  · exact (witnessNativeAttachmentSignCyclicMap_injective k b delta hp).comp hi
  · intro y
    rfl

/-- The repeated attachment cyclic space embeds in the sign twist of the attachment
cyclic space. -/
theorem witnessSelectedAttachmentRepeated_embedding (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    ∃ J : Representation.IntertwiningMap
        (witnessAttachmentRepeatedCyclic b delta).toRepresentation
        (signTwist (witnessAttachmentCyclic k b delta hp).toRepresentation),
      Function.Injective J.toLinearMap := by
  obtain ⟨_,_,_,J,hJ,_⟩ := witnessSelectedAttachmentRepeated_lift k b delta hp
  exact ⟨J,hJ⟩

end
end HSTZ
#print axioms HSTZ.witnessNativeAttachmentSignCyclicMap

#print axioms HSTZ.witnessNativeAttachmentSignCyclicMap_injective

#print axioms HSTZ.witnessSelectedAttachmentRepeated_lift
#print axioms HSTZ.witnessSelectedAttachmentRepeated_embedding
