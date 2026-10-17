import HSTZ.WitnessAttachmentRepeatedSupport

/-! Maschke step for the attachment. Reuses the image map and inclusion and the
existing Maschke lift from OpenAI's `math` repository (commit adc7f1241, Apache-2.0);
no target support is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- Maschke lifts the repeated cyclic carrier, keeping the image equation. -/
theorem witnessAttachmentRepeated_embedding (b delta : ℕ) :
    ∃ i : Representation.IntertwiningMap (witnessAttachmentRepeatedCyclic b delta).toRepresentation
        (witnessAttachmentSignCyclic b delta).toRepresentation,
      Function.Injective i ∧ ∀ y,
        witnessAttachmentRepeatedCyclicImageMap b delta (i y) =
          witnessAttachmentRepeatedImageIncl b delta y := by
  letI : NeZero (Nat.card (Equiv.Perm (Fin (witnessAttachment b delta).card)) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos.ne')⟩
  exact equivariant_injective_lift
    (K := ℂ) (G := Equiv.Perm (Fin (witnessAttachment b delta).card))
    (U := (witnessAttachmentRepeatedCyclic b delta).toSubmodule)
    (V := (witnessAttachmentSignCyclic b delta).toSubmodule)
    (W := (witnessAttachmentRepeatedImageCyclic b delta).toSubmodule)
    (witnessAttachmentRepeatedCyclicImageMap b delta)
    (witnessAttachmentRepeatedCyclicImageMap_surjective b delta)
    (witnessAttachmentRepeatedImageIncl b delta)
    (witnessAttachmentRepeatedImageIncl_injective b delta)

end
end HSTZ
#print axioms HSTZ.witnessAttachmentRepeated_embedding
