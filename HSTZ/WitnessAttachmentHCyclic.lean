import HSTZ.WitnessAttachmentH

/-! Full-group cyclic carrier of the ordered paper H tensor.
Reuses orbit/image interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The canonical permutation is explicit; nothing is deduced from characters or dimensions. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def attachmentHTensor (b delta : ℕ) : WordSpace (witnessAttachment b delta).card 4 :=
  positionProduct (attachmentColumnSplit b delta) (attachmentHPower b)
    (Pi.single (fun _ : Fin delta => (0 : Fin 4)) (1:ℂ))

theorem attachmentHTensor_action (b delta : ℕ) :
    wordRep (witnessAttachment b delta).card 4
      (witnessAttachmentColumnEnumeration b delta).symm
      (witnessAttachmentBinaryRepeatedWord b delta)=attachmentHTensor b delta := by
  funext w
  exact witnessAttachmentBinaryRepeated_HPower b delta w

theorem attachmentHTensor_action_inverse (b delta : ℕ) :
    wordRep (witnessAttachment b delta).card 4
      (witnessAttachmentColumnEnumeration b delta) (attachmentHTensor b delta)=
      witnessAttachmentBinaryRepeatedWord b delta := by
  rw [← attachmentHTensor_action]
  rw [← Module.End.mul_apply,← map_mul]
  have hi : (witnessAttachmentColumnEnumeration b delta : Equiv.Perm _)*
      (witnessAttachmentColumnEnumeration b delta).symm=1 := by
    apply Equiv.ext
    intro i
    exact (witnessAttachmentColumnEnumeration b delta).apply_symm_apply i
  rw [hi,map_one]
  rfl

theorem attachmentHTensor_ne_zero (b delta : ℕ) : attachmentHTensor b delta≠0 := by
  intro hz
  have he:=attachmentHTensor_action_inverse b delta
  rw [hz,map_zero] at he
  exact witnessAttachmentBinaryRepeatedWord_ne_zero b delta he.symm

def attachmentHCyclic (b delta : ℕ) :
    Subrepresentation (wordRep (witnessAttachment b delta).card 4) :=
  cyclicSubrepresentation (wordRep _ _) (attachmentHTensor b delta)

theorem attachmentHCyclic_eq (b delta : ℕ) :
    cyclicSpan (wordRep (witnessAttachment b delta).card 4)
      (witnessAttachmentBinaryRepeatedWord b delta)=(attachmentHCyclic b delta).toSubmodule := by
  apply le_antisymm
  · apply (cyclicSpan_le_iff (wordRep _ _) (witnessAttachmentBinaryRepeatedWord b delta)
      (attachmentHCyclic b delta)).mpr
    rw [← attachmentHTensor_action_inverse]
    exact orbit_mem_cyclicSpan _ _ _
  · change cyclicSpan (wordRep _ _) (attachmentHTensor b delta)≤_
    apply (cyclicSpan_le_iff (wordRep _ _) (attachmentHTensor b delta)
      (cyclicSubrepresentation (wordRep _ _) (witnessAttachmentBinaryRepeatedWord b delta))).mpr
    rw [← attachmentHTensor_action]
    exact orbit_mem_cyclicSpan _ _ _

theorem attachmentHCyclic_repeated_image (b delta : ℕ) :
    (witnessAttachmentRepeatedCyclic b delta).toSubmodule.map
      (witnessAttachmentBinaryRepeatedMap b delta).toLinearMap=(attachmentHCyclic b delta).toSubmodule := by
  have he:=cyclicSpan_image (witnessAttachmentBinaryRepeatedMap b delta)
    (witnessAttachmentRepeatedWord b delta)
  exact he.trans (attachmentHCyclic_eq b delta)

end
end HSTZ
#print axioms HSTZ.attachmentHTensor_action
#print axioms HSTZ.attachmentHTensor_action_inverse
#print axioms HSTZ.attachmentHTensor_ne_zero
#print axioms HSTZ.attachmentHCyclic_eq
#print axioms HSTZ.attachmentHCyclic_repeated_image
