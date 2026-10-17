import HSTZ.WitnessAttachmentRepeatedImage
import HSTZ.WitnessAttachmentColumns

/-! Transport of the canonical repeated attachment pair from row-height letters
to a two-letter alphabet, keeping the canonical positions and the diagonal action.
Uses the attachment row bound and `encodedLetterLift`, the tensor formula and the
cyclic-image declarations from OpenAI's `math` repository (commit adc7f1241,
Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessAttachmentBinaryLetter (b delta : ℕ) :
    Fin ((witnessAttachment b delta).colLen 0) ↪ Fin 2 where
  toFun i := ⟨i.val,lt_of_lt_of_le i.isLt (witnessAttachment_rows b delta)⟩
  inj' := by
    intro i j he
    exact Fin.ext (congrArg (fun z : Fin 2 => z.val) he)

abbrev witnessAttachmentBinaryRepeatedMap (b delta : ℕ) :=
  encodedLetterLift (n := (witnessAttachment b delta).card)
    (witnessAttachmentBinaryLetter b delta) (witnessAttachmentBinaryLetter b delta)

theorem witnessAttachmentBinaryRepeatedMap_injective (b delta : ℕ) :
    Function.Injective (witnessAttachmentBinaryRepeatedMap b delta) :=
  encodedLetterLift_injective _ _ (witnessAttachmentBinaryLetter b delta).injective
    (witnessAttachmentBinaryLetter b delta).injective

def witnessAttachmentBinaryRepeatedWord (b delta : ℕ) :
    WordSpace (witnessAttachment b delta).card (2*2) :=
  witnessAttachmentBinaryRepeatedMap b delta (witnessAttachmentRepeatedWord b delta)

theorem witnessAttachmentBinaryRepeatedWord_tensor (b delta : ℕ) :
    witnessAttachmentBinaryRepeatedWord b delta = wordTensor _ 2 2
      (letterLift (witnessAttachmentBinaryLetter b delta)
        (polytabloid (witnessCanonicalAttachment b delta)) ⊗ₜ[ℂ]
       letterLift (witnessAttachmentBinaryLetter b delta)
        (polytabloid (witnessCanonicalAttachment b delta))) :=
  encodedLetterLift_tensor _ _ _ _

theorem witnessAttachmentBinaryRepeatedWord_ne_zero (b delta : ℕ) :
    witnessAttachmentBinaryRepeatedWord b delta ≠ 0 := by
  intro he
  apply witnessAttachmentRepeatedWord_ne_zero b delta
  exact witnessAttachmentBinaryRepeatedMap_injective b delta
    (he.trans (witnessAttachmentBinaryRepeatedMap b delta).toLinearMap.map_zero.symm)

abbrev witnessAttachmentBinaryRepeatedCyclicMap (b delta : ℕ) :=
  cyclicImageMap (witnessAttachmentBinaryRepeatedMap b delta)
    (witnessAttachmentRepeatedWord b delta)

theorem witnessAttachmentBinaryRepeatedCyclicMap_bijective (b delta : ℕ) :
    Function.Bijective (witnessAttachmentBinaryRepeatedCyclicMap b delta) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact witnessAttachmentBinaryRepeatedMap_injective b delta (congrArg Subtype.val he)
  · exact cyclicImageMap_surjective _ _

/-- The binary row letters in column order, including the singleton positions. -/
theorem witnessAttachmentBinaryRowWord_ordered (b delta : ℕ)
    (i : WitnessAttachmentColumnOrder b delta) :
    witnessAttachmentBinaryLetter b delta
      (rowWord (witnessCanonicalAttachment b delta)
        (witnessAttachmentColumnPositions b delta i)) =
      witnessAttachmentOrderedRow b delta i := by
  apply Fin.ext
  exact witnessAttachmentColumnPositions_row b delta i


theorem witnessAttachmentBinaryRepeatedWord_coefficient (b delta : ℕ) :
    witnessAttachmentBinaryRepeatedWord b delta
      (mergeWords
        (witnessAttachmentBinaryLetter b delta ∘ rowWord (witnessCanonicalAttachment b delta))
        (witnessAttachmentBinaryLetter b delta ∘ rowWord (witnessCanonicalAttachment b delta))) = 1 := by
  rw [witnessAttachmentBinaryRepeatedWord_tensor,wordTensor_tmul,splitLeft_merge,splitRight_merge]
  rw [letterLift_eval _ (witnessAttachmentBinaryLetter b delta).injective]
  simp only [polytabloid_rowWord,mul_one]


end
end HSTZ
#print axioms HSTZ.witnessAttachmentBinaryLetter
#print axioms HSTZ.witnessAttachmentBinaryRepeatedMap_injective
#print axioms HSTZ.witnessAttachmentBinaryRepeatedWord_tensor
#print axioms HSTZ.witnessAttachmentBinaryRepeatedWord_ne_zero
#print axioms HSTZ.witnessAttachmentBinaryRepeatedCyclicMap_bijective

#print axioms HSTZ.witnessAttachmentBinaryRowWord_ordered

#print axioms HSTZ.witnessAttachmentBinaryRepeatedWord_coefficient
