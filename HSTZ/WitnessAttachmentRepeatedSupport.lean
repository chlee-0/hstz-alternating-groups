import HSTZ.WitnessAttachmentRepeatedLift

/-! The restricted attachment cyclic image map.
Reuses `cyclicImageMap` and its surjectivity from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Source and image are the sign-twisted mixed and ordinary image cyclic carriers of the
repeated map and the canonical mixed generator. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev witnessAttachmentRepeatedCyclicImageMap (b delta : ℕ) :=
  cyclicImageMap (witnessAttachmentRepeatedMap b delta) (witnessCanonicalAttachmentPair b delta)

theorem witnessAttachmentRepeatedCyclicImageMap_surjective (b delta : ℕ) :
    Function.Surjective (witnessAttachmentRepeatedCyclicImageMap b delta) :=
  cyclicImageMap_surjective (witnessAttachmentRepeatedMap b delta) (witnessCanonicalAttachmentPair b delta)

end
end HSTZ
#print axioms HSTZ.witnessAttachmentRepeatedCyclicImageMap
#print axioms HSTZ.witnessAttachmentRepeatedCyclicImageMap_surjective
