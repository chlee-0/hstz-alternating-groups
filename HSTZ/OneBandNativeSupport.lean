import HSTZ.OneBandInducedLift
import HSTZ.NativeStaircaseCyclic

/-! A one-step induced tensor map into the native prescribed cyclic space.
The smaller-core injection is a hypothesis, not a universality theorem. -/
namespace HSTZ
open scoped TensorProduct

noncomputable def staircaseOneBandNativeMap (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) (hnu : nu.colLen 0 ≤ 1)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :=
  (Classical.choose (staircase_native_cyclic_embedding (h+1))).comp
    (Classical.choose (staircaseOneBandLift h t u hnu f hf))

theorem staircaseOneBandNativeMap_injective (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) (hnu : nu.colLen 0 ≤ 1)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    Function.Injective (staircaseOneBandNativeMap h t u hnu f hf).toLinearMap :=
  (Classical.choose_spec (staircase_native_cyclic_embedding (h+1))).comp
    (Classical.choose_spec (staircaseOneBandLift h t u hnu f hf)).1

end HSTZ
#check HSTZ.staircaseOneBandNativeMap
#print axioms HSTZ.staircaseOneBandNativeMap
#print axioms HSTZ.staircaseOneBandNativeMap_injective
