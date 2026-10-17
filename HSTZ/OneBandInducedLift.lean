import HSTZ.StaircaseOneBandStabilizer
import HSTZ.StaircaseInducedSupport

/-! A fully typed one-step induction/projection lift. The proposition is inferred
from the generic theorem and keeps its projection identity. -/
namespace HSTZ
open scoped TensorProduct

noncomputable def staircaseOneBandLift (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) (hnu : nu.colLen 0 ≤ 1)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :=
  @staircase_induced_embedding_lift h 1
    (OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u)
    TensorProduct.addCommGroup TensorProduct.leftModule (oneBandConstituent h t u)
    (Classical.choose (staircase_oneBand_stabilizer_embedding h t u hnu f hf))
    (Classical.choose_spec (staircase_oneBand_stabilizer_embedding h t u hnu f hf))

end HSTZ
#check HSTZ.staircaseOneBandLift
#print axioms HSTZ.staircaseOneBandLift
