import HSTZ.OneBandTensor
import HSTZ.FactorSupport

/-! Independent core/one-band tensor embedding into the selected stabilizer base.
The smaller-core injection is a hypothesis supplied by the caller. -/
namespace HSTZ
theorem staircase_oneBand_base_embedding (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) (hnu : nu.colLen 0 ≤ 1)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ F : Representation.IntertwiningMap
      (independentTensor (OAI.Saxl.spechtRep t) (OAI.Saxl.spechtRep u))
      (staircaseBaseRepresentation h 1), Function.Injective F := by
  obtain ⟨core, hcore⟩ := shiftedCore_embedding h 1 t f hf
  let M := oneBandTensorMap h t u hnu core
  have hM : Function.Injective M.toLinearMap :=
    oneBandTensorMap_injective h t u hnu core hcore
  exact ⟨(staircaseFactorToStabilizer h 1).comp M,
    (staircaseFactorToStabilizer_bijective h 1).1.comp hM⟩

end HSTZ
#print axioms HSTZ.staircase_oneBand_base_embedding
