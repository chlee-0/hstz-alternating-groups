import HSTZ.StaircaseOneBandBase

/-! Transport of the source action from the product of blocks to the label
stabilizer. The underlying injection is unchanged. -/
namespace HSTZ
open scoped TensorProduct
noncomputable abbrev oneBandConstituent (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) :
    Representation ℂ (staircaseLabelStabilizer h 1)
      (OAI.Saxl.Specht t ⊗[ℂ] OAI.Saxl.Specht u) :=
  (independentTensor (OAI.Saxl.spechtRep t) (OAI.Saxl.spechtRep u)).comp
    (staircaseLabelBlockEquiv h 1).symm.toMonoidHom

theorem staircase_oneBand_stabilizer_embedding (h : ℕ) {mu nu : YoungDiagram}
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) nu) (hnu : nu.colLen 0 ≤ 1)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ F : Representation.IntertwiningMap (oneBandConstituent h t u)
      (staircaseStabilizerRepresentation h 1), Function.Injective F := by
  obtain ⟨F, hF⟩ := staircase_oneBand_base_embedding h t u hnu f hf
  exact ⟨transportIntertwiner (staircaseLabelBlockEquiv h 1) F, hF⟩

end HSTZ
#print axioms HSTZ.staircase_oneBand_stabilizer_embedding
