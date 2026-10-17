import HSTZ.BlockInductionSwap
import HSTZ.ContainedSpechtSupport
import HSTZ.StaircaseBlockInduction

/-! The short contained-four-row completion, using swapped induction carriers and
the prescribed staircase cyclic space. Support for the smaller core is a map
hypothesis; staircase universality is not asserted here. -/
namespace HSTZ
open OAI.Saxl
open scoped TensorProduct

/-- Four-row-first induction composes with the smaller-core-first map. -/
theorem staircase_fourRow_first_induced_embedding (h : ℕ) (hh : 1 ≤ h)
    {nu xi : YoungDiagram}
    (s : Tableau (staircase h).card nu) (u : Tableau (bandSize h 2) xi)
    (hxi : xi.colLen 0 ≤ 4)
    (f : Representation.IntertwiningMap (spechtRep s)
      (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ E : Representation.IntertwiningMap
      (Representation.ind (A := Specht u ⊗[ℂ] Specht s)
        (sumPermHom (swapPositionBlocks (cutPositions h 2)))
        (independentTensor (spechtRep u) (spechtRep s)))
      (staircaseCyclic (h+2)).toRepresentation, Function.Injective E := by
  obtain ⟨M, hM, _⟩ := exists_blockInductionSwap (R := ℂ) (cutPositions h 2)
    (spechtRep s) (spechtRep u)
  obtain ⟨N, hN⟩ := staircase_twoBand_block_induced_embedding h hh s u hxi f hf
  exact ⟨N.comp M, hN.comp hM.1⟩

/-- Containment suffices, given support for every canonical smaller-core Specht
module. This universal core input is an explicit hypothesis, not proved here. -/
theorem staircase_contained_fourRow_support (h : ℕ) (hh : 1 ≤ h)
    {xi mu : YoungDiagram}
    (u : Tableau (bandSize h 2) xi) (t : Tableau (staircase (h+2)).card mu)
    (hxi : xi.colLen 0 ≤ 4) (hc : xi ≤ mu)
    (hcore : ∀ p : Nat.Partition (staircase h).card,
      ∃ f : Representation.IntertwiningMap (spechtRep (partitionTableau p))
        (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation,
        Function.Injective f) :
    ∃ E : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic (h+2)).toRepresentation, Function.Injective E := by
  obtain ⟨p, J, hJ⟩ := contained_specht_embedding_of_containment u t hc
    (swapPositionBlocks (cutPositions h 2))
  obtain ⟨f, hf⟩ := hcore p
  obtain ⟨N, hN⟩ := staircase_fourRow_first_induced_embedding h hh
    (partitionTableau p) u hxi f hf
  exact ⟨N.comp J, hN.comp hJ⟩

end HSTZ
#print axioms HSTZ.staircase_fourRow_first_induced_embedding
#print axioms HSTZ.staircase_contained_fourRow_support
