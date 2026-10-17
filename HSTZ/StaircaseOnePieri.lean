import HSTZ.StaircaseOneBlockInduction
import HSTZ.OneRowInduction
import HSTZ.TableauAlignment
import HSTZ.OneRowTableau

/-! One-step horizontal-strip support, conditional on a supplied core injection.
Two-step support keeps its own carrier and guards. -/
namespace HSTZ
open scoped TensorProduct
/-- Horizontal-strip target support. Position alignment and smaller-core support
are explicit hypotheses; horizontal-strip Pieri does not supply them. -/
theorem staircase_oneStep_strip_embedding (h : ℕ)
    {nu mu xi : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card nu)
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase (h+1)).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) xi) (hxi : xi.colLen 0 ≤ 1)
    (hs : OAI.Saxl.HorizontalStrip nu mu)
    (hi : OAI.Saxl.tableauInclusion s t hs.1 = blockInclusion (OAI.Saxl.cutPositions h 1))
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep s)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ E : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (OAI.Saxl.staircaseCyclic (h+1)).toRepresentation, Function.Injective E := by
  let e := OAI.Saxl.cutPositions h 1
  obtain ⟨E, hE⟩ := pieri_block_embedding s t hs e hi
  let M := @oneRowInducedMap
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card)) (StaircasePositionGroup (h+1))
    (OAI.Saxl.Specht s) inferInstance inferInstance inferInstance inferInstance
    (OAI.Saxl.spechtRep s) (OAI.Saxl.bandSize h 1) xi u hxi (sumPermHom e)
  have hM : Function.Injective M.toLinearMap :=
    @oneRowInducedMap_injective
      (Equiv.Perm (Fin (OAI.Saxl.staircase h).card)) (StaircasePositionGroup (h+1))
      (OAI.Saxl.Specht s) inferInstance inferInstance inferInstance inferInstance
      (OAI.Saxl.spechtRep s) (OAI.Saxl.bandSize h 1) xi u hxi (sumPermHom e)
  obtain ⟨N, hN⟩ := staircase_oneBand_block_induced_embedding h s u (by omega) f hf
  exact ⟨N.comp (M.comp E), hN.comp (hM.comp hE)⟩

/-- Horizontal-strip target support assuming only smaller-core support; the
target tableau needs no position-matching hypothesis. -/
theorem staircase_oneStep_strip_embedding_of_core (h : ℕ)
    {nu mu xi : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card nu)
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase (h+1)).card mu)
    (u : OAI.Saxl.Tableau (OAI.Saxl.bandSize h 1) xi) (hxi : xi.colLen 0 ≤ 1)
    (hs : OAI.Saxl.HorizontalStrip nu mu)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep s)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ E : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (OAI.Saxl.staircaseCyclic (h+1)).toRepresentation, Function.Injective E := by
  obtain ⟨t', hi⟩ := exists_block_tableau s t hs.1 (OAI.Saxl.cutPositions h 1)
  obtain ⟨E, hE⟩ := staircase_oneStep_strip_embedding h s t' u hxi hs hi f hf
  exact ⟨E.comp (tableauSpechtMap t t'),
    hE.comp (tableauSpechtMap_bijective t t').1⟩

/-- Horizontal-strip support using internally chosen auxiliary one-row data.
Only the smaller-core embedding is a hypothesis. -/
theorem staircase_oneStep_strip_support (h : ℕ)
    {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card nu)
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase (h+1)).card mu)
    (hs : OAI.Saxl.HorizontalStrip nu mu)
    (f : Representation.IntertwiningMap (OAI.Saxl.spechtRep s)
      (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).toRepresentation)
    (hf : Function.Injective f) :
    ∃ E : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (OAI.Saxl.staircaseCyclic (h+1)).toRepresentation, Function.Injective E :=
  staircase_oneStep_strip_embedding_of_core h s t
    (oneRowTableau (OAI.Saxl.bandSize h 1))
    (oneRowDiagram_rows (OAI.Saxl.bandSize h 1)) hs f hf

end HSTZ
#print axioms HSTZ.staircase_oneStep_strip_embedding

#print axioms HSTZ.staircase_oneStep_strip_embedding_of_core

#print axioms HSTZ.staircase_oneStep_strip_support
