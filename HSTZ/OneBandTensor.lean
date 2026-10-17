import HSTZ.OneBandSource

/-! The one-band source in the cyclic carrier used by the independent
position-block tensor. The native HSTZ/OpenAI word coordinates are retained. -/
namespace HSTZ
open OAI.Saxl

noncomputable abbrev oneBandCyclicRepresentation (h : ℕ) :=
  (cyclicSubrepresentation (wordRep _ _) (bandPairWord h 1)).toRepresentation

/-- Carrier and action conversion; the underlying one-row map is unchanged. -/
noncomputable def oneBandCyclicSourceMap (h : ℕ) {mu : YoungDiagram}
    (u : Tableau (bandSize h 1) mu) (hmu : mu.colLen 0 ≤ 1) :
    Representation.IntertwiningMap (spechtRep u) (oneBandCyclicRepresentation h) :=
  oneBandSourceMap h u hmu

theorem oneBandCyclicSourceMap_injective (h : ℕ) {mu : YoungDiagram}
    (u : Tableau (bandSize h 1) mu) (hmu : mu.colLen 0 ≤ 1) :
    Function.Injective (oneBandCyclicSourceMap h u hmu).toLinearMap :=
  oneBandSourceMap_injective h u hmu

open scoped TensorProduct

abbrev ShiftedOneCoreCarrier (h : ℕ) :=
  ↥(cyclicSpan (wordRep _ _) (shiftedCoreWord h 1))

noncomputable abbrev shiftedOneCoreRepresentation (h : ℕ) :=
  (cyclicSubrepresentation (wordRep _ _) (shiftedCoreWord h 1)).toRepresentation

/-- Independent position-block tensor map, with its carriers named. -/
noncomputable def oneBandTensorMap (h : ℕ) {mu nu : YoungDiagram}
    (t : Tableau (staircase h).card mu) (u : Tableau (bandSize h 1) nu)
    (hnu : nu.colLen 0 ≤ 1)
    (core : Representation.IntertwiningMap (spechtRep t) (shiftedOneCoreRepresentation h)) :
    Representation.IntertwiningMap (independentTensor (spechtRep t) (spechtRep u))
      (independentTensor (shiftedOneCoreRepresentation h) (oneBandCyclicRepresentation h)) :=
  independentTensorMap (R := ℂ)
    (G := Equiv.Perm (Fin (staircase h).card))
    (H := Equiv.Perm (Fin (bandSize h 1)))
    (V := Specht t) (W := Specht u)
    (V' := ShiftedOneCoreCarrier h) (W' := OneBandCarrier h)
    core (oneBandCyclicSourceMap h u hnu)

theorem oneBandTensorMap_injective (h : ℕ) {mu nu : YoungDiagram}
    (t : Tableau (staircase h).card mu) (u : Tableau (bandSize h 1) nu)
    (hnu : nu.colLen 0 ≤ 1)
    (core : Representation.IntertwiningMap (spechtRep t) (shiftedOneCoreRepresentation h))
    (hcore : Function.Injective core.toLinearMap) :
    Function.Injective (oneBandTensorMap h t u hnu core).toLinearMap :=
  independentTensorMap_injective (K := ℂ)
    (G := Equiv.Perm (Fin (staircase h).card))
    (H := Equiv.Perm (Fin (bandSize h 1)))
    (V := Specht t) (W := Specht u)
    (V' := ShiftedOneCoreCarrier h) (W' := OneBandCarrier h)
    core (oneBandCyclicSourceMap h u hnu) hcore (oneBandCyclicSourceMap_injective h u hnu)

end HSTZ
#print axioms HSTZ.oneBandCyclicSourceMap
#print axioms HSTZ.oneBandCyclicSourceMap_injective

#print axioms HSTZ.oneBandTensorMap
#print axioms HSTZ.oneBandTensorMap_injective
