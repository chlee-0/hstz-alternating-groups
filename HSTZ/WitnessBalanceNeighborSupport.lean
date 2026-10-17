import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.WitnessBalanceNeighborCarrier
import HSTZ.WitnessPathLetterTransport
import HSTZ.BalanceNeighboringSupport

/-! Support of the full neighboring component square in the original positions.
Reuses local support, tensor, cyclic and private finite-basis results, building on
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). No target packing hypothesis is used. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (a s : ℕ)
    (hs : 2*s+1<k-(2+delta))

private def neighborSquareWords : Representation.IntertwiningMap
    ((witnessBalanceComponentRows hk z a).toRepresentation.tprod
      (witnessBalanceComponentRows hk z a).toRepresentation)
    (wordRep (witnessBalanceComponentSize hk z a) (witnessBalancePairDim k b delta hk)) where
  toLinearMap := (wordTensor _ _ _).toLinearMap.comp
    (cyclicTensorInclusion (wordRep _ _) (wordRep _ _)
      (witnessBalanceComponentWord hk z a) (witnessBalanceComponentWord hk z a)).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    have he := (cyclicTensorInclusion (wordRep _ _) (wordRep _ _)
      (witnessBalanceComponentWord hk z a) (witnessBalanceComponentWord hk z a)).map_action (g,g) q
    exact (congrArg (wordTensor _ _ _) he).trans
      ((wordTensorIntertwiner _ _ _).map_action g _)

private theorem neighborPredicate_invariant
    (g : Equiv.Perm (Fin (witnessBalanceComponentSize hk z a))) w :
    witnessBalanceLocalPairWords hk z a (w ∘ g) ↔
      witnessBalanceLocalPairWords hk z a w := by
  constructor
  · rintro ⟨hA,hL⟩
    exact ⟨fun i => by simpa only [Function.comp_apply,g.apply_symm_apply] using hA (g.symm i),
      fun i => by simpa only [Function.comp_apply,g.apply_symm_apply] using hL (g.symm i)⟩
  · rintro ⟨hA,hL⟩
    exact ⟨fun i => hA (g i),fun i => hL (g i)⟩

private def neighborProjection : Representation.IntertwiningMap
    (wordRep (witnessBalanceComponentSize hk z a) (witnessBalancePairDim k b delta hk))
    (wordRep (witnessBalanceComponentSize hk z a) (witnessBalancePairDim k b delta hk)) where
  toLinearMap := coordinateProjection (witnessBalanceLocalPairWords hk z a)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext w
    change (if witnessBalanceLocalPairWords hk z a w then x (w ∘ g) else 0)=
      (if witnessBalanceLocalPairWords hk z a (w ∘ g) then x (w ∘ g) else 0)
    rw [neighborPredicate_invariant]

/-- Projector onto the original component for all component labels.
The local square and invariance proofs above are reused. -/
def witnessBalanceLocalProjectedMap := (neighborProjection hk z a).comp (neighborSquareWords hk z a)

/-- Image of the full component square under the original local selector.
This is not the cyclic span of a repeated tensor. -/
def witnessBalanceNeighborProjectedSquare : Subrepresentation
    (wordRep (witnessBalanceComponentSize hk z (3+s)) (witnessBalancePairDim k b delta hk)) where
  toSubmodule := ((neighborProjection hk z (3+s)).comp (neighborSquareWords hk z (3+s))).toLinearMap.range
  apply_mem_toSubmodule g x hx := by
    obtain ⟨q,rfl⟩ := hx
    exact ⟨((witnessBalanceComponentRows hk z (3+s)).toRepresentation.tprod
      (witnessBalanceComponentRows hk z (3+s)).toRepresentation) g q,
      ((neighborProjection hk z (3+s)).comp (neighborSquareWords hk z (3+s))).map_action g q⟩

include hs

def witnessBalanceNeighborPairMap :=
  (positionRelabelIntertwiner (witnessBalanceNeighborPositions hk z s hs)).comp
    (encodedLetterLift (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs)
      (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs))

theorem witnessBalanceNeighborPairMap_injective :
    Function.Injective (witnessBalanceNeighborPairMap hk z s hs) :=
  (positionRelabel (witnessBalanceNeighborPositions hk z s hs)).injective.comp
    (encodedLetterLift_injective _ _ (witnessBalanceNeighborRowLetter hk s hs).injective
      (witnessBalanceNeighborRowLetter hk s hs).injective)

private theorem neighbor_square_transport
    (q : Specht (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)) ⊗[ℂ]
      Specht (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))) :
    witnessBalanceNeighborPairMap hk z s hs
      (((wordTensorIntertwiner _ _ _).comp
        (spechtTensorInclusion (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))
          (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)))) q)=
    neighborSquareWords hk z (3+s)
      (TensorProduct.map (witnessBalanceNeighborSpechtMap hk z s hs).toLinearMap
        (witnessBalanceNeighborSpechtMap hk z s hs).toLinearMap q) := by
  let F := witnessBalanceNeighborSpechtMap hk z s hs
  have heq : (witnessBalanceNeighborPairMap hk z s hs).toLinearMap.comp
      (((wordTensorIntertwiner _ _ _).comp
        (spechtTensorInclusion (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))
          (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)))).toLinearMap)=
    (neighborSquareWords hk z (3+s)).toLinearMap.comp (TensorProduct.map F.toLinearMap F.toLinearMap) := by
    apply TensorProduct.ext'
    intro x y
    change positionRelabel (witnessBalanceNeighborPositions hk z s hs)
      (encodedLetterLift _ _ (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val)))=
      wordTensor _ _ _ ((F x).val ⊗ₜ[ℂ] (F y).val)
    rw [encodedLetterLift_tensor,positionRelabel_tensor]
    rfl
  exact DFunLike.congr_fun heq q

private theorem neighbor_projected_mem
    (x : (balanceProjectedSquare (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))
      (balanceInOutputs (Set.Icc (witnessBalanceNeighborSize (k:=k) s)
        (witnessBalanceNeighborSize (k:=k) s+1))) (balanceInOutputs_invariant _)).toSubmodule) :
    witnessBalanceNeighborPairMap hk z s hs x.val ∈
      (witnessBalanceNeighborProjectedSquare hk z s).toSubmodule := by
  obtain ⟨q,hq⟩ := x.property
  refine ⟨TensorProduct.map (witnessBalanceNeighborSpechtMap hk z s hs).toLinearMap
    (witnessBalanceNeighborSpechtMap hk z s hs).toLinearMap q,?_⟩
  change coordinateProjection (witnessBalanceLocalPairWords hk z (3+s))
    (neighborSquareWords hk z (3+s) (TensorProduct.map _ _ q))=
      witnessBalanceNeighborPairMap hk z s hs x.val
  rw [← neighbor_square_transport hk z s hs q]
  have hp := witnessBalanceNeighbor_pair_projection hk z s hs
    (((wordTensorIntertwiner _ _ _).comp
      (spechtTensorInclusion (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))
        (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)))) q)
  change coordinateProjection _ (witnessBalanceNeighborPairMap hk z s hs _) =
    witnessBalanceNeighborPairMap hk z s hs (coordinateProjection _ _) at hp
  rw [hp]
  apply congrArg (witnessBalanceNeighborPairMap hk z s hs)
  exact hq

/-- Filtered full-square transport, with the inverse positions, both letters
and the component degree. -/
def witnessBalanceNeighborProjectedMap : Representation.IntertwiningMap
    (balanceProjectedSquare (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))
      (balanceInOutputs (Set.Icc (witnessBalanceNeighborSize (k:=k) s)
        (witnessBalanceNeighborSize (k:=k) s+1))) (balanceInOutputs_invariant _)).toRepresentation
    ((witnessBalanceNeighborProjectedSquare hk z s).toRepresentation.comp
      (positionPermHom (witnessBalanceNeighborPositions hk z s hs))) where
  toLinearMap := ((witnessBalanceNeighborPairMap hk z s hs).toLinearMap.domRestrict _).codRestrict _
    (neighbor_projected_mem hk z s hs)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBalanceNeighborPairMap hk z s hs).map_action g x.val

theorem witnessBalanceNeighborProjectedMap_injective :
    Function.Injective (witnessBalanceNeighborProjectedMap hk z s hs) := by
  intro x y h
  apply Subtype.ext
  exact witnessBalanceNeighborPairMap_injective hk z s hs (congrArg Subtype.val h)

/-- Complete support of the original component. All placement, action,
source, letter, interval and projection inputs are discharged in the proof. -/
theorem witnessBalanceNeighbor_projected_support {nu : YoungDiagram}
    (v : Tableau (2*witnessBalanceNeighborSize (k:=k) s+1) nu) (hnu : nu.colLen 0≤4) :
    ∃ J : Representation.IntertwiningMap (spechtRep v)
      ((witnessBalanceNeighborProjectedSquare hk z s).toRepresentation.comp
        (positionPermHom (witnessBalanceNeighborPositions hk z s hs))), Function.Injective J := by
  obtain ⟨f,hf⟩ := balanceNeighbor_projected_support _ (witnessBalance_neighbor_native_guard s hs)
    (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)) v hnu
  exact ⟨(witnessBalanceNeighborProjectedMap hk z s hs).comp f,
    (witnessBalanceNeighborProjectedMap_injective hk z s hs).comp hf⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceNeighborProjectedSquare
#print axioms HSTZ.witnessBalanceNeighborPairMap_injective
#print axioms HSTZ.witnessBalanceNeighborProjectedMap
#print axioms HSTZ.witnessBalanceNeighborProjectedMap_injective
#print axioms HSTZ.witnessBalanceNeighbor_projected_support

#print axioms HSTZ.witnessBalanceLocalProjectedMap
