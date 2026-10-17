import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.WitnessBalanceProjectedFactors
import HSTZ.WitnessBalanceUnmatchedWords

/-! Support for the original unmatched singleton component (label 3+s) in the full
local projected square. Reuses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0)
and the existing neighboring transport pattern. Both letters, the source tableau and
its size, and E are kept explicit. The existing local projector and its range are reused. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (s : ℕ) (hd : delta≤1) (hs : k-(2+delta)=2*s+1)

def witnessBalanceUnmatchedPairMap :=
  (positionRelabelIntertwiner (witnessBalanceUnmatchedPositions hk z s hd hs)).comp
    (encodedLetterLift (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs)
      (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs))

theorem witnessBalanceUnmatchedPairMap_injective :
    Function.Injective (witnessBalanceUnmatchedPairMap hk z s hd hs) :=
  (positionRelabel (witnessBalanceUnmatchedPositions hk z s hd hs)).injective.comp
    (encodedLetterLift_injective _ _ (witnessBalanceUnmatchedRowLetter hk s hd hs).injective
      (witnessBalanceUnmatchedRowLetter hk s hd hs).injective)

/-- Both Specht maps, the `wordTensor` coordinates and the original local projector
agree on every tensor in the full square. -/
theorem witnessBalanceUnmatched_square_projection
    (q : Specht (balanceSingletonTableau (k-2*s)) ⊗[ℂ]
      Specht (balanceSingletonTableau (k-2*s))) :
    witnessBalanceLocalProjectedMap hk z (3+s)
      (TensorProduct.map (witnessBalanceUnmatchedSpechtMap hk z s hd hs).toLinearMap
        (witnessBalanceUnmatchedSpechtMap hk z s hd hs).toLinearMap q)=
    witnessBalanceUnmatchedPairMap hk z s hd hs
      (coordinateProjection (balanceInOutputs ({k-2*s} : Set ℕ))
        (((wordTensorIntertwiner _ _ _).comp (spechtTensorInclusion (balanceSingletonTableau (k-2*s)) (balanceSingletonTableau (k-2*s)))) q)) := by
  let F := witnessBalanceUnmatchedSpechtMap hk z s hd hs
  have heq : (witnessBalanceLocalProjectedMap hk z (3+s)).toLinearMap.comp
      (TensorProduct.map F.toLinearMap F.toLinearMap)=
    (witnessBalanceUnmatchedPairMap hk z s hd hs).toLinearMap.comp
      ((coordinateProjection (balanceInOutputs ({k-2*s} : Set ℕ))).comp
        ((wordTensorIntertwiner _ _ _).comp (spechtTensorInclusion (balanceSingletonTableau (k-2*s)) (balanceSingletonTableau (k-2*s)))).toLinearMap) := by
    apply TensorProduct.ext'
    intro x y
    change coordinateProjection (witnessBalanceLocalPairWords hk z (3+s))
      (wordTensor _ _ _ ((F x).val ⊗ₜ[ℂ] (F y).val))=
      witnessBalanceUnmatchedPairMap hk z s hd hs
        (coordinateProjection (balanceInOutputs ({k-2*s} : Set ℕ))
          (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val)))
    have hp := witnessBalanceUnmatched_pair_projection hk z s hd hs
      (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val))
    rw [encodedLetterLift_tensor,positionRelabel_tensor] at hp
    exact hp
  exact DFunLike.congr_fun heq q

private theorem unmatched_projected_mem
    (x : (balanceProjectedSquare (balanceSingletonTableau (k-2*s))
      (balanceInOutputs ({k-2*s} : Set ℕ)) (balanceInOutputs_invariant _)).toSubmodule) :
    witnessBalanceUnmatchedPairMap hk z s hd hs x.val ∈
      (witnessBalanceLocalProjectedFactor hk z (3+s)).toSubmodule := by
  obtain ⟨q,hq⟩ := x.property
  refine ⟨TensorProduct.map (witnessBalanceUnmatchedSpechtMap hk z s hd hs).toLinearMap
    (witnessBalanceUnmatchedSpechtMap hk z s hd hs).toLinearMap q,?_⟩
  change witnessBalanceLocalProjectedMap hk z (3+s)
    (TensorProduct.map (witnessBalanceUnmatchedSpechtMap hk z s hd hs).toLinearMap
      (witnessBalanceUnmatchedSpechtMap hk z s hd hs).toLinearMap q)=_
  rw [witnessBalanceUnmatched_square_projection]
  apply congrArg (witnessBalanceUnmatchedPairMap hk z s hd hs)
  exact hq

/-- Transport of the filtered full square to the original label 3+s range, using
`positionPermHom E`, both row-letter casts, and the source tableau and size. -/
def witnessBalanceUnmatchedProjectedMap : Representation.IntertwiningMap
    (balanceProjectedSquare (balanceSingletonTableau (k-2*s))
      (balanceInOutputs ({k-2*s} : Set ℕ)) (balanceInOutputs_invariant _)).toRepresentation
    ((witnessBalanceLocalProjectedFactor hk z (3+s)).toRepresentation.comp
      (positionPermHom (witnessBalanceUnmatchedPositions hk z s hd hs))) where
  toLinearMap := ((witnessBalanceUnmatchedPairMap hk z s hd hs).toLinearMap.domRestrict _).codRestrict _
    (unmatched_projected_mem hk z s hd hs)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBalanceUnmatchedPairMap hk z s hd hs).map_action g x.val

theorem witnessBalanceUnmatchedProjectedMap_injective :
    Function.Injective (witnessBalanceUnmatchedProjectedMap hk z s hd hs) := by
  intro x y h
  apply Subtype.ext
  exact witnessBalanceUnmatchedPairMap_injective hk z s hd hs (congrArg Subtype.val h)

/-- Support of the one-row target of the given height in the original unmatched
singleton component (label 3+s). All placement, source, action, letter and projection
inputs are discharged. -/
theorem witnessBalanceUnmatched_projected_support :
    ∃ J : Representation.IntertwiningMap (spechtRep (oneRowTableau (k-2*s)))
      ((witnessBalanceLocalProjectedFactor hk z (3+s)).toRepresentation.comp
        (positionPermHom (witnessBalanceUnmatchedPositions hk z s hd hs))), Function.Injective J := by
  obtain ⟨f,hf⟩ := balanceSingleton_projected_support (k-2*s) (balanceSingletonTableau (k-2*s))
  exact ⟨(witnessBalanceUnmatchedProjectedMap hk z s hd hs).comp f,
    (witnessBalanceUnmatchedProjectedMap_injective hk z s hd hs).comp hf⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceUnmatchedPairMap_injective
#print axioms HSTZ.witnessBalanceUnmatched_square_projection
#print axioms HSTZ.witnessBalanceUnmatchedProjectedMap
#print axioms HSTZ.witnessBalanceUnmatchedProjectedMap_injective
#print axioms HSTZ.witnessBalanceUnmatched_projected_support
