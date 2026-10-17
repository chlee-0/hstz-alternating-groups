import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.WitnessBalanceProjectedFactors
import HSTZ.WitnessBalanceThreeWords

/-! Support of the original height-3 / label-2 component in the full local projected square.
Reuses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0) and the
neighboring-transport pattern. The existing local projector and its range are used directly. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 1 hk))

def witnessBalanceThreePairMap :=
  (positionRelabelIntertwiner (witnessBalanceThreePositions hk z)).comp
    (encodedLetterLift (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk)
      (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk))

theorem witnessBalanceThreePairMap_injective :
    Function.Injective (witnessBalanceThreePairMap hk z) :=
  (positionRelabel (witnessBalanceThreePositions hk z)).injective.comp
    (encodedLetterLift_injective _ _ (witnessBalanceThreeRowLetter hk).injective
      (witnessBalanceThreeRowLetter hk).injective)

/-- Both Specht maps, the physical `wordTensor` coordinates and the original local
projector agree on every tensor in the full native square. -/
theorem witnessBalanceThree_square_projection
    (q : Specht (balanceSingletonTableau 3) ⊗[ℂ]
      Specht (balanceSingletonTableau 3)) :
    witnessBalanceLocalProjectedMap hk z 2
      (TensorProduct.map (witnessBalanceThreeSpechtMap hk z).toLinearMap
        (witnessBalanceThreeSpechtMap hk z).toLinearMap q)=
    witnessBalanceThreePairMap hk z
      (coordinateProjection (balanceInOutputs ({3} : Set ℕ))
        (((wordTensorIntertwiner _ _ _).comp (spechtTensorInclusion (balanceSingletonTableau 3) (balanceSingletonTableau 3))) q)) := by
  let F := witnessBalanceThreeSpechtMap hk z
  have heq : (witnessBalanceLocalProjectedMap hk z 2).toLinearMap.comp
      (TensorProduct.map F.toLinearMap F.toLinearMap)=
    (witnessBalanceThreePairMap hk z).toLinearMap.comp
      ((coordinateProjection (balanceInOutputs ({3} : Set ℕ))).comp
        ((wordTensorIntertwiner _ _ _).comp (spechtTensorInclusion (balanceSingletonTableau 3) (balanceSingletonTableau 3))).toLinearMap) := by
    apply TensorProduct.ext'
    intro x y
    change coordinateProjection (witnessBalanceLocalPairWords hk z 2)
      (wordTensor _ _ _ ((F x).val ⊗ₜ[ℂ] (F y).val))=
      witnessBalanceThreePairMap hk z
        (coordinateProjection (balanceInOutputs ({3} : Set ℕ))
          (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val)))
    have hp := witnessBalanceThree_pair_projection hk z
      (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val))
    rw [encodedLetterLift_tensor,positionRelabel_tensor] at hp
    exact hp
  exact DFunLike.congr_fun heq q

private theorem three_projected_mem
    (x : (balanceProjectedSquare (balanceSingletonTableau 3)
      (balanceInOutputs ({3} : Set ℕ)) (balanceInOutputs_invariant _)).toSubmodule) :
    witnessBalanceThreePairMap hk z x.val ∈
      (witnessBalanceLocalProjectedFactor hk z 2).toSubmodule := by
  obtain ⟨q,hq⟩ := x.property
  refine ⟨TensorProduct.map (witnessBalanceThreeSpechtMap hk z).toLinearMap
    (witnessBalanceThreeSpechtMap hk z).toLinearMap q,?_⟩
  change witnessBalanceLocalProjectedMap hk z 2
    (TensorProduct.map (witnessBalanceThreeSpechtMap hk z).toLinearMap
      (witnessBalanceThreeSpechtMap hk z).toLinearMap q)=_
  rw [witnessBalanceThree_square_projection]
  apply congrArg (witnessBalanceThreePairMap hk z)
  exact hq

/-- Filtered full-square transport to the original label-2 range, with
`positionPermHom E`, both row-letter casts and the native caller and cardinality. -/
def witnessBalanceThreeProjectedMap : Representation.IntertwiningMap
    (balanceProjectedSquare (balanceSingletonTableau 3)
      (balanceInOutputs ({3} : Set ℕ)) (balanceInOutputs_invariant _)).toRepresentation
    ((witnessBalanceLocalProjectedFactor hk z 2).toRepresentation.comp
      (positionPermHom (witnessBalanceThreePositions hk z))) where
  toLinearMap := ((witnessBalanceThreePairMap hk z).toLinearMap.domRestrict _).codRestrict _
    (three_projected_mem hk z)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBalanceThreePairMap hk z).map_action g x.val

theorem witnessBalanceThreeProjectedMap_injective :
    Function.Injective (witnessBalanceThreeProjectedMap hk z) := by
  intro x y h
  apply Subtype.ext
  exact witnessBalanceThreePairMap_injective hk z (congrArg Subtype.val h)

/-- One-row-3 target support in the original height-3 / label-2 component.
All placement, source, action, letter and projection inputs are discharged. -/
theorem witnessBalanceThree_projected_support :
    ∃ J : Representation.IntertwiningMap (spechtRep (oneRowTableau 3))
      ((witnessBalanceLocalProjectedFactor hk z 2).toRepresentation.comp
        (positionPermHom (witnessBalanceThreePositions hk z))), Function.Injective J := by
  obtain ⟨f,hf⟩ := balanceSingleton_projected_support 3 (balanceSingletonTableau 3)
  exact ⟨(witnessBalanceThreeProjectedMap hk z).comp f,
    (witnessBalanceThreeProjectedMap_injective hk z).comp hf⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceThreePairMap_injective
#print axioms HSTZ.witnessBalanceThree_square_projection
#print axioms HSTZ.witnessBalanceThreeProjectedMap
#print axioms HSTZ.witnessBalanceThreeProjectedMap_injective
#print axioms HSTZ.witnessBalanceThree_projected_support
