import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.WitnessBalanceProjectedFactors
import HSTZ.WitnessBalanceTwosWords

/-! Support of the original output-2 component in the full local projected
square. Uses interfaces and a transport pattern adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Both letters, the source tableau
and `E` are kept, and the existing local projector and its range are reused. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

def witnessBalanceTwosPairMap :=
  (positionRelabelIntertwiner (witnessBalanceTwosPositions hk z)).comp
    (encodedLetterLift (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk))

theorem witnessBalanceTwosPairMap_injective :
    Function.Injective (witnessBalanceTwosPairMap hk z) :=
  (positionRelabel (witnessBalanceTwosPositions hk z)).injective.comp
    (encodedLetterLift_injective _ _ (witnessBalanceTwosRowLetter hk).injective
      (witnessBalanceTwosRowLetter hk).injective)

/-- Both Specht maps, the physical `wordTensor` coordinates and the original
local projector agree on every tensor in the full native square. -/
theorem witnessBalanceTwos_square_projection
    (q : Specht (balanceOutputTwoTableau (b+1)) ⊗[ℂ]
      Specht (balanceOutputTwoTableau (b+1))) :
    witnessBalanceLocalProjectedMap hk z 0
      (TensorProduct.map (witnessBalanceTwosSpechtMap hk z).toLinearMap
        (witnessBalanceTwosSpechtMap hk z).toLinearMap q)=
    witnessBalanceTwosPairMap hk z
      (coordinateProjection (balanceInOutputs ({2} : Set ℕ))
        (((wordTensorIntertwiner _ _ _).comp (spechtTensorInclusion (balanceOutputTwoTableau (b+1)) (balanceOutputTwoTableau (b+1)))) q)) := by
  let F := witnessBalanceTwosSpechtMap hk z
  have heq : (witnessBalanceLocalProjectedMap hk z 0).toLinearMap.comp
      (TensorProduct.map F.toLinearMap F.toLinearMap)=
    (witnessBalanceTwosPairMap hk z).toLinearMap.comp
      ((coordinateProjection (balanceInOutputs ({2} : Set ℕ))).comp
        ((wordTensorIntertwiner _ _ _).comp (spechtTensorInclusion (balanceOutputTwoTableau (b+1)) (balanceOutputTwoTableau (b+1)))).toLinearMap) := by
    apply TensorProduct.ext'
    intro x y
    change coordinateProjection (witnessBalanceLocalPairWords hk z 0)
      (wordTensor _ _ _ ((F x).val ⊗ₜ[ℂ] (F y).val))=
      witnessBalanceTwosPairMap hk z
        (coordinateProjection (balanceInOutputs ({2} : Set ℕ))
          (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val)))
    have hp := witnessBalanceTwos_pair_projection hk z
      (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val))
    rw [encodedLetterLift_tensor,positionRelabel_tensor] at hp
    exact hp
  exact DFunLike.congr_fun heq q

private theorem twos_projected_mem
    (x : (balanceProjectedSquare (balanceOutputTwoTableau (b+1))
      (balanceInOutputs ({2} : Set ℕ)) (balanceInOutputs_invariant _)).toSubmodule) :
    witnessBalanceTwosPairMap hk z x.val ∈
      (witnessBalanceLocalProjectedFactor hk z 0).toSubmodule := by
  obtain ⟨q,hq⟩ := x.property
  refine ⟨TensorProduct.map (witnessBalanceTwosSpechtMap hk z).toLinearMap
    (witnessBalanceTwosSpechtMap hk z).toLinearMap q,?_⟩
  change witnessBalanceLocalProjectedMap hk z 0
    (TensorProduct.map (witnessBalanceTwosSpechtMap hk z).toLinearMap
      (witnessBalanceTwosSpechtMap hk z).toLinearMap q)=_
  rw [witnessBalanceTwos_square_projection]
  apply congrArg (witnessBalanceTwosPairMap hk z)
  exact hq

/-- Filtered transport from the full square to the original label-0 range, with
`positionPermHom E`, both row-letter casts and the native source tableau. -/
def witnessBalanceTwosProjectedMap : Representation.IntertwiningMap
    (balanceProjectedSquare (balanceOutputTwoTableau (b+1))
      (balanceInOutputs ({2} : Set ℕ)) (balanceInOutputs_invariant _)).toRepresentation
    ((witnessBalanceLocalProjectedFactor hk z 0).toRepresentation.comp
      (positionPermHom (witnessBalanceTwosPositions hk z))) where
  toLinearMap := ((witnessBalanceTwosPairMap hk z).toLinearMap.domRestrict _).codRestrict _
    (twos_projected_mem hk z)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBalanceTwosPairMap hk z).map_action g x.val

theorem witnessBalanceTwosProjectedMap_injective :
    Function.Injective (witnessBalanceTwosProjectedMap hk z) := by
  intro x y h
  apply Subtype.ext
  exact witnessBalanceTwosPairMap_injective hk z (congrArg Subtype.val h)

/-- Two-row target support for even rows in the original output-2 component.
All placement, source, action, letter and projection inputs are discharged. -/
theorem witnessBalanceTwos_projected_support {nu : YoungDiagram}
    (v : Tableau (witnessAttachment (b+1) 0).card nu)
    (he : AttachmentEvenRows nu) (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep v)
      ((witnessBalanceLocalProjectedFactor hk z 0).toRepresentation.comp
        (positionPermHom (witnessBalanceTwosPositions hk z))), Function.Injective J := by
  obtain ⟨f,hf⟩ := balanceOutputTwo_projected_support (b+1) (by omega)
    (balanceOutputTwoTableau (b+1)) v he ht
  exact ⟨(witnessBalanceTwosProjectedMap hk z).comp f,
    (witnessBalanceTwosProjectedMap_injective hk z).comp hf⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceTwosPairMap_injective
#print axioms HSTZ.witnessBalanceTwos_square_projection
#print axioms HSTZ.witnessBalanceTwosProjectedMap
#print axioms HSTZ.witnessBalanceTwosProjectedMap_injective
#print axioms HSTZ.witnessBalanceTwos_projected_support
