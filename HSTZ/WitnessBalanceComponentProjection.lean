import HSTZ.WitnessBalanceTailCyclic
import HSTZ.PositionLayer

/-! The retained-word coordinate projection splits along the cut into a component
projection and a projection on the remaining positions. Pair coordinates and the
remaining label constraints are kept. Uses declarations from OpenAI's `math`
repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (a : ℕ)

abbrev witnessBalanceComponentSquareSource :=
  (independentTensor (witnessBalanceComponentRows hk z a).toRepresentation
    (witnessBalanceOtherRows hk z a).toRepresentation).tprod
  (independentTensor (witnessBalanceComponentRows hk z a).toRepresentation
    (witnessBalanceOtherRows hk z a).toRepresentation)

def witnessBalanceLocalPairWords
    (w : Fin (witnessBalanceComponentSize hk z a) → Fin (witnessBalancePairDim k b delta hk)) : Prop :=
  (∀ i, witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk (w i)) ∧
    ∀ i, witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk (w i)=a

def witnessBalanceOtherPairWords
    (w : Fin (witnessBalanceOtherSize hk z a) → Fin (witnessBalancePairDim k b delta hk)) : Prop :=
  (∀ i, witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk (w i)) ∧
    ∀ i, witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk (w i)=
      witnessBalanceLabel hk z ((witnessBalanceComponentCut hk z a).symm (.inr i))

theorem witnessBalance_component_pair_selector
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w ↔
      witnessBalanceLocalPairWords hk z a (leftWord (witnessBalanceComponentCut hk z a) w) ∧
      witnessBalanceOtherPairWords hk z a (rightWord (witnessBalanceComponentCut hk z a) w) := by
  constructor
  · rintro ⟨hA,he⟩
    refine ⟨⟨fun i => hA _,fun i => ?_⟩,⟨fun i => hA _,fun i => he _⟩⟩
    exact (he _).trans (witnessBalanceComponentCut_left hk z a i)
  · rintro ⟨⟨hA,he⟩,⟨hB,hf⟩⟩
    constructor
    · intro i
      obtain ⟨j,rfl⟩ := (witnessBalanceComponentCut hk z a).symm.surjective i
      cases j with
      | inl j => exact hA j
      | inr j => exact hB j
    · intro i
      obtain ⟨j,rfl⟩ := (witnessBalanceComponentCut hk z a).symm.surjective i
      cases j with
      | inl j => exact (he j).trans (witnessBalanceComponentCut_left hk z a j).symm
      | inr j => exact hf j

theorem witnessBalance_component_pair_projection
    (x : WordSpace (witnessBalanceComponentSize hk z a) (witnessBalancePairDim k b delta hk))
    (y : WordSpace (witnessBalanceOtherSize hk z a) (witnessBalancePairDim k b delta hk)) :
    coordinateProjection (witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z)
      (positionProduct (witnessBalanceComponentCut hk z a) x y) =
    positionProduct (witnessBalanceComponentCut hk z a)
      (coordinateProjection (witnessBalanceLocalPairWords hk z a) x)
      (coordinateProjection (witnessBalanceOtherPairWords hk z a) y) := by
  funext w
  simp only [coordinateProjection_apply,positionProduct,witnessBalance_component_pair_selector hk z a w]
  split_ifs <;> simp_all

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_component_pair_selector
#print axioms HSTZ.witnessBalance_component_pair_projection
