import HSTZ.WitnessBalanceUnmatchedSupport
import HSTZ.WitnessBalanceThreeSupport
import HSTZ.WitnessBalanceTwosSupport
import HSTZ.BalanceEvenSingletonInduction

/-! For delta = 1, the ordinary induction of the twos and height-three projected
factors, each pulled back along its component positions. This is local block support
only; support for the remaining factors is not addressed here. Uses declarations from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 1 hk))

/-- The native block degree equals the sum of the two component degrees. -/
theorem witnessBalance_twos_three_degree :
    (witnessAttachment (b+1) 0).card+3=
      witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2 := by
  rw [witnessBalance_twos_positions_card,witnessBalance_three_positions_card]

/-- The joint position equivalence, built from the two component position
equivalences. -/
def witnessBalanceTwosThreePositions : Fin ((witnessAttachment (b+1) 0).card+3) ≃
    Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (witnessBalanceTwosPositions hk z)
    (witnessBalanceThreePositions hk z)).trans finSumFinEquiv)

theorem witnessBalance_twos_three_positions_left (i : Fin (witnessAttachment (b+1) 0).card) :
    witnessBalanceTwosThreePositions hk z (finSumFinEquiv (.inl i))=
      finSumFinEquiv (.inl (witnessBalanceTwosPositions hk z i)) := by
  simp [witnessBalanceTwosThreePositions]

theorem witnessBalance_twos_three_positions_right (i : Fin 3) :
    witnessBalanceTwosThreePositions hk z (finSumFinEquiv (.inr i))=
      finSumFinEquiv (.inr (witnessBalanceThreePositions hk z i)) := by
  simp [witnessBalanceTwosThreePositions]

/-- Ordinary induction of the tensor product of the two local projected factors,
pulled back along the native positions. The remaining labels and factors are
treated separately. -/
def witnessBalanceTwosThreeInduced := by
  let W := witnessBalanceLocalProjectedFactor hk z 0
  let V := witnessBalanceLocalProjectedFactor hk z 2
  letI : AddCommGroup (W.toSubmodule ⊗[ℂ] V.toSubmodule) := TensorProduct.addCommGroup
  letI : Module ℂ (W.toSubmodule ⊗[ℂ] V.toSubmodule) := TensorProduct.leftModule
  exact Representation.ind (A:=W.toSubmodule ⊗[ℂ] V.toSubmodule)
    (sumPermHom (finSumFinEquiv.symm : Fin ((witnessAttachment (b+1) 0).card+3) ≃
      Fin (witnessAttachment (b+1) 0).card ⊕ Fin 3))
    (independentTensor
      (W.toRepresentation.comp (positionPermHom (witnessBalanceTwosPositions hk z)))
      (V.toRepresentation.comp (positionPermHom (witnessBalanceThreePositions hk z))))

/-- For delta = 1, every Specht module with at most two rows embeds in the induction
of the twos and height-three local factors. The case b = 0 is included. -/
theorem witnessBalanceTwosThree_induced_support {nu : YoungDiagram}
    (t : Tableau ((witnessAttachment (b+1) 0).card+3) nu) (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceTwosThreeInduced hk z), Function.Injective J := by
  let e : Fin ((witnessAttachment (b+1) 0).card+3) ≃
      Fin (witnessAttachment (b+1) 0).card ⊕ Fin 3 := finSumFinEquiv.symm
  obtain ⟨f,hf⟩ := balanceEvenSingleton_induced_support (b+1) 3 (by omega)
    (Or.inr rfl) (by omega) (balanceOutputTwoTableau (b+1))
    (balanceSingletonTableau 3) e t ht
  let W := balanceProjectedSquare (balanceOutputTwoTableau (b+1))
    (balanceInOutputs ({2} : Set ℕ)) (balanceInOutputs_invariant _)
  let V := balanceProjectedSquare (balanceSingletonTableau 3)
    (balanceInOutputs ({3} : Set ℕ)) (balanceInOutputs_invariant _)
  let U := witnessBalanceLocalProjectedFactor hk z 0
  let X := witnessBalanceLocalProjectedFactor hk z 2
  let H := Equiv.Perm (Fin (witnessAttachment (b+1) 0).card) × Equiv.Perm (Fin 3)
  let G := Equiv.Perm (Fin ((witnessAttachment (b+1) 0).card+3))
  let S := W.toSubmodule ⊗[ℂ] V.toSubmodule
  let T := U.toSubmodule ⊗[ℂ] X.toSubmodule
  letI : NeZero (Nat.card H : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card H).ne'⟩
  let D := independentTensorMap (witnessBalanceTwosProjectedMap hk z)
    (witnessBalanceThreeProjectedMap hk z)
  have hD : Function.Injective D := independentTensorMap_injective _ _
    (witnessBalanceTwosProjectedMap_injective hk z)
    (witnessBalanceThreeProjectedMap_injective hk z)
  let I := @inducedMap ℂ H G S T
    inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    TensorProduct.addCommGroup TensorProduct.leftModule
    _ _ (sumPermHom e) D
  have hI : Function.Injective I := @inducedMap_injective ℂ H G S T
    inferInstance inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    TensorProduct.addCommGroup TensorProduct.leftModule
    _ _ (sumPermHom e) D hD
  exact ⟨I.comp f,hI.comp hf⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_twos_three_degree
#print axioms HSTZ.witnessBalanceTwosThreePositions
#print axioms HSTZ.witnessBalance_twos_three_positions_left
#print axioms HSTZ.witnessBalance_twos_three_positions_right
#print axioms HSTZ.witnessBalanceTwosThreeInduced
#print axioms HSTZ.witnessBalanceTwosThree_induced_support
