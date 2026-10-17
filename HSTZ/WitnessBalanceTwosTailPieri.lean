import HSTZ.WitnessBalanceTailPositions
import HSTZ.WitnessBalanceTwosThreePieri

/-! Ordinary induction for the delta0 twos and whole tail. Adapts the concrete
Pieri induction pattern and interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Both projected factors and their position pullbacks are kept. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 0 hk))

theorem witnessBalance_twos_tail_degree : (witnessAttachment (b+1) 0).card+1=
    witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1 := by
  rw [witnessBalance_twos_positions_card,witnessBalance_tail_positions_card]

def witnessBalanceTwosTailPositions : Fin ((witnessAttachment (b+1) 0).card+1) ≃
    Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (witnessBalanceTwosPositions hk z)
    (witnessBalanceTailPositions hk z)).trans finSumFinEquiv)

theorem witnessBalance_twos_tail_positions_left (i : Fin (witnessAttachment (b+1) 0).card) :
    witnessBalanceTwosTailPositions hk z (finSumFinEquiv (.inl i))=
      finSumFinEquiv (.inl (witnessBalanceTwosPositions hk z i)) := by
  simp [witnessBalanceTwosTailPositions]

theorem witnessBalance_twos_tail_positions_right (i : Fin 1) :
    witnessBalanceTwosTailPositions hk z (finSumFinEquiv (.inr i))=
      finSumFinEquiv (.inr (witnessBalanceTailPositions hk z i)) := by
  simp [witnessBalanceTwosTailPositions]

def witnessBalanceTwosTailInduced := by
  let W := witnessBalanceLocalProjectedFactor hk z 0
  let V := witnessBalanceLocalProjectedFactor hk z 1
  letI : AddCommGroup (W.toSubmodule ⊗[ℂ] V.toSubmodule) := TensorProduct.addCommGroup
  letI : Module ℂ (W.toSubmodule ⊗[ℂ] V.toSubmodule) := TensorProduct.leftModule
  exact Representation.ind (A:=W.toSubmodule ⊗[ℂ] V.toSubmodule)
    (sumPermHom (finSumFinEquiv.symm : Fin ((witnessAttachment (b+1) 0).card+1) ≃
      Fin (witnessAttachment (b+1) 0).card ⊕ Fin 1))
    (independentTensor
      (W.toRepresentation.comp (positionPermHom (witnessBalanceTwosPositions hk z)))
      (V.toRepresentation.comp (positionPermHom (witnessBalanceTailPositions hk z))))

/-- Every two-row target lies in the delta0 twos-and-whole-tail induction. The x1
legality, the even precursor, the source maps and both factors are handled internally. -/
theorem witnessBalanceTwosTail_induced_support {nu : YoungDiagram}
    (t : Tableau ((witnessAttachment (b+1) 0).card+1) nu) (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceTwosTailInduced hk z), Function.Injective J := by
  let e : Fin ((witnessAttachment (b+1) 0).card+1) ≃
      Fin (witnessAttachment (b+1) 0).card ⊕ Fin 1 := finSumFinEquiv.symm
  obtain ⟨xi,s,he,hh,hstrip,_,_⟩ := balanceEvenPrecursor_pieri (b+1) 1
    (Or.inl rfl) (by omega) t ht
  let aligned := containedBlockTableau s t hstrip.1 e
  have hi := containedBlockTableau_matching s t hstrip.1 e
  obtain ⟨E,hE⟩ := pieri_block_embedding s aligned hstrip e hi
  let Q := tableauSpechtMap t aligned
  have hQ : Function.Injective Q := (tableauSpechtMap_bijective t aligned).1
  let P := oneRowInducedMap (spechtRep s) (oneRowTableau 1)
    (oneRowDiagram_rows 1) (sumPermHom e)
  have hP : Function.Injective P := oneRowInducedMap_injective
    (spechtRep s) (oneRowTableau 1) (oneRowDiagram_rows 1) (sumPermHom e)
  obtain ⟨B,hB⟩ := witnessBalanceTwos_projected_support hk z s he hh
  obtain ⟨C,hC⟩ := witnessBalanceTail_native_projected_support hk z
  let U := witnessBalanceLocalProjectedFactor hk z 0
  let V := witnessBalanceLocalProjectedFactor hk z 1
  let H := Equiv.Perm (Fin (witnessAttachment (b+1) 0).card) × Equiv.Perm (Fin 1)
  let G := Equiv.Perm (Fin ((witnessAttachment (b+1) 0).card+1))
  let S := Specht s ⊗[ℂ] Specht (oneRowTableau 1)
  let T := U.toSubmodule ⊗[ℂ] V.toSubmodule
  letI : NeZero (Nat.card H : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card H).ne'⟩
  let D := independentTensorMap B C
  have hD : Function.Injective D := independentTensorMap_injective B C hB hC
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
  exact ⟨I.comp (P.comp (E.comp Q)),hI.comp (hP.comp (hE.comp hQ))⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_twos_tail_degree
#print axioms HSTZ.witnessBalanceTwosTailPositions
#print axioms HSTZ.witnessBalance_twos_tail_positions_left
#print axioms HSTZ.witnessBalance_twos_tail_positions_right
#print axioms HSTZ.witnessBalanceTwosTailInduced
#print axioms HSTZ.witnessBalanceTwosTail_induced_support
