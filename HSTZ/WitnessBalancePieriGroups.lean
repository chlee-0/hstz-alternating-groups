import HSTZ.WitnessBalanceTwosTailPieri

/-! Native and component block permutation identities for both original Pieri branches.
Reuses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). These are group
equations, not a conjugation of induced modules or a global target map for `H`. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical
section
variable {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 0 hk))

/-- The native x1 block homomorphism and the component block homomorphism are conjugate
by the joint `E`. -/
theorem witnessBalance_twos_tail_group
    (g : Equiv.Perm (Fin (witnessAttachment (b+1) 0).card)) (h : Equiv.Perm (Fin 1)) :
    positionPermHom (witnessBalanceTwosTailPositions hk z)
      (sumPermHom (finSumFinEquiv.symm : Fin ((witnessAttachment (b+1) 0).card+1) ≃
        Fin (witnessAttachment (b+1) 0).card ⊕ Fin 1) (g,h))=
    sumPermHom (finSumFinEquiv.symm :
      Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1) ≃
        Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 1))
      (positionPermHom (witnessBalanceTwosPositions hk z) g,
       positionPermHom (witnessBalanceTailPositions hk z) h) := by
  ext i
  obtain ⟨v,rfl⟩ := (finSumFinEquiv :
    Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 1) ≃
      Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1)).surjective i
  cases v <;> simp [positionPermHom,sumPermHom,OAI.Saxl.sumPerm,
    witnessBalanceTwosTailPositions,Equiv.permCongr_apply]
end

section
variable {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 1 hk))

/-- The native x3 block homomorphism and the twos/height-3 block homomorphisms, preserving
both ordered factors. -/
theorem witnessBalance_twos_three_group
    (g : Equiv.Perm (Fin (witnessAttachment (b+1) 0).card)) (h : Equiv.Perm (Fin 3)) :
    positionPermHom (witnessBalanceTwosThreePositions hk z)
      (sumPermHom (finSumFinEquiv.symm : Fin ((witnessAttachment (b+1) 0).card+3) ≃
        Fin (witnessAttachment (b+1) 0).card ⊕ Fin 3) (g,h))=
    sumPermHom (finSumFinEquiv.symm :
      Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2) ≃
        Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 2))
      (positionPermHom (witnessBalanceTwosPositions hk z) g,
       positionPermHom (witnessBalanceThreePositions hk z) h) := by
  ext i
  obtain ⟨v,rfl⟩ := (finSumFinEquiv :
    Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 2) ≃
      Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2)).surjective i
  cases v <;> simp [positionPermHom,sumPermHom,OAI.Saxl.sumPerm,
    witnessBalanceTwosThreePositions,Equiv.permCongr_apply]
end
end
end HSTZ
#print axioms HSTZ.witnessBalance_twos_tail_group
#print axioms HSTZ.witnessBalance_twos_three_group
