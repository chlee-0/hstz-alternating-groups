import HSTZ.WitnessBalancePieriGroups

/-! Return of the two local nonzero maps to the component product group.
Builds on APIs from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Native target tableaux
remain explicit; this is not the global assembly of H, the other factor and the
packing. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

private theorem perm_inverse {m n : ℕ} (e : Fin m ≃ Fin n) (g : Equiv.Perm (Fin n)) :
    positionPermHom e (positionPermHom e.symm g)=g := by
  ext i
  simp [positionPermHom,Equiv.permCongr_apply]

private theorem perm_inverse_back {m n : ℕ} (e : Fin m ≃ Fin n) (g : Equiv.Perm (Fin m)) :
    positionPermHom e.symm (positionPermHom e g)=g := by
  ext i
  simp [positionPermHom,Equiv.permCongr_apply]

section
variable {k b n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b 0 hk))

private abbrev actualTailSpace :=
  (witnessBalanceLocalProjectedFactor hk z 0).toSubmodule ⊗[ℂ]
    (witnessBalanceLocalProjectedFactor hk z 1).toSubmodule
local instance : AddCommGroup (actualTailSpace hk z) := TensorProduct.addCommGroup
local instance : Module ℂ (actualTailSpace hk z) := TensorProduct.leftModule

/-- Both projected factors under their independent component actions. -/
def witnessBalanceTwosTailActualProduct :
    Representation ℂ (Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)) ×
      Equiv.Perm (Fin (witnessBalanceComponentSize hk z 1))) (actualTailSpace hk z) :=
  independentTensor (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
    (witnessBalanceLocalProjectedFactor hk z 1).toRepresentation

private theorem native_actual_tail_block
    (g : Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)))
    (h : Equiv.Perm (Fin (witnessBalanceComponentSize hk z 1))) :
    sumPermHom (finSumFinEquiv.symm :
      Fin ((witnessAttachment (b+1) 0).card+1) ≃
        Fin (witnessAttachment (b+1) 0).card ⊕ Fin 1)
      (positionPermHom (witnessBalanceTwosPositions hk z).symm g,
       positionPermHom (witnessBalanceTailPositions hk z).symm h)=
    positionPermHom (witnessBalanceTwosTailPositions hk z).symm
      (sumPermHom (finSumFinEquiv.symm :
        Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1) ≃
          Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 1)) (g,h)) := by
  have he := witnessBalance_twos_tail_group hk z
    (positionPermHom (witnessBalanceTwosPositions hk z).symm g)
    (positionPermHom (witnessBalanceTailPositions hk z).symm h)
  rw [perm_inverse,perm_inverse] at he
  have hi := congrArg (positionPermHom (witnessBalanceTwosTailPositions hk z).symm) he
  rw [perm_inverse_back] at hi
  exact hi

/-- Native target with the inverse joint position and the block action. -/
def witnessBalanceTwosTailActualTarget {nu : YoungDiagram}
    (t : Tableau ((witnessAttachment (b+1) 0).card+1) nu) :
    Representation ℂ (Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)) ×
      Equiv.Perm (Fin (witnessBalanceComponentSize hk z 1))) (Specht t) :=
  (spechtRep t).comp ((positionPermHom (witnessBalanceTwosTailPositions hk z).symm).comp
    (sumPermHom (finSumFinEquiv.symm :
      Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1) ≃
        Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 1))))

end

section
variable {k b n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b 1 hk))

private abbrev actualThreeSpace :=
  (witnessBalanceLocalProjectedFactor hk z 0).toSubmodule ⊗[ℂ]
    (witnessBalanceLocalProjectedFactor hk z 2).toSubmodule
local instance : AddCommGroup (actualThreeSpace hk z) := TensorProduct.addCommGroup
local instance : Module ℂ (actualThreeSpace hk z) := TensorProduct.leftModule

/-- Both projected factors under their independent component actions. -/
def witnessBalanceTwosThreeActualProduct :
    Representation ℂ (Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)) ×
      Equiv.Perm (Fin (witnessBalanceComponentSize hk z 2))) (actualThreeSpace hk z) :=
  independentTensor (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
    (witnessBalanceLocalProjectedFactor hk z 2).toRepresentation

private theorem native_actual_three_block
    (g : Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)))
    (h : Equiv.Perm (Fin (witnessBalanceComponentSize hk z 2))) :
    sumPermHom (finSumFinEquiv.symm :
      Fin ((witnessAttachment (b+1) 0).card+3) ≃
        Fin (witnessAttachment (b+1) 0).card ⊕ Fin 3)
      (positionPermHom (witnessBalanceTwosPositions hk z).symm g,
       positionPermHom (witnessBalanceThreePositions hk z).symm h)=
    positionPermHom (witnessBalanceTwosThreePositions hk z).symm
      (sumPermHom (finSumFinEquiv.symm :
        Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2) ≃
          Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 2)) (g,h)) := by
  have he := witnessBalance_twos_three_group hk z
    (positionPermHom (witnessBalanceTwosPositions hk z).symm g)
    (positionPermHom (witnessBalanceThreePositions hk z).symm h)
  rw [perm_inverse,perm_inverse] at he
  have hi := congrArg (positionPermHom (witnessBalanceTwosThreePositions hk z).symm) he
  rw [perm_inverse_back] at hi
  exact hi

/-- Native target with the inverse joint position and the block action. -/
def witnessBalanceTwosThreeActualTarget {nu : YoungDiagram}
    (t : Tableau ((witnessAttachment (b+1) 0).card+3) nu) :
    Representation ℂ (Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)) ×
      Equiv.Perm (Fin (witnessBalanceComponentSize hk z 2))) (Specht t) :=
  (spechtRep t).comp ((positionPermHom (witnessBalanceTwosThreePositions hk z).symm).comp
    (sumPermHom (finSumFinEquiv.symm :
      Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2) ≃
        Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 2))))

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceTwosTailActualProduct
#print axioms HSTZ.witnessBalanceTwosTailActualTarget
#print axioms HSTZ.witnessBalanceTwosThreeActualProduct
#print axioms HSTZ.witnessBalanceTwosThreeActualTarget
