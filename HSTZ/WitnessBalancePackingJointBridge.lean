import HSTZ.WitnessBalancePackingBlockFamily

/-! Joint support for delta = 0 and delta = 1, restated in the generic joint
representation. The joint label is a free parameter `j`, and `j = 1` (resp. `2`) is
discharged by `subst`, so Lean never has to reduce
`witnessBalancePackingJointLabel delta` inside the projected-factor definitions. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

local instance wbjbPairACG (j : ℕ) : AddCommGroup ((witnessBalanceLocalProjectedFactor hk z 0).toSubmodule ⊗[ℂ]
    (witnessBalanceLocalProjectedFactor hk z j).toSubmodule) :=
  TensorProduct.addCommGroup (R:=ℂ)
    (M:=(witnessBalanceLocalProjectedFactor hk z 0).toSubmodule)
    (N:=(witnessBalanceLocalProjectedFactor hk z j).toSubmodule)
local instance wbjbPairModule (j : ℕ) : Module ℂ ((witnessBalanceLocalProjectedFactor hk z 0).toSubmodule ⊗[ℂ]
    (witnessBalanceLocalProjectedFactor hk z j).toSubmodule) := TensorProduct.leftModule

/-- Joint pair source with an explicit second label. -/
abbrev witnessBalanceJointPairRepAt (j : ℕ) : Representation ℂ
    (Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)) ×
      Equiv.Perm (Fin (witnessBalanceComponentSize hk z j)))
    ((witnessBalanceLocalProjectedFactor hk z 0).toSubmodule ⊗[ℂ]
      (witnessBalanceLocalProjectedFactor hk z j).toSubmodule) :=
  independentTensor (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
    (witnessBalanceLocalProjectedFactor hk z j).toRepresentation

/-- Joint induced pair representation with an explicit second label. -/
abbrev witnessBalanceJointRepAt (j : ℕ) :=
  Representation.ind (sumPermHom (finSumFinEquiv.symm :
      Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z j) ≃
        Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z j)))
    (witnessBalanceJointPairRepAt hk z j)
end

theorem witnessBalanceJointRepAt_tail_support {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 0 hk)) (j : ℕ) (hj : j = 1) {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z j) nu)
    (ht : nu.colLen 0 ≤ 2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t) (witnessBalanceJointRepAt hk z j),
      Function.Injective J := by
  subst hj
  exact witnessBalanceTwosTail_actual_tableau_induced_support hk z t ht

theorem witnessBalanceJointRepAt_three_support {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 1 hk)) (j : ℕ) (hj : j = 2) {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z j) nu)
    (ht : nu.colLen 0 ≤ 2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t) (witnessBalanceJointRepAt hk z j),
      Function.Injective J := by
  subst hj
  exact witnessBalanceTwosThree_actual_tableau_induced_support hk z t ht

/-- delta = 0 joint support in the generic joint representation. -/
theorem witnessBalance_joint_bridge_zero {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 0 hk)) {nu : YoungDiagram}
    (t : Tableau (witnessBalancePackingJointDegree hk z) nu) (ht : nu.colLen 0 ≤ 2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t) (witnessBalanceJointRep hk z),
      Function.Injective J :=
  witnessBalanceJointRepAt_tail_support hk z (witnessBalancePackingJointLabel 0) rfl t ht

/-- delta = 1 joint support in the generic joint representation. -/
theorem witnessBalance_joint_bridge_one {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 1 hk)) {nu : YoungDiagram}
    (t : Tableau (witnessBalancePackingJointDegree hk z) nu) (ht : nu.colLen 0 ≤ 2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t) (witnessBalanceJointRep hk z),
      Function.Injective J :=
  witnessBalanceJointRepAt_three_support hk z (witnessBalancePackingJointLabel 1) rfl t ht

end
end HSTZ
#print axioms HSTZ.witnessBalanceJointRepAt_tail_support
#print axioms HSTZ.witnessBalanceJointRepAt_three_support
#print axioms HSTZ.witnessBalance_joint_bridge_zero
#print axioms HSTZ.witnessBalance_joint_bridge_one
