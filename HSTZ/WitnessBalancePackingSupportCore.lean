import HSTZ.WitnessBalancePackingSupportMap

/-! Packing support for the witness, for general delta, from joint two-row
support. The main theorem is conditional on the joint two-row induced support
hypothesis `hjoint`. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

/-- Packing support, given the joint two-row induced support. -/
theorem witnessBalance_support_of_joint (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    (hjoint : ∀ {nu : YoungDiagram}
      (t : Tableau (witnessBalancePackingJointDegree hp.staircase_bound z) nu),
      nu.colLen 0 ≤ 2 → ∃ J : Representation.IntertwiningMap (spechtRep t)
        (witnessBalanceJointRep hp.staircase_bound z), Function.Injective J)
    {mu : YoungDiagram} (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j ≤ youngPrefix (balancePacking k b delta) j) :
    0 < kronecker z z s := by
  obtain ⟨D,hzero,hlast,hc,p,hrows,E,hE⟩ :=
    paperWitness_balance_physical_tower_embedding k b delta hp z s hprefix
  choose L hL using fun v : TowerIdx (witnessBalancePackingBlocks k delta).length
      (witnessBalancePackingBlocks k delta).length =>
    witnessBalance_block_local_support hp.staircase_bound z hp.parity hjoint v (p v.val) (hrows v.val).2
  exact witnessBalance_pos_of_tower_injection hp.staircase_bound z hp.parity p L hL s E hE

end
end HSTZ
#print axioms HSTZ.witnessBalance_support_of_joint
