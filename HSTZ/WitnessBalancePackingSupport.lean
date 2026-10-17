import HSTZ.WitnessBalancePackingSupportCore
import HSTZ.WitnessBalancePackingJointBridge

/-! Packing support for the asymmetric witness, and oriented Kronecker positivity
without a support hypothesis. The proof composes the physical tower, the local block
injections, the tower-to-assembly map, the return to H, Frobenius reciprocity and
projected positivity. Uses declarations from OpenAI's `math` repository (commit
adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

/-- Packing support for the asymmetric witness: every target satisfying the prefix
bound `hprefix` for the (unsorted) balance packing has positive Kronecker
coefficient `kronecker z z s`. -/
theorem paperWitness_balance_support (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) {mu : YoungDiagram}
    (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j ≤ youngPrefix (balancePacking k b delta) j) :
    0 < kronecker z z s := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp.parity with h | h
  · subst h
    exact witnessBalance_support_of_joint k b 0 hp z
      (fun t ht => witnessBalance_joint_bridge_zero hp.staircase_bound z t ht) s hprefix
  · subst h
    exact witnessBalance_support_of_joint k b 1 hp z
      (fun t ht => witnessBalance_joint_bridge_one hp.staircase_bound z t ht) s hprefix

/-- Oriented Kronecker positivity for the asymmetric witness: for every target,
the sum of the coefficients of the target and of its transpose is positive. No
support hypothesis is needed. -/
theorem paperWitness_oriented_pos (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    {nu : YoungDiagram} (target : Tableau n nu) :
    0 < kronecker z z target + kronecker z z (transposeTableau target) :=
  paperWitness_oriented_pos_of_balance_consumer k b delta hp z
    (fun s hs => paperWitness_balance_support k b delta hp z s hs) target

end
end HSTZ
#print axioms HSTZ.paperWitness_balance_support
#print axioms HSTZ.paperWitness_oriented_pos
