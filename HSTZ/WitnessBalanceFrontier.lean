import HSTZ.WitnessBandSupport
import HSTZ.WitnessBalanceProjectedRange

/-! Conditional final step for the two remaining balance prefix cases.
The one-direction packing support is an explicit hypothesis (`balanceSupport`) here.
It is proved in `WitnessBalancePackingSupport` (`paperWitness_balance_support`), which
also gives oriented positivity without the hypothesis. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem paperWitness_oriented_pos_of_balance_consumer (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    (balanceSupport : ∀ {mu : YoungDiagram} (s : Tableau n mu),
      (∀ j, prefixSum mu.colLen j ≤ youngPrefix (balancePacking k b delta) j) →
        0 < kronecker z z s)
    {nu : YoungDiagram} (target : Tableau n nu) :
    0 < kronecker z z target + kronecker z z (transposeTableau target) := by
  rcases paperWitness_numeric_support_frontier k b delta hp target z with hh | hh | hh
  · have hs := balanceSupport target hh
    omega
  · have hs := balanceSupport (transposeTableau target) hh
    omega
  · exact hh

end
end HSTZ
#print axioms HSTZ.paperWitness_oriented_pos_of_balance_consumer
