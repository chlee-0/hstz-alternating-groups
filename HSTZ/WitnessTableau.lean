import HSTZ.WitnessDiagram
import OAI.RepresentationTheory.Saxl.SignEquivalence

/-! A canonical tableau of the paper's asymmetric witness. The paper's guard is an
explicit hypothesis; these declarations do not identify any of its marked core/band
cuts with the native staircase carrier. -/
namespace HSTZ
open OAI.Saxl

noncomputable def witnessTableau (k b delta : ℕ) (hk : 5 ≤ k) :
    Tableau (k*(k+1)/2+2*b+delta) (witnessDiagram k b delta hk) :=
  canonicalTableau _ (witnessDiagram_card k b delta hk)

/-- The paper parameters. No extension of the witness to small k is asserted. -/
structure PaperWitnessGuard (k b delta : ℕ) : Prop where
  staircase_bound : 5 ≤ k
  parity : delta≤1
  positive_remainder : 1≤2*b+delta
  remainder_bound : 2*b+delta≤k+1

theorem paperWitness_width_gt_height (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    (witnessDiagram k b delta hp.staircase_bound).colLen 0 <
      (witnessDiagram k b delta hp.staircase_bound).rowLen 0 := by
  rw [witnessDiagram_height, witnessDiagram_width]
  have hr := hp.positive_remainder
  omega

end HSTZ
#print axioms HSTZ.witnessTableau
#print axioms HSTZ.paperWitness_width_gt_height
