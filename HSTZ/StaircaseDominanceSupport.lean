import HSTZ.YoungDiagramCompat
import HSTZ.StaircaseDominanceArithmetic
import HSTZ.StaircaseRowGeometry
import HSTZ.StaircasePrefixSupport

/-! Staircase support for targets with a short first row that are not dominated by
the staircase. The dominance direction is explicit: some target row prefix exceeds
the corresponding staircase row prefix. Support for the smaller core remains a
hypothesis. -/
namespace HSTZ
open OAI.Saxl

theorem staircase_failed_prefix_range (m : ℕ) (nu : YoungDiagram)
    (hsize : nu.card = (staircase m).card) {j : ℕ}
    (hfail : prefixSum (staircase m).rowLen j < prefixSum nu.rowLen j) : j < m := by
  by_contra hn
  have hj : (staircase m).colLen 0 ≤ j := by rw [staircase_colLen]; omega
  have ht := row_prefix_full (staircase m) hj
  have hb := row_prefix_card_bound nu j
  omega


theorem staircase_short_row_failure_capacity (h : ℕ) (mu : YoungDiagram)
    (hsize : mu.card = (staircase (h+2)).card) (hrow : mu.rowLen 0 < h+2)
    (hfail : ∃ j, prefixSum (staircase (h+2)).rowLen j < prefixSum mu.rowLen j) :
    bandSize h 2 ≤ prefixSum mu.rowLen 4 := by
  obtain ⟨j, hj⟩ := hfail
  have hr := staircase_failed_prefix_range (h+2) mu hsize hj
  have hf : j*(2*(h+2)-j+1) < 2*prefixSum mu.rowLen j := by
    rw [← staircase_prefix_twice (h+2) hr.le]
    omega
  have hc := short_row_failed_prefix_capacity mu.rowLen_antitone hrow hr.le hf
  rw [bandPath_card]
  omega

/-- Target embedding, with no failed-index or four-row-capacity hypothesis. -/
theorem staircase_short_row_nondominated_support (h : ℕ) (hh : 1 ≤ h)
    {mu : YoungDiagram} (t : Tableau (staircase (h+2)).card mu)
    (hrow : mu.rowLen 0 < h+2)
    (hnd : ¬ ∀ j, prefixSum mu.rowLen j ≤ prefixSum (staircase (h+2)).rowLen j)
    (hcore : ∀ p : Nat.Partition (staircase h).card,
      ∃ f : Representation.IntertwiningMap (spechtRep (partitionTableau p))
        (cyclicSubrepresentation (wordRep _ _) (staircaseWord h)).toRepresentation,
        Function.Injective f) :
    ∃ E : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic (h+2)).toRepresentation, Function.Injective E := by
  classical
  have hsize : mu.card = (staircase (h+2)).card := by
    simpa [YoungDiagram.card] using (Fintype.card_congr t).symm
  push_neg at hnd
  exact staircase_fourRow_prefix_support h hh t
    (staircase_short_row_failure_capacity h mu hsize hrow hnd) hcore

end HSTZ
#print axioms HSTZ.staircase_short_row_failure_capacity
#print axioms HSTZ.staircase_short_row_nondominated_support

#print axioms HSTZ.staircase_failed_prefix_range
