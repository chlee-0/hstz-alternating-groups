import HSTZ.YoungDiagramCompat
import HSTZ.ParityCapacity
import OAI.RepresentationTheory.Saxl.Basic

/-! Staircase rows and row-prefix formulas, with natural subtraction made explicit.
No representation support is concluded here. -/
namespace HSTZ
open OAI.Saxl

theorem staircase_row_length (m i : ℕ) : (staircase m).rowLen i = m-i := by
  have hh : ∀ j, j < (staircase m).rowLen i ↔ j < m-i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_staircase]
    omega
  have h₁ := hh ((staircase m).rowLen i)
  have h₂ := hh (m-i)
  omega

theorem staircase_prefix_twice (m : ℕ) {j : ℕ} (hj : j ≤ m) :
    2*prefixSum (staircase m).rowLen j = j*(2*m-j+1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hi := ih (by omega)
    rw [prefix_succ, staircase_row_length]
    have hx : 2*m-j+1 = (2*m-(j+1)+1)+1 := by omega
    have hr : j+2*(m-j) = 2*m-(j+1)+1 := by omega
    rw [Nat.mul_add, hi, hx, Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]
    omega

theorem row_prefix_card_bound (nu : YoungDiagram) (j : ℕ) :
    prefixSum nu.rowLen j ≤ nu.card := by
  rw [row_prefix_eq_capped_columns]
  calc
    prefixSum (capacity nu.colLen j) (nu.rowLen 0) ≤
        prefixSum nu.colLen (nu.rowLen 0) :=
      Finset.sum_le_sum (fun i _ => Nat.min_le_right _ _)
    _ = nu.card := by
      rw [← fromColumns_card nu.colLen nu.colLen_antitone (nu.rowLen 0), fromColumns_target]

theorem row_prefix_full (nu : YoungDiagram) {j : ℕ} (hj : nu.colLen 0 ≤ j) :
    prefixSum nu.rowLen j = nu.card := by
  rw [row_prefix_eq_capped_columns]
  have hc : capacity nu.colLen j = nu.colLen := by
    funext i
    exact Nat.min_eq_right ((nu.colLen_antitone (Nat.zero_le i)).trans hj)
  rw [hc, ← fromColumns_card nu.colLen nu.colLen_antitone (nu.rowLen 0), fromColumns_target]


end HSTZ
#print axioms HSTZ.staircase_row_length
#print axioms HSTZ.staircase_prefix_twice
#print axioms HSTZ.row_prefix_card_bound
#print axioms HSTZ.row_prefix_full
