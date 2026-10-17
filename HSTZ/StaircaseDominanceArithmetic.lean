import HSTZ.BalancePrefix

/-! The short-first-row failure branch of the staircase induction.
Only antitone natural sequences and legal prefix bounds are used; the arithmetic
assumes no support or core universality. -/
namespace HSTZ

/-- A staircase-prefix failure cannot occur within the first three short rows. -/
theorem short_row_failed_prefix_depth {a : ℕ → ℕ} (ha : Antitone a)
    {m j : ℕ} (hrow : a 0 < m) (hj : j ≤ m)
    (hfail : j*(2*m-j+1) < 2*prefixSum a j) : 4 ≤ j := by
  have hjpos : 1 ≤ j := by
    by_contra hn
    have hz : j = 0 := by omega
    simp [hz] at hfail
  have havg := prefix_average_bound ha (a := 1) hjpos
  have hsum : prefixSum a j ≤ j*a 0 := by
    simpa [prefix_succ] using havg
  have hrowprod := Nat.mul_le_mul_left j (show a 0+1 ≤ m by omega)
  have hnorm := congrArg (fun n : ℕ => j*n)
    (show (2*m-j+1)+j = 2*m+1 by omega)
  by_contra hn
  have hsquare := Nat.mul_le_mul_left j (show j ≤ 3 by omega)
  nlinarith

/-- Legal failed prefixes force a stronger margin than the path-size capacity. -/
theorem short_row_failed_prefix_four {a : ℕ → ℕ} (ha : Antitone a)
    {m j : ℕ} (hrow : a 0 < m) (hj : j ≤ m)
    (hfail : j*(2*m-j+1) < 2*prefixSum a j) :
    2*m+2 < prefixSum a 4 := by
  have hdepth := short_row_failed_prefix_depth ha hrow hj hfail
  have havg := prefix_average_bound ha hdepth
  have hsquare := Nat.mul_le_mul_left j hj
  have hnorm := congrArg (fun n : ℕ => j*n)
    (show (2*m-j+1)+j = 2*m+1 by omega)
  by_contra hn
  have hprod := Nat.mul_le_mul_left j (show prefixSum a 4 ≤ 2*m+2 by omega)
  nlinarith

theorem short_row_failed_prefix_capacity {a : ℕ → ℕ} (ha : Antitone a)
    {m j : ℕ} (hrow : a 0 < m) (hj : j ≤ m)
    (hfail : j*(2*m-j+1) < 2*prefixSum a j) :
    2*m-1 ≤ prefixSum a 4 := by
  have := short_row_failed_prefix_four ha hrow hj hfail
  omega

end HSTZ
#print axioms HSTZ.short_row_failed_prefix_depth
#print axioms HSTZ.short_row_failed_prefix_four
#print axioms HSTZ.short_row_failed_prefix_capacity
