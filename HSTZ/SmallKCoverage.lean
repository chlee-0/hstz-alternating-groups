import HSTZ.YoungDiagramCompat
import HSTZ.BalancePacking

/-!
Numerical coverage for the small degrees k = 5, 6, using the unsorted
`balancePacking` and the existing `BandGeometry` with d = q = 2 and four-position
clearance. Together with `balancePacking_numeric_coverage` for k ≥ 7 this gives
numerical coverage for every k ≥ 5.

This is numerical coverage only. It does not weaken `PaperWitnessGuard` and does
not prove the small-k representation-support theorems.

The imported declarations keep their HSTZ and OpenAI attribution.
-/
namespace HSTZ.SmallKCoverage

abbrev Bal (nu : YoungDiagram) (A : List ℕ) : Prop :=
  ∀ t, prefixSum nu.colLen t ≤ youngPrefix A t

/-- One-point and two-prefix bounds transfer through a short profile envelope. -/
private theorem balance_of_envelope (nu : YoungDiagram) (A : List ℕ) (c : ℕ)
    (hsum : A.sum = nu.card) (hpos : ∀ a ∈ A, 0 < a)
    (henv : ∀ t, 2 ≤ t → min nu.card (c*t) ≤ youngPrefix A t)
    (hfirst : nu.colLen 0 ≤ A.length)
    (htwo : prefixSum nu.colLen 2 ≤ 2*c) : Bal nu A := by
  intro t
  by_cases ht0 : t = 0
  · subst t
    simp [prefixSum, youngPrefix]
  by_cases ht1 : t = 1
  · subst t
    rw [youngPrefix_one A hpos]
    simpa [prefixSum, Finset.sum_range_succ] using hfirst
  · have ht : 2 ≤ t := by omega
    have hav := prefix_average_bound nu.colLen_antitone ht
    have hmul := Nat.mul_le_mul_left t htwo
    have hlin : prefixSum nu.colLen t ≤ c*t := by nlinarith
    exact (le_min (column_prefix_le_card nu t) hlin).trans (henv t ht)

private theorem staircasePairs_lt {low k : ℕ} (h : k < low) : staircasePairs low k = [] := by
  rw [staircasePairs]; simp [h]

private theorem staircasePairs_self (low : ℕ) : staircasePairs low low = [low] := by
  rw [staircasePairs]; simp

private theorem staircasePairs_gt {low k : ℕ} (h : low < k) :
    staircasePairs low k = balancedPack 4 (2*k-1) ++ staircasePairs low (k-2) := by
  rw [staircasePairs]; simp [show ¬ k < low by omega, show k ≠ low by omega]

/-- Above the largest part the Young prefix is the full sum, so only t < B is checked. -/
private theorem envelope_of_check (A : List ℕ) (n c B : ℕ) (hB : ∀ a ∈ A, a ≤ B)
    (hsum : A.sum = n) (hchk : ∀ t < B, 2 ≤ t → min n (c*t) ≤ youngPrefix A t) :
    ∀ t, 2 ≤ t → min n (c*t) ≤ youngPrefix A t := by
  intro t ht
  by_cases htB : t < B
  · exact hchk t htB ht
  · rw [youngPrefix_eq_sum A (fun a ha => (hB a ha).trans (by omega)), hsum]
    exact min_le_left _ _

/-- Finite parameter arithmetic, not a partition enumeration.
The only valid (k,b,delta) rows are the 13 degrees 16,...,28. -/
private theorem profile_table {k b delta : ℕ}
    (hk : 5 ≤ k) (hkmax : k ≤ 6) (hd : delta ≤ 1)
    (hr : 0 < 2*b+delta) (hrmax : 2*b+delta ≤ k+1) :
    2*b+delta+1 ≤ (balancePacking k b delta).length ∧
    ∀ t, 2 ≤ t →
      min (k*(k+1)/2+2*b+delta) (max (k-1) (b+2)*t) ≤
        youngPrefix (balancePacking k b delta) t := by
  have h35 : staircasePairs 3 5 = balancedPack 4 9 ++ [3] := by
    rw [staircasePairs_gt (by decide : 3 < 5)]; simp [staircasePairs_self]
  have h45 : staircasePairs 4 5 = balancedPack 4 9 := by
    rw [staircasePairs_gt (by decide : 4 < 5)]; simp [staircasePairs_lt]
  have h36 : staircasePairs 3 6 = balancedPack 4 11 ++ balancedPack 4 7 := by
    rw [staircasePairs_gt (by decide : 3 < 6), staircasePairs_gt (by decide : 3 < 4)]
    simp [staircasePairs_lt]
  have h46 : staircasePairs 4 6 = balancedPack 4 11 ++ [4] := by
    rw [staircasePairs_gt (by decide : 4 < 6)]; simp [staircasePairs_self]
  have hb3 : b ≤ 3 := by omega
  interval_cases k <;> interval_cases b <;> interval_cases delta
  all_goals first
    | (exfalso; omega)
    | (simp only [balancePacking, Nat.reduceAdd, h35, h45, h36, h46]
       exact ⟨by decide, envelope_of_check _ _ _ 7 (by decide) (by decide) (by decide)⟩)

/-- A failed signed (2,2) capacity bounds the first height by r+1.
The all-even/odd-capacity value -1 is retained. -/
private theorem first_height_of_failed22 (h : ℕ → ℕ) {r delta : ℕ}
    (hpar : r % 2 = delta)
    (hfail : parityCapacity (fun i => h i-2) 2 delta < (r : ℤ)) :
    h 0 ≤ r+1 := by
  classical
  let P := prefixSum (fun i => (h i-2)/2) 2
  have hP : P = (h 0-2)/2 + (h 1-2)/2 := by
    simp [P, prefixSum, Finset.sum_range_succ]
  by_cases hd : delta = 0
  · simp only [parityCapacity, hd] at hfail
    change 2*(P : ℤ) < (r : ℤ) at hfail
    omega
  · have hd1 : delta = 1 := by omega
    rw [hd1] at hpar hfail
    by_cases ho : ∃ i < 2, (h i-2) % 2 = 1
    · simp only [parityCapacity, if_neg (by decide : 1 ≠ 0), if_pos ho] at hfail
      change 2*(P : ℤ)+1 < (r : ℤ) at hfail
      omega
    · simp only [parityCapacity, if_neg (by decide : 1 ≠ 0), if_neg ho] at hfail
      change 2*(P : ℤ)-1 < (r : ℤ) at hfail
      have hm : (h 0-2) % 2 ≠ 1 := fun hm => ho ⟨0, by decide, hm⟩
      omega

/-- If both two-prefixes are <= M and |nu| >= 2M > 0, the second
column has at least two cells; otherwise nu is a hook with at most 2M-1 cells. -/
private theorem first_height_of_small_two_prefixes (nu : YoungDiagram) {M : ℕ}
    (hne : 0 < nu.card) (hn : 2*M ≤ nu.card)
    (hR : prefixSum nu.rowLen 2 ≤ M)
    (hC : prefixSum nu.colLen 2 ≤ M) : nu.colLen 0+2 ≤ M := by
  have htotal : prefixSum nu.colLen (nu.rowLen 0) = nu.card := by
    rw [← fromColumns_card nu.colLen nu.colLen_antitone (nu.rowLen 0), fromColumns_target]
  have hw : 0 < nu.rowLen 0 := by
    by_contra h
    have hw0 : nu.rowLen 0 = 0 := by omega
    simp [hw0, prefixSum] at htotal
    omega
  have hC' := hC
  have hR' := hR
  simp only [prefixSum, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add] at hC' hR'
  have hsecond : 2 ≤ nu.colLen 1 := by
    by_contra h
    have htail : ∀ j, 1 ≤ j → nu.colLen j ≤ 1 := by
      intro j hj
      have hh := nu.colLen_anti 1 j hj
      omega
    have hp : ∀ t, prefixSum nu.colLen (t+1) ≤ nu.colLen 0+t := by
      intro t
      induction t with
      | zero => simp [prefixSum]
      | succ t ih =>
        rw [prefix_succ]
        have hh := htail (t+1) (by omega)
        omega
    have ht := hp (nu.rowLen 0-1)
    have he : nu.rowLen 0-1+1 = nu.rowLen 0 := by omega
    rw [he, htotal] at ht
    omega
  omega

/-- Capacity failure alone already gives `Bal` for the balance packing at k=5,6. -/
private theorem failed22_balance (nu : YoungDiagram) {k b delta : ℕ}
    (hk : 5 ≤ k) (hkmax : k ≤ 6) (hd : delta ≤ 1)
    (hr : 0 < 2*b+delta) (hrmax : 2*b+delta ≤ k+1)
    (hn : 2*nu.card = k*(k+1)+2*(2*b+delta))
    (hfail : parityCapacity (fun i => nu.colLen i-2) 2 delta < ((2*b+delta : ℕ) : ℤ)) :
    Bal nu (balancePacking k b delta) := by
  have hpar : (2*b+delta)%2 = delta := by omega
  obtain ⟨hsum, hpos, _, _⟩ := balancePacking_properties (by omega : 3 ≤ k) hd rfl hrmax hn
  obtain ⟨hlen, henv⟩ := profile_table hk hkmax hd hr hrmax
  have hcard : nu.card = k*(k+1)/2+2*b+delta := by omega
  have hfirst := first_height_of_failed22 nu.colLen hpar hfail
  have htwo := failed_capacity_prefix_sharp (by decide : 2 ≤ 2) hpar hfail
  apply balance_of_envelope nu _ (max (k-1) (b+2)) hsum hpos
  · intro t ht
    rw [hcard]
    exact henv t ht
  · omega
  · have hc := le_max_right (k-1) (b+2)
    omega

/-- Simultaneously small row and column two-prefixes also force `Bal`. -/
private theorem low22_balance (nu : YoungDiagram) {k b delta : ℕ}
    (hk : 5 ≤ k) (hkmax : k ≤ 6) (hd : delta ≤ 1)
    (hr : 0 < 2*b+delta) (hrmax : 2*b+delta ≤ k+1)
    (hn : 2*nu.card = k*(k+1)+2*(2*b+delta))
    (hR : prefixSum nu.rowLen 2 < 2*k-1)
    (hC : prefixSum nu.colLen 2 < 2*k-1) :
    Bal nu (balancePacking k b delta) := by
  obtain ⟨hsum, hpos, hlen, _⟩ := balancePacking_properties (by omega : 3 ≤ k) hd rfl hrmax hn
  obtain ⟨_, henv⟩ := profile_table hk hkmax hd hr hrmax
  have hcard : nu.card = k*(k+1)/2+2*b+delta := by omega
  have hlarge : 2*(2*k-2) ≤ nu.card := by
    interval_cases k <;> norm_num at hn ⊢ <;> omega
  have hne : 0 < nu.card := by omega
  have hfirst := first_height_of_small_two_prefixes nu hne hlarge
    (show prefixSum nu.rowLen 2 ≤ 2*k-2 by omega)
    (show prefixSum nu.colLen 2 ≤ 2*k-2 by omega)
  apply balance_of_envelope nu _ (max (k-1) (b+2)) hsum hpos
  · intro t ht
    rw [hcard]
    exact henv t ht
  · omega
  · have hc := le_max_left (k-1) (b+2)
    omega

/-- Numerical leaf for k=5,6. It uses the existing `BandGeometry` with its
four-position clearance. No representation-theoretic hypothesis occurs. -/
theorem smallK_numeric_coverage (nu : YoungDiagram) {k b r delta : ℕ}
    (hk : 5 ≤ k) (hkmax : k ≤ 6) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hpar : r%2 = delta) (hb : r = 2*b+delta)
    (hn : 2*nu.card = k*(k+1)+2*r) :
    Bal nu (balancePacking k b delta) ∨
    Bal nu.transpose (balancePacking k b delta) ∨
    BandGeometry nu (2*k-1) r delta ∨ BandGeometry nu.transpose (2*k-1) r delta := by
  classical
  subst r
  have hd : delta ≤ 1 := by omega
  have hcardT : nu.transpose.card = nu.card := by
    simp [YoungDiagram.card, YoungDiagram.transpose]
  have hnT : 2*nu.transpose.card = k*(k+1)+2*(2*b+delta) := by
    rw [hcardT]
    exact hn
  by_cases hB : Bal nu (balancePacking k b delta)
  · exact Or.inl hB
  by_cases hBt : Bal nu.transpose (balancePacking k b delta)
  · exact Or.inr (Or.inl hBt)
  have hc : ((2*b+delta : ℕ) : ℤ) ≤ parityCapacity (fun i => nu.colLen i-2) 2 delta := by
    by_contra h
    exact hB (failed22_balance nu hk hkmax hd hr hrmax hn (by omega))
  have hcT : ((2*b+delta : ℕ) : ℤ) ≤ parityCapacity (fun i => nu.transpose.colLen i-2) 2 delta := by
    by_contra h
    exact hBt (failed22_balance nu.transpose hk hkmax hd hr hrmax hnT (by omega))
  have hclear : 2*2+4 ≤ 2*k-1 := by omega
  by_cases hR : 2*k-1 ≤ prefixSum nu.rowLen 2
  · exact Or.inr (Or.inr (Or.inl (band_feasible_geometry nu hr hpar
      ⟨2, 2, by decide, by decide, by decide, by decide, hR, hclear, hc⟩)))
  · have hC : 2*k-1 ≤ prefixSum nu.colLen 2 := by
      by_contra h
      exact hB (low22_balance nu hk hkmax hd hr hrmax hn (by omega) (by omega))
    have hRT : 2*k-1 ≤ prefixSum nu.transpose.rowLen 2 := by
      simpa only [prefixSum, YoungDiagram.rowLen_transpose] using hC
    exact Or.inr (Or.inr (Or.inr (band_feasible_geometry nu.transpose hr hpar
      ⟨2, 2, by decide, by decide, by decide, by decide, hRT, hclear, hcT⟩)))

end HSTZ.SmallKCoverage

namespace HSTZ

/-- Numerical coverage for every k ≥ 5: the case k ≥ 7 is
`balancePacking_numeric_coverage`; k = 5, 6 use `smallK_numeric_coverage`. -/
theorem balancePacking_numeric_coverage_ge5 (nu : YoungDiagram) {k b delta r : ℕ}
    (hk : 5 ≤ k) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hpar : r%2=delta) (hb : r=2*b+delta)
    (hn : 2*nu.card=k*(k+1)+2*r) :
    (∀ t, prefixSum nu.colLen t ≤ youngPrefix (balancePacking k b delta) t) ∨
    (∀ t, prefixSum nu.transpose.colLen t ≤ youngPrefix (balancePacking k b delta) t) ∨
    BandGeometry nu (2*k-1) r delta ∨ BandGeometry nu.transpose (2*k-1) r delta := by
  by_cases hk7 : 7 ≤ k
  · exact balancePacking_numeric_coverage nu hk7 hr hrmax hpar hb hn
  · exact SmallKCoverage.smallK_numeric_coverage nu hk (by omega) hr hrmax hpar hb hn

end HSTZ

#print axioms HSTZ.SmallKCoverage.smallK_numeric_coverage
#print axioms HSTZ.balancePacking_numeric_coverage_ge5
