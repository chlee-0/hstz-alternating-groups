import HSTZ.YoungDiagramCompat
import HSTZ.AreaBound
import Mathlib.Tactic.IntervalCases

/-! Boundary geometry for 7 ≤ k ≤ 10: outside the balance region a target diagram
admits a guarded band in one orientation, unless it is the 6 by 6 square (k = 7, r = 8).
This is purely combinatorial; no representation support is assumed or concluded. -/
namespace HSTZ

/-- The sole equality diagram in the reduced boundary argument. -/
def squareSix : YoungDiagram := fromColumns (fun _ => 6) antitone_const 6

@[simp] theorem mem_squareSix (i j : ℕ) : (i,j) ∈ squareSix ↔ i < 6 ∧ j < 6 := by
  erw [squareSix,mem_fromColumns]
  exact and_comm

@[simp] theorem squareSix_card : squareSix.card = 36 := by
  erw [squareSix,fromColumns_card]
  norm_num [prefixSum]

@[simp] theorem squareSix_transpose : squareSix.transpose = squareSix := by
  apply SetLike.ext
  rintro ⟨i,j⟩
  simp only [YoungDiagram.mem_transpose,Prod.swap_prod_mk,mem_squareSix]
  exact and_comm

/-- Area 36 and the two sharp prefix bounds force the 6 by 6 square. -/
theorem square_six_of_prefix_bounds (nu : YoungDiagram) (hn : nu.card = 36)
    (hR : prefixSum nu.rowLen 2 ≤ 12) (hC : prefixSum nu.colLen 3 ≤ 18) :
    nu = squareSix := by
  have hc : (1,2) ∈ nu := by
    by_contra h
    have hs := area_union_bound nu (by omega : 0 < 2) (by omega : 0 < 3) h
    omega
  have hx := (prefix_last_le nu 2 (by omega)).trans hR
  change 2*nu.rowLen 1 ≤ 12 at hx
  have hy := prefix_last_le nu.transpose 3 (by omega)
  simp only [prefixSum,YoungDiagram.rowLen_transpose] at hy
  change 3*nu.colLen 2 ≤ prefixSum nu.colLen 3 at hy
  have hy' := hy.trans hC
  have ht := area_tail_bound nu (by omega : 0 < 2) (by omega : 0 < 3) hc
  change nu.card+6 ≤ prefixSum nu.rowLen 2+prefixSum nu.colLen 3+
    (nu.colLen 2-2)*(nu.rowLen 1-3) at ht
  have hx' : nu.rowLen 1 ≤ 6 := by omega
  have hy'' : nu.colLen 2 ≤ 6 := by omega
  have hp := Nat.mul_le_mul_right (nu.rowLen 1-3) (show nu.colLen 2-2 ≤ 4 by omega)
  have hq := Nat.mul_le_mul_left (nu.colLen 2-2) (show nu.rowLen 1-3 ≤ 3 by omega)
  have hxeq : nu.rowLen 1 = 6 := by omega
  have hyeq : nu.colLen 2 = 6 := by omega
  have hr0 : nu.rowLen 0 ≤ 6 := by
    simp only [prefixSum,Finset.sum_range_succ,Finset.sum_range_zero] at hR
    omega
  have hc0 : nu.colLen 0 ≤ 6 := by
    have hanti := nu.colLen_anti 1 2 (by omega)
    simp only [prefixSum,Finset.sum_range_succ,Finset.sum_range_zero] at hC
    omega
  have hsub : nu.cells ⊆ squareSix.cells := by
    intro p hp
    rcases p with ⟨i,j⟩
    apply (mem_squareSix i j).mpr
    exact ⟨lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp hp)
        ((nu.colLen_anti 0 j (Nat.zero_le j)).trans hc0),
      lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp hp)
        ((nu.rowLen_anti 0 i (Nat.zero_le i)).trans hr0)⟩
  have heq : nu.cells = squareSix.cells := Finset.eq_of_subset_of_card_le hsub (by
    change squareSix.card ≤ nu.card
    rw [squareSix_card,hn])
  apply SetLike.ext
  intro p
  change p ∈ nu.cells ↔ p ∈ squareSix.cells
  rw [heq]

/-- Young's column-prefix function; part-list sorting is unnecessary. -/
def youngPrefix (A : List ℕ) (t : ℕ) : ℕ := (A.map (fun a => min t a)).sum

/-- The source balance list at k=7,r=8, kept in its displayed order. -/
def squareBalanceParts : List ℕ := [6,5,4,3,3,3,3,3,2,2,2]

theorem squareSix_colLen_of_lt {j : ℕ} (hj : j < 6) : squareSix.colLen j = 6 :=
  fromColumns_colLen _ _ hj

/-- The equality diagram satisfies every Young inequality for the explicit
balance list. This is a numerical dominance statement; it transfers no support. -/
theorem squareSix_young_prefix (t : ℕ) :
    prefixSum squareSix.colLen t ≤ youngPrefix squareBalanceParts t := by
  by_cases ht : t < 6
  · interval_cases t <;>
      norm_num [prefixSum,Finset.sum_range_succ,squareSix_colLen_of_lt,youngPrefix,squareBalanceParts]
  · have hs : youngPrefix squareBalanceParts t = 36 := by
      simp [youngPrefix,squareBalanceParts,
        Nat.min_eq_right (show 6 ≤ t by omega),Nat.min_eq_right (show 5 ≤ t by omega),
        Nat.min_eq_right (show 4 ≤ t by omega),Nat.min_eq_right (show 3 ≤ t by omega),
        Nat.min_eq_right (show 2 ≤ t by omega)]
    rw [hs]
    exact (column_prefix_le_card squareSix t).trans_eq squareSix_card

/-- Test only depths 2,3,4; a predecessor bound is needed only at 3 and 4. -/
theorem choose_boundary_depth (f : ℕ → ℕ) {K : ℕ} (hfour : K ≤ prefixSum f 4) :
    ∃ d, 2 ≤ d ∧ d ≤ 4 ∧ K ≤ prefixSum f d ∧
      (3 ≤ d → prefixSum f (d-1) < K) := by
  by_cases htwo : K ≤ prefixSum f 2
  · exact ⟨2,by omega,by omega,htwo,by omega⟩
  · by_cases hthree : K ≤ prefixSum f 3
    · exact ⟨3,by omega,by omega,hthree,by intro _; change prefixSum f 2 < K; omega⟩
    · exact ⟨4,by omega,by omega,hfour,by intro _; change prefixSum f 3 < K; omega⟩

private theorem margin_33 {n k r : ℕ} (hk : 7 ≤ k) (hkmax : k ≤ 10)
    (hr : 0 < r) (hrmax : r ≤ k+1) (hn : 2*n = k*(k+1)+2*r) :
    ((2*(k : ℚ)-2)^2/9 < (n : ℚ)) ∧ (4*(k : ℚ)-5 < (n : ℚ)) := by
  have hnq : 2*(n : ℚ) = (k : ℚ)*((k : ℚ)+1)+2*r := by exact_mod_cast hn
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  interval_cases k <;> simp only [Nat.cast_ofNat] at hnq ⊢ <;>
    constructor <;> nlinarith only [hnq,hrq]

private theorem margin_23 {n k r : ℕ} (hk : 7 ≤ k) (hkmax : k ≤ 10)
    (hr : 0 < r) (hrmax : r ≤ k+1) (hn : 2*n = k*(k+1)+2*r)
    (hexc : k ≠ 7 ∨ r ≠ 8) :
    ((2*(k : ℚ)-2)*((r : ℚ)+10)/6 < (n : ℚ)) ∧
      (2*(k : ℚ)+(r : ℚ)+7 < (n : ℚ)) := by
  have hnq : 2*(n : ℚ) = (k : ℚ)*((k : ℚ)+1)+2*r := by exact_mod_cast hn
  have hrq : (r : ℚ) ≤ (k : ℚ)+1 := by exact_mod_cast hrmax
  have hexq : k=7 → (r : ℚ) ≤ 7 := by
    intro heq
    exact_mod_cast (show r ≤ 7 by omega)
  interval_cases k
  · have hb := hexq rfl
    simp only [Nat.cast_ofNat] at hnq hrq ⊢
    constructor <;> nlinarith only [hnq,hrq,hb]
  all_goals simp only [Nat.cast_ofNat] at hnq hrq ⊢
  all_goals constructor <;> nlinarith only [hnq,hrq]

private theorem margin_44 {n k r : ℕ} (hk : 7 ≤ k) (hkmax : k ≤ 10)
    (hr : 0 < r) (hrmax : r ≤ k+1) (hn : 2*n = k*(k+1)+2*r) :
    (((r : ℚ)+10)^2/16 < (n : ℚ)) ∧ (2*(r : ℚ)+19 < (n : ℚ)) := by
  have hnq : 2*(n : ℚ) = (k : ℚ)*((k : ℚ)+1)+2*r := by exact_mod_cast hn
  have hrq : (r : ℚ) ≤ (k : ℚ)+1 := by exact_mod_cast hrmax
  have hp : (0 : ℚ) ≤ ((k : ℚ)+1-r)*((k : ℚ)+r+5) :=
    mul_nonneg (sub_nonneg.mpr hrq) (by positivity)
  interval_cases k <;> simp only [Nat.cast_ofNat] at hnq hrq hp ⊢ <;> constructor <;>
    nlinarith only [hnq,hrq,hp]

private theorem margin_32 {n k r : ℕ} (hk : 7 ≤ k) (hkmax : k ≤ 10)
    (_hr : 0 < r) (hrmax : r ≤ k+1) (hn : 2*n = k*(k+1)+2*r) :
    (((r : ℚ)+8)*(2*(k : ℚ)-2)/6 < (n : ℚ)) ∧
      (2*(k : ℚ)+(r : ℚ)+5 < (n : ℚ)) := by
  have hnq : 2*(n : ℚ) = (k : ℚ)*((k : ℚ)+1)+2*r := by exact_mod_cast hn
  have hrq : (r : ℚ) ≤ (k : ℚ)+1 := by exact_mod_cast hrmax
  interval_cases k <;> simp only [Nat.cast_ofNat] at hnq hrq ⊢ <;> constructor <;>
    nlinarith only [hnq,hrq]

private theorem area_impossible (nu : YoungDiagram) {a c R C : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hne : 0 < nu.card)
    (hR : prefixSum nu.rowLen a ≤ R) (hC : prefixSum nu.colLen c ≤ C)
    (hp : (R : ℚ)*C/((a : ℚ)*c) < (nu.card : ℚ))
    (hu : (R : ℚ)+C-1 < (nu.card : ℚ)) : False :=
  (not_lt_of_ge (area_bound_nonempty nu ha hc hne hR hC)) (max_lt hp hu)

private theorem case_33 (nu : YoungDiagram) {k r : ℕ}
    (hk : 7 ≤ k) (hkmax : k ≤ 10) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hn : 2*nu.card = k*(k+1)+2*r)
    (hR : prefixSum nu.rowLen 3 ≤ 2*k-2) (hC : prefixSum nu.colLen 3 ≤ 2*k-2) : False := by
  have hm := margin_33 hk hkmax hr hrmax hn
  have hs : 2 ≤ 2*k := by omega
  apply area_impossible nu (by omega : 0 < 3) (by omega : 0 < 3) (by nlinarith) hR hC
  · simpa only [Nat.cast_sub hs,Nat.cast_mul,Nat.cast_ofNat,pow_two,
      show (3 : ℚ)*3 = 9 by norm_num] using hm.1
  · convert hm.2 using 1
    push_cast [Nat.cast_sub hs]
    ring

private theorem case_23 (nu : YoungDiagram) {k r : ℕ}
    (hk : 7 ≤ k) (hkmax : k ≤ 10) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hn : 2*nu.card = k*(k+1)+2*r)
    (hR : prefixSum nu.rowLen 2 ≤ 2*k-2) (hC : prefixSum nu.colLen 3 ≤ r+10) :
    nu = squareSix := by
  by_cases hexc : k ≠ 7 ∨ r ≠ 8
  · have hm := margin_23 hk hkmax hr hrmax hn hexc
    have hs : 2 ≤ 2*k := by omega
    apply False.elim
    apply area_impossible nu (by omega : 0 < 2) (by omega : 0 < 3) (by nlinarith) hR hC
    · simpa only [Nat.cast_sub hs,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,
        show (2 : ℚ)*3 = 6 by norm_num] using hm.1
    · convert hm.2 using 1
      push_cast [Nat.cast_sub hs]
      ring
  · have hk7 : k=7 := by tauto
    have hr8 : r=8 := by tauto
    apply square_six_of_prefix_bounds nu
    · rw [hk7,hr8] at hn; omega
    · simpa only [hk7] using hR
    · simpa only [hr8] using hC

private theorem case_44 (nu : YoungDiagram) {k r : ℕ}
    (hk : 7 ≤ k) (hkmax : k ≤ 10) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hn : 2*nu.card = k*(k+1)+2*r)
    (hR : prefixSum nu.rowLen 4 ≤ r+10) (hC : prefixSum nu.colLen 4 ≤ r+10) : False := by
  have hm := margin_44 hk hkmax hr hrmax hn
  apply area_impossible nu (by omega : 0 < 4) (by omega : 0 < 4) (by nlinarith) hR hC
  · simpa only [Nat.cast_add,Nat.cast_ofNat,pow_two,
      show (4 : ℚ)*4 = 16 by norm_num] using hm.1
  · convert hm.2 using 1
    push_cast
    ring

private theorem case_32 (nu : YoungDiagram) {k r : ℕ}
    (hk : 7 ≤ k) (hkmax : k ≤ 10) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hn : 2*nu.card = k*(k+1)+2*r)
    (hR : prefixSum nu.rowLen 2 ≤ r+8) (hC : prefixSum nu.colLen 3 ≤ 2*k-2) : False := by
  have hm := margin_32 hk hkmax hr hrmax hn
  have hs : 2 ≤ 2*k := by omega
  apply area_impossible nu (by omega : 0 < 2) (by omega : 0 < 3) (by nlinarith) hR hC
  · simpa only [Nat.cast_sub hs,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,
      show (2 : ℚ)*3 = 6 by norm_num] using hm.1
  · convert hm.2 using 1
    push_cast [Nat.cast_sub hs]
    ring

/-- Legal boundary tests, with depths 2,3,4 and q=2,3,4. -/
def BandFeasible (nu : YoungDiagram) (K r delta : ℕ) : Prop :=
  ∃ d q, 2 ≤ d ∧ d ≤ 4 ∧ 2 ≤ q ∧ q ≤ 4 ∧ K ≤ prefixSum nu.rowLen d ∧
    d*q+4 ≤ K ∧ (r : ℤ) ≤ parityCapacity (fun i => nu.colLen i-d) q delta

private theorem failure_at_depth (nu : YoungDiagram) {K r delta d q : ℕ}
    (hno : ¬ BandFeasible nu K r delta) (hpar : r%2=delta)
    (hd : 2 ≤ d) (hd4 : d ≤ 4) (hq : 2 ≤ q) (hq4 : q ≤ 4)
    (hrows : K ≤ prefixSum nu.rowLen d) (hclear : d*q+4 ≤ K) :
    prefixSum nu.colLen q+2+delta ≤ q*d+r+q := by
  apply failed_capacity_prefix_sharp hq hpar
  exact lt_of_not_ge (fun hb => hno ⟨d,q,hd,hd4,hq,hq4,hrows,hclear,hb⟩)

/-- The four boundary cases force a guarded band in one orientation,
unless the target is the single square equality diagram. -/
theorem boundary_capacity_or_square (nu : YoungDiagram) {k r delta : ℕ}
    (hk : 7 ≤ k) (hkmax : k ≤ 10) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hpar : r%2=delta) (hn : 2*nu.card = k*(k+1)+2*r)
    (hrows : 2*k-1 ≤ prefixSum nu.rowLen 4)
    (hcols : 2*k-1 ≤ prefixSum nu.colLen 4) :
    BandFeasible nu (2*k-1) r delta ∨
      BandFeasible nu.transpose (2*k-1) r delta ∨ nu = squareSix := by
  by_cases hb : BandFeasible nu (2*k-1) r delta
  · exact Or.inl hb
  by_cases hbt : BandFeasible nu.transpose (2*k-1) r delta
  · exact Or.inr (Or.inl hbt)
  refine Or.inr (Or.inr ?_)
  obtain ⟨d,hd,hd4,hRd,hRprev⟩ := choose_boundary_depth nu.rowLen hrows
  obtain ⟨e,he,he4,hCe,hCprev⟩ := choose_boundary_depth nu.colLen hcols
  have hCet : 2*k-1 ≤ prefixSum nu.transpose.rowLen e := by
    simpa only [prefixSum,YoungDiagram.rowLen_transpose] using hCe
  have hnt : 2*nu.transpose.card = k*(k+1)+2*r := by
    simpa [YoungDiagram.card,YoungDiagram.transpose] using hn
  have F (q : ℕ) (hq : 2 ≤ q) (hq4 : q ≤ 4) (hclear : d*q+4 ≤ 2*k-1) :=
    failure_at_depth nu hb hpar hd hd4 hq hq4 hRd hclear
  have Ft (q : ℕ) (hq : 2 ≤ q) (hq4 : q ≤ 4) (hclear : e*q+4 ≤ 2*k-1) :
      prefixSum nu.rowLen q+2+delta ≤ q*e+r+q := by
    simpa only [prefixSum,YoungDiagram.colLen_transpose] using
      failure_at_depth nu.transpose hbt hpar he he4 hq hq4 hCet hclear
  by_cases hd3 : d=3
  · have hc3 := F 3 (by omega) (by omega) (by omega)
    have hp := hRprev (by omega)
    apply case_23 nu hk hkmax hr hrmax hn
    · simpa only [hd3] using (show prefixSum nu.rowLen (d-1) ≤ 2*k-2 by omega)
    · omega
  by_cases he3 : e=3
  · have hr3 := Ft 3 (by omega) (by omega) (by omega)
    have hp := hCprev (by omega)
    have hs : nu.transpose = squareSix := by
      apply case_23 nu.transpose hk hkmax hr hrmax hnt
      · simp only [prefixSum,YoungDiagram.rowLen_transpose]
        change prefixSum nu.colLen 2 ≤ 2*k-2
        have hprev : prefixSum nu.colLen (e-1) ≤ 2*k-2 := by omega
        simpa only [he3] using hprev
      · simp only [prefixSum,YoungDiagram.colLen_transpose]
        change prefixSum nu.rowLen 3 ≤ r+10
        omega
    have hs' := congrArg YoungDiagram.transpose hs
    simpa using hs'
  by_cases hd4eq : d=4
  · by_cases he4eq : e=4
    · have hRp := hRprev (by omega)
      have hCp := hCprev (by omega)
      apply False.elim
      apply case_33 nu hk hkmax hr hrmax hn
      · have hh : prefixSum nu.rowLen (d-1) ≤ 2*k-2 := by omega
        simpa only [hd4eq] using hh
      · have hh : prefixSum nu.colLen (e-1) ≤ 2*k-2 := by omega
        simpa only [he4eq] using hh
    · have hc2 := F 2 (by omega) (by omega) (by omega)
      have hRp := hRprev (by omega)
      apply False.elim
      apply case_32 nu.transpose hk hkmax hr hrmax hnt
      · simp only [prefixSum,YoungDiagram.rowLen_transpose]
        change prefixSum nu.colLen 2 ≤ r+8
        omega
      · simp only [prefixSum,YoungDiagram.colLen_transpose]
        change prefixSum nu.rowLen 3 ≤ 2*k-2
        have hh : prefixSum nu.rowLen (d-1) ≤ 2*k-2 := by omega
        simpa only [hd4eq] using hh
  · by_cases he4eq : e=4
    · have hr2 := Ft 2 (by omega) (by omega) (by omega)
      have hCp := hCprev (by omega)
      apply False.elim
      apply case_32 nu hk hkmax hr hrmax hn
      · omega
      · have hh : prefixSum nu.colLen (e-1) ≤ 2*k-2 := by omega
        simpa only [he4eq] using hh
    · have hc4 := F 4 (by omega) (by omega) (by omega)
      have hr4 := Ft 4 (by omega) (by omega) (by omega)
      exact False.elim (case_44 nu hk hkmax hr hrmax hn (by omega) (by omega))

/-- Guarded target data; purely geometric, separate from any representation constituent. -/
def BandGeometry (nu : YoungDiagram) (K r delta : ℕ) : Prop :=
  ∃ d q, 2 ≤ d ∧ d ≤ 4 ∧ 2 ≤ q ∧ q ≤ 4 ∧ d*q+4 ≤ K ∧
    ∃ (f : ℕ → ℕ) (t : ℕ),
      Antitone f ∧ ColumnParity f delta ∧ 0 < t ∧ t ≤ q ∧ t ≤ nu.rowLen 0 ∧
      (∀ i < t, 0 < f i ∧ d+f i ≤ nu.colLen i) ∧
      (∀ i, t ≤ i → f i = 0) ∧ prefixSum f (nu.rowLen 0) = r ∧
      ∃ pi theta : YoungDiagram,
        pi.card = K ∧ theta.card = K+r ∧ theta ≤ nu ∧
        (∀ i < t, pi.colLen i = d) ∧
        (∀ i < nu.rowLen 0, pi.colLen i ≤ d ∧ theta.colLen i = pi.colLen i+f i)

theorem band_feasible_geometry (nu : YoungDiagram) {K r delta : ℕ}
    (hr : 0 < r) (hpar : r%2=delta) (hb : BandFeasible nu K r delta) :
    BandGeometry nu K r delta := by
  obtain ⟨d,q,hd,hd4,hq,hq4,hrows,hclear,hcap⟩ := hb
  exact ⟨d,q,hd,hd4,hq,hq4,hclear,band_contained_target nu hr hpar hcap hrows hclear⟩

theorem square_exception_parameters (nu : YoungDiagram) {k r : ℕ}
    (hk : 7 ≤ k) (hr : 0 < r) (hn : 2*nu.card = k*(k+1)+2*r)
    (hsq : nu = squareSix) : k=7 ∧ r=8 := by
  rw [hsq,squareSix_card] at hn
  have hkup : k ≤ 7 := by
    by_contra h
    have hk8 : 8 ≤ k := by omega
    have hp := Nat.mul_le_mul hk8 (show 9 ≤ k+1 by omega)
    omega
  have hk7 : k=7 := by omega
  exact ⟨hk7,by rw [hk7] at hn; omega⟩

/-- Boundary assembly for 7 ≤ k ≤ 10, with the square as the unique equality exception. -/
theorem boundary_band_or_square (nu : YoungDiagram) {k r delta : ℕ}
    (hk : 7 ≤ k) (hkmax : k ≤ 10) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hpar : r%2=delta) (hn : 2*nu.card = k*(k+1)+2*r)
    (hrows : 2*k-1 ≤ prefixSum nu.rowLen 4)
    (hcols : 2*k-1 ≤ prefixSum nu.colLen 4) :
    BandGeometry nu (2*k-1) r delta ∨ BandGeometry nu.transpose (2*k-1) r delta ∨
      (nu = squareSix ∧ k=7 ∧ r=8) := by
  rcases boundary_capacity_or_square nu hk hkmax hr hrmax hpar hn hrows hcols with hb | hb | hs
  · exact Or.inl (band_feasible_geometry nu hr hpar hb)
  · exact Or.inr (Or.inl (band_feasible_geometry nu.transpose hr hpar hb))
  · exact Or.inr (Or.inr ⟨hs,square_exception_parameters nu hk hr hn hs⟩)

/-- The full outside-balance geometry for k ≥ 7. The k ≥ 11 branch uses
depth four directly; only the bounded branch uses the prefix tests. -/
theorem large_degree_band_or_square (nu : YoungDiagram) {k r delta : ℕ}
    (hk : 7 ≤ k) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hpar : r%2=delta) (hn : 2*nu.card = k*(k+1)+2*r)
    (hrows : 2*k-1 ≤ prefixSum nu.rowLen 4)
    (hcols : 2*k-1 ≤ prefixSum nu.colLen 4) :
    BandGeometry nu (2*k-1) r delta ∨ BandGeometry nu.transpose (2*k-1) r delta ∨
      (nu = squareSix ∧ k=7 ∧ r=8) := by
  by_cases hk11 : 11 ≤ k
  · rcases uniform_capacity_success nu hk11 hrmax hpar hn (le_refl 4) (le_refl 4) with hb | hb
    · apply Or.inl
      apply band_feasible_geometry nu hr hpar
      exact ⟨4,4,by omega,by omega,by omega,by omega,hrows,by omega,hb⟩
    · apply Or.inr ∘ Or.inl
      apply band_feasible_geometry nu.transpose hr hpar
      refine ⟨4,4,by omega,by omega,by omega,by omega, ?_,by omega, ?_⟩
      · simpa only [prefixSum,YoungDiagram.rowLen_transpose] using hcols
      · simpa only [YoungDiagram.colLen_transpose] using hb
  · exact boundary_band_or_square nu hk (by omega) hr hrmax hpar hn hrows hcols

end HSTZ
#print axioms HSTZ.square_six_of_prefix_bounds
#print axioms HSTZ.squareSix_young_prefix
#print axioms HSTZ.choose_boundary_depth
#print axioms HSTZ.boundary_capacity_or_square
#print axioms HSTZ.band_feasible_geometry
#print axioms HSTZ.square_exception_parameters
#print axioms HSTZ.boundary_band_or_square
#print axioms HSTZ.large_degree_band_or_square
