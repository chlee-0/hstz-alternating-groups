import HSTZ.YoungDiagramCompat
import HSTZ.ParityCapacity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Young-diagram area estimates used in the band-capacity argument. They depend only
on the geometry of the diagram, not on representation support. The two geometric
cases are whether the corner cell `(a-1, c-1)` lies in the diagram. -/
namespace HSTZ

private def rows (nu : YoungDiagram) (a : ℕ) :=
  nu.cells.filter (fun p => p.1 < a)

private def cols (nu : YoungDiagram) (c : ℕ) :=
  nu.cells.filter (fun p => p.2 < c)

private theorem rows_card (nu : YoungDiagram) (a : ℕ) :
    (rows nu a).card = prefixSum nu.rowLen a := by
  let hh : Antitone (capacity nu.colLen a) :=
    fun _ _ hij => min_le_min (le_refl a) (nu.colLen_antitone hij)
  have he : rows nu a = (fromColumns (capacity nu.colLen a) hh (nu.rowLen 0)).cells := by
    ext p
    rcases p with ⟨i,j⟩
    simp only [rows, Finset.mem_filter, YoungDiagram.mem_cells, mem_fromColumns, capacity,
      lt_min_iff]
    constructor
    · rintro ⟨hm,hi⟩
      exact ⟨lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp hm)
        (nu.rowLen_antitone (Nat.zero_le i)), hi, YoungDiagram.mem_iff_lt_colLen.mp hm⟩
    · rintro ⟨_,hi,hj⟩
      exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr hj,hi⟩
  rw [he, ← YoungDiagram.card, fromColumns_card, ← row_prefix_eq_capped_columns]

private theorem cols_card (nu : YoungDiagram) (c : ℕ) :
    (cols nu c).card = prefixSum nu.colLen c := by
  have he : cols nu c = (rows nu.transpose c).map (Equiv.prodComm ℕ ℕ).toEmbedding := by
    ext p
    rcases p with ⟨i,j⟩
    simp [cols,rows,YoungDiagram.mem_transpose]
  rw [he,Finset.card_map,rows_card]
  simp only [prefixSum,YoungDiagram.rowLen_transpose]

/-- A column prefix sum counts a subset of the cells. -/
theorem column_prefix_le_card (nu : YoungDiagram) (c : ℕ) :
    prefixSum nu.colLen c ≤ nu.card := by
  rw [← cols_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem prefix_last_le (nu : YoungDiagram) (a : ℕ) (ha : 0 < a) :
    a * nu.rowLen (a-1) ≤ prefixSum nu.rowLen a := by
  have hs : (∑ _i ∈ Finset.range a, nu.rowLen (a-1)) ≤
      ∑ i ∈ Finset.range a, nu.rowLen i :=
    Finset.sum_le_sum (fun i hi => nu.rowLen_antitone
      (show i ≤ a-1 by have := Finset.mem_range.mp hi; omega))
  simpa [prefixSum] using hs

/-- If the corner is missing, every cell belongs to one of the two prefixes. -/
theorem area_union_bound (nu : YoungDiagram) {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hcorner : (a-1,c-1) ∉ nu) :
    nu.card ≤ prefixSum nu.rowLen a + prefixSum nu.colLen c := by
  have hs : nu.cells ⊆ rows nu a ∪ cols nu c := by
    intro p hp
    rcases p with ⟨i,j⟩
    by_cases hi : i < a
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hi⟩)
    · have hj : j < c := by
        by_contra hj
        exact hcorner (nu.up_left_mem (by omega) (by omega) hp)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hj⟩)
  calc
    nu.card ≤ (rows nu a ∪ cols nu c).card := Finset.card_le_card hs
    _ ≤ (rows nu a).card + (cols nu c).card := Finset.card_union_le _ _
    _ = _ := by rw [rows_card,cols_card]

/-- In a nonempty diagram the covering prefixes share the origin cell. -/
theorem area_union_bound_nonempty (nu : YoungDiagram) {a c : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hne : 0 < nu.card)
    (hcorner : (a-1,c-1) ∉ nu) :
    nu.card+1 ≤ prefixSum nu.rowLen a + prefixSum nu.colLen c := by
  obtain ⟨⟨i,j⟩,hp⟩ := Finset.card_pos.mp hne
  have hzero : (0,0) ∈ nu := nu.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hp
  have hsub : nu.cells ⊆ rows nu a ∪ cols nu c := by
    intro p hp
    rcases p with ⟨i,j⟩
    by_cases hi : i < a
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hi⟩)
    · have hj : j < c := by
        by_contra hj
        exact hcorner (nu.up_left_mem (by omega) (by omega) hp)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hj⟩)
  have hinter : 0 < (rows nu a ∩ cols nu c).card := Finset.card_pos.mpr
    ⟨(0,0),Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨hzero,ha⟩,Finset.mem_filter.mpr ⟨hzero,hc⟩⟩⟩
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_add_card_inter (rows nu a) (cols nu c)
  rw [rows_card,cols_card] at hunion
  change nu.card ≤ _ at hcard
  omega

/-- Count the two prefixes, their full rectangle, and the outside tail. -/
theorem area_tail_bound (nu : YoungDiagram) {a c : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hcorner : (a-1,c-1) ∈ nu) :
    nu.card + a*c ≤ prefixSum nu.rowLen a + prefixSum nu.colLen c +
      (nu.colLen (c-1)-a)*(nu.rowLen (a-1)-c) := by
  let A := rows nu a
  let B := cols nu c
  let T := nu.cells \ (A ∪ B)
  have hi : A ∩ B = Finset.range a ×ˢ Finset.range c := by
    ext p
    rcases p with ⟨i,j⟩
    simp only [A,B,rows,cols,Finset.mem_inter,Finset.mem_filter,
      Finset.mem_product,Finset.mem_range]
    constructor
    · tauto
    · rintro ⟨hai,hcj⟩
      have hm := nu.up_left_mem (show i ≤ a-1 by omega) (show j ≤ c-1 by omega) hcorner
      exact ⟨⟨hm,hai⟩,⟨hm,hcj⟩⟩
  have hsub : A ∪ B ⊆ nu.cells := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1
  have hcount := Finset.card_sdiff_add_card_eq_card hsub
  have hunion := Finset.card_union_add_card_inter A B
  have hinter : (A ∩ B).card = a*c := by rw [hi]; simp
  have htail : T ⊆ Finset.Ico a (nu.colLen (c-1)) ×ˢ Finset.Ico c (nu.rowLen (a-1)) := by
    intro p hp
    rcases p with ⟨i,j⟩
    obtain ⟨hmem,hnot⟩ := Finset.mem_sdiff.mp hp
    have hai : a ≤ i := by
      by_contra h
      exact hnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem,by omega⟩))
    have hcj : c ≤ j := by
      by_contra h
      exact hnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem,by omega⟩))
    have hy : i < nu.colLen (c-1) := YoungDiagram.mem_iff_lt_colLen.mp
      (nu.up_left_mem (le_refl i) (by omega) hmem)
    have hx : j < nu.rowLen (a-1) := YoungDiagram.mem_iff_lt_rowLen.mp
      (nu.up_left_mem (by omega) (le_refl j) hmem)
    exact Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hai,hy⟩,Finset.mem_Ico.mpr ⟨hcj,hx⟩⟩
  have ht := Finset.card_le_card htail
  simp only [Finset.card_product,Nat.card_Ico] at ht
  rw [hinter] at hunion
  have hA : A.card = prefixSum nu.rowLen a := rows_card nu a
  have hB : B.card = prefixSum nu.colLen c := cols_card nu c
  change T.card + (A ∪ B).card = nu.card at hcount
  omega

/-- A present rectangle gives the product bound, in a form with no division. -/
theorem area_product_bound (nu : YoungDiagram) {a c R C : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hcorner : (a-1,c-1) ∈ nu)
    (hR : prefixSum nu.rowLen a ≤ R) (hC : prefixSum nu.colLen c ≤ C) :
    (nu.card : ℚ) * a * c ≤ (R : ℚ) * C := by
  have htail := area_tail_bound nu ha hc hcorner
  have hx : c ≤ nu.rowLen (a-1) := by
    have := YoungDiagram.mem_iff_lt_rowLen.mp hcorner
    omega
  have hy : a ≤ nu.colLen (c-1) := by
    have := YoungDiagram.mem_iff_lt_colLen.mp hcorner
    omega
  have hax := (prefix_last_le nu a ha).trans hR
  have hcy : c * nu.colLen (c-1) ≤ C := by
    have h := prefix_last_le nu.transpose c hc
    simp only [prefixSum,YoungDiagram.rowLen_transpose] at h
    change c * nu.colLen (c-1) ≤ prefixSum nu.colLen c at h
    exact h.trans hC
  have ht : (nu.card : ℚ) + a*c ≤ (R : ℚ)+C+
      ((nu.colLen (c-1) : ℚ)-a)*((nu.rowLen (a-1) : ℚ)-c) := by
    have hn : nu.card+a*c ≤ R+C+(nu.colLen (c-1)-a)*(nu.rowLen (a-1)-c) := by omega
    have hcast : (nu.card : ℚ)+(a : ℚ)*c ≤ (R : ℚ)+C+
        ((nu.colLen (c-1)-a : ℕ) : ℚ)*((nu.rowLen (a-1)-c : ℕ) : ℚ) := by
      exact_mod_cast hn
    simpa only [Nat.cast_sub hy,Nat.cast_sub hx] using hcast
  have hxq : (0 : ℚ) ≤ (nu.rowLen (a-1) : ℚ)-c := sub_nonneg.mpr (by exact_mod_cast hx)
  have hyq : (0 : ℚ) ≤ (nu.colLen (c-1) : ℚ)-a := sub_nonneg.mpr (by exact_mod_cast hy)
  have haxq : (a : ℚ)*nu.rowLen (a-1) ≤ R := by exact_mod_cast hax
  have hcyq : (c : ℚ)*nu.colLen (c-1) ≤ C := by exact_mod_cast hcy
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hcq : (0 : ℚ) < c := by exact_mod_cast hc
  have hmul := mul_le_mul_of_nonneg_right ht (show (0 : ℚ) ≤ a*c by positivity)
  have h1 := mul_le_mul_of_nonneg_right haxq (show (0 : ℚ) ≤ c*((nu.colLen (c-1) : ℚ)-a) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hcyq (show (0 : ℚ) ≤ (R : ℚ)-a*c by nlinarith)
  nlinarith

/-- Area bound for a finite Young diagram. -/
theorem area_bound (nu : YoungDiagram) {a c R C : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hR : prefixSum nu.rowLen a ≤ R) (hC : prefixSum nu.colLen c ≤ C) :
    (nu.card : ℚ) ≤ max ((R : ℚ)*C/((a : ℚ)*c)) ((R : ℚ)+C) := by
  by_cases hcorner : (a-1,c-1) ∈ nu
  · apply le_trans _ (le_max_left _ _)
    apply (le_div_iff₀ (show (0 : ℚ) < (a : ℚ)*c by positivity)).mpr
    simpa [mul_assoc] using area_product_bound nu ha hc hcorner hR hC
  · apply le_trans _ (le_max_right _ _)
    have hn := area_union_bound nu ha hc hcorner
    have : nu.card ≤ R+C := by omega
    exact_mod_cast this

/-- Sharpened area bound for a nonempty Young diagram. -/
theorem area_bound_nonempty (nu : YoungDiagram) {a c R C : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hne : 0 < nu.card)
    (hR : prefixSum nu.rowLen a ≤ R) (hC : prefixSum nu.colLen c ≤ C) :
    (nu.card : ℚ) ≤ max ((R : ℚ)*C/((a : ℚ)*c)) ((R : ℚ)+C-1) := by
  by_cases hcorner : (a-1,c-1) ∈ nu
  · apply le_trans _ (le_max_left _ _)
    apply (le_div_iff₀ (show (0 : ℚ) < (a : ℚ)*c by positivity)).mpr
    simpa [mul_assoc] using area_product_bound nu ha hc hcorner hR hC
  · apply le_trans _ (le_max_right _ _)
    have hn := area_union_bound_nonempty nu ha hc hne hcorner
    have hsum : nu.card+1 ≤ R+C := by omega
    have hcast : (nu.card : ℚ)+1 ≤ (R : ℚ)+C := by exact_mod_cast hsum
    linarith only [hcast]

/-- The two positive margins in the uniform k>=11 arithmetic argument. -/
theorem uniform_area_margins {n k r : ℕ} (hk : 11 ≤ k) (hr : r ≤ k+1)
    (hsize : 2*n = k*(k+1)+2*r) :
    ((r : ℚ)+19)^2/16 < (n : ℚ) ∧ 2*(r : ℚ)+38 < (n : ℚ) := by
  have hsizeq : 2*(n : ℚ) = (k : ℚ)*((k : ℚ)+1)+2*(r : ℚ) := by exact_mod_cast hsize
  have hu : (0 : ℚ) ≤ (k : ℚ)-11 := sub_nonneg.mpr (by exact_mod_cast hk)
  have hv : (0 : ℚ) ≤ (k : ℚ)+1-r := sub_nonneg.mpr (by exact_mod_cast hr)
  have hw : (0 : ℚ) ≤ (k : ℚ)+r+23 := by positivity
  have hprod := mul_nonneg hv hw
  have hsq := sq_nonneg ((k : ℚ)-11)
  have hi : 16*(n : ℚ)-((r : ℚ)+19)^2 =
      287+138*((k : ℚ)-11)+7*((k : ℚ)-11)^2+
        ((k : ℚ)+1-r)*((k : ℚ)+r+23) := by nlinarith only [hsizeq]
  have hj : 2*((n : ℚ)-2*r-38) =
      32+21*((k : ℚ)-11)+((k : ℚ)-11)^2+2*((k : ℚ)+1-r) := by
    nlinarith only [hsizeq]
  constructor
  · nlinarith only [hi,hu,hsq,hprod]
  · nlinarith only [hj,hu,hsq,hv]

/-- At k>=11 at least one q=4 band capacity succeeds. This is combinatorics,
not a claim that its attachment contributes a representation constituent. -/
theorem uniform_capacity_success (nu : YoungDiagram) {k r d e delta : ℕ}
    (hk : 11 ≤ k) (hr : r ≤ k+1) (hpar : r%2 = delta)
    (hsize : 2*nu.card = k*(k+1)+2*r) (hd : d ≤ 4) (he : e ≤ 4) :
    (r : ℤ) ≤ parityCapacity (fun i => nu.colLen i-d) 4 delta ∨
      (r : ℤ) ≤ parityCapacity (fun i => nu.rowLen i-e) 4 delta := by
  by_contra h
  obtain ⟨hcol,hrow⟩ := not_or.mp h
  have hC := failed_capacity_prefix hpar (lt_of_not_ge hcol)
  have hR := failed_capacity_prefix hpar (lt_of_not_ge hrow)
  have hC' : prefixSum nu.colLen 4 ≤ r+19 := by omega
  have hR' : prefixSum nu.rowLen 4 ≤ r+19 := by omega
  have hab := area_bound nu (by omega : 0 < 4) (by omega : 0 < 4) hR' hC'
  have hm := uniform_area_margins hk hr hsize
  have hmax : max (((r : ℚ)+19)^2/16) (2*(r : ℚ)+38) < (nu.card : ℚ) :=
    max_lt hm.1 hm.2
  have hfinal : (nu.card : ℚ) ≤ max (((r : ℚ)+19)^2/16) (2*(r : ℚ)+38) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,pow_two,
      show (4 : ℚ)*4 = 16 by norm_num,
      show (r : ℚ)+19+((r : ℚ)+19) = 2*(r : ℚ)+38 by ring] using hab
  exact (not_lt_of_ge hfinal) hmax

/-- Outside both four-prefix balance conditions, take fixed depth d = q = 4:
a contained band target exists in one orientation. -/
theorem uniform_band_target (nu : YoungDiagram) {k r delta : ℕ}
    (hk : 11 ≤ k) (hr : 0 < r) (hrmax : r ≤ k+1) (hpar : r%2 = delta)
    (hsize : 2*nu.card = k*(k+1)+2*r)
    (hrows : 2*k-1 ≤ prefixSum nu.rowLen 4)
    (hcols : 2*k-1 ≤ prefixSum nu.colLen 4) :
    ∃ tau : YoungDiagram, (tau = nu ∨ tau = nu.transpose) ∧
      ∃ (f : ℕ → ℕ) (t : ℕ),
        Antitone f ∧ ColumnParity f delta ∧ 0 < t ∧ t ≤ 4 ∧ t ≤ tau.rowLen 0 ∧
        (∀ i < t, 0 < f i ∧ 4+f i ≤ tau.colLen i) ∧
        (∀ i, t ≤ i → f i = 0) ∧ prefixSum f (tau.rowLen 0) = r ∧
        ∃ pi theta : YoungDiagram,
          pi.card = 2*k-1 ∧ theta.card = 2*k-1+r ∧ theta ≤ tau ∧
          (∀ i < t, pi.colLen i = 4) ∧
          (∀ i < tau.rowLen 0, pi.colLen i ≤ 4 ∧ theta.colLen i = pi.colLen i+f i) := by
  rcases uniform_capacity_success nu hk hrmax hpar hsize
      (le_refl 4) (le_refl 4) with hb | hb
  · refine ⟨nu,Or.inl rfl, ?_⟩
    exact band_contained_target nu hr hpar hb hrows (by omega)
  · refine ⟨nu.transpose,Or.inr rfl, ?_⟩
    apply band_contained_target nu.transpose hr hpar
    · simpa only [YoungDiagram.colLen_transpose] using hb
    · simpa only [prefixSum,YoungDiagram.rowLen_transpose] using hcols
    · omega

end HSTZ
#print axioms HSTZ.area_union_bound
#print axioms HSTZ.area_product_bound
#print axioms HSTZ.area_bound
#print axioms HSTZ.area_union_bound_nonempty
#print axioms HSTZ.area_bound_nonempty
#print axioms HSTZ.uniform_area_margins
#print axioms HSTZ.uniform_capacity_success
#print axioms HSTZ.uniform_band_target
