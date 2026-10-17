import HSTZ.YoungDiagramCompat
import HSTZ.ContainedTarget
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Parity-capacity selection by an ordered construction that does not sort after selecting.
This module proves only combinatorial statements.
-/
namespace HSTZ
open scoped BigOperators

/-- All columns even, or exactly one odd column, according to δ. -/
def ColumnParity (e : ℕ → ℕ) (delta : ℕ) : Prop :=
  if delta = 0 then ∀ i, e i % 2 = 0
  else ∃ j, e j % 2 = 1 ∧ ∀ i, i ≠ j → e i % 2 = 0

/-- Signed capacity; −1 really denotes the empty feasible odd case. -/
noncomputable def parityCapacity (a : ℕ → ℕ) (q delta : ℕ) : ℤ := by
  classical
  let P := prefixSum (fun i => a i / 2) q
  exact if delta = 0 then 2*(P : ℤ)
    else if ∃ j < q, a j % 2 = 1 then 2*(P : ℤ)+1 else 2*(P : ℤ)-1

private theorem half_antitone {a : ℕ → ℕ} (ha : Antitone a) :
    Antitone (fun i => a i / 2) := fun _ _ hij => Nat.div_le_div_right (ha hij)

private theorem half_capacity {a : ℕ → ℕ} (ha : Antitone a) :
    capacity (fun i => a i / 2) (a 0 / 2) = (fun i => a i / 2) := by
  funext i
  exact Nat.min_eq_right (half_antitone ha (Nat.zero_le i))

/-- Ordered even fill with b pairs, supported where that total is exhausted. -/
def evenFill (a : ℕ → ℕ) (b i : ℕ) : ℕ :=
  2 * greedy (fun j => a j / 2) (a 0 / 2) b i

private theorem evenFill_antitone {a : ℕ → ℕ} (ha : Antitone a) (b : ℕ) :
    Antitone (evenFill a b) := by
  intro i j hij
  exact Nat.mul_le_mul_left 2 (greedy_antitone (half_antitone ha) _ _ hij)

private theorem evenFill_le (a : ℕ → ℕ) (b i : ℕ) : evenFill a b i ≤ a i := by
  have hg := greedy_le_height (fun j => a j / 2) (a 0 / 2) b i
  dsimp [evenFill]
  omega

private theorem evenFill_even (a : ℕ → ℕ) (b i : ℕ) : evenFill a b i % 2 = 0 := by
  dsimp [evenFill]
  omega

private theorem evenFill_sum {a : ℕ → ℕ} (ha : Antitone a) (b q : ℕ)
    (hb : b ≤ prefixSum (fun i => a i / 2) q) :
    prefixSum (evenFill a b) q = 2*b := by
  unfold prefixSum evenFill
  rw [← Finset.mul_sum]
  change 2 * prefixSum (greedy (fun j => a j / 2) (a 0 / 2) b) q = 2*b
  rw [prefix_greedy, half_capacity ha, Nat.min_eq_left hb]

private theorem evenFill_zero {a : ℕ → ℕ} (ha : Antitone a) (b q : ℕ)
    (hb : b ≤ prefixSum (fun i => a i / 2) q) (i : ℕ) (hi : q ≤ i) :
    evenFill a b i = 0 := by
  have hp := prefix_mono (fun j => a j / 2) hi
  dsimp [evenFill, greedy]
  rw [half_capacity ha]
  have hz : b - prefixSum (fun j => a j / 2) i = 0 := by omega
  rw [hz]
  simp

private theorem evenFill_full {a : ℕ → ℕ} (ha : Antitone a) (q i : ℕ) (hi : i < q) :
    evenFill a (prefixSum (fun j => a j / 2) q) i = 2*(a i / 2) := by
  have hp := prefix_mono (fun j => a j / 2) (Nat.succ_le_of_lt hi)
  rw [prefix_succ] at hp
  change prefixSum (fun j => a j / 2) i + a i / 2 ≤ prefixSum (fun j => a j / 2) q at hp
  have hm : a i / 2 ≤ prefixSum (fun j => a j / 2) q - prefixSum (fun j => a j / 2) i := by omega
  dsimp [evenFill, greedy]
  rw [half_capacity ha]
  rw [Nat.min_eq_left hm]

/-- Extract the positive-column count without sorting or losing zeros. -/
theorem positive_prefix {e : ℕ → ℕ} (he : Antitone e) {q : ℕ}
    (hzero : ∀ i, q ≤ i → e i = 0) :
    ∃ t ≤ q, (∀ i < t, 0 < e i) ∧ (∀ i, t ≤ i → e i = 0) := by
  let hex : ∃ i, e i = 0 := ⟨q,hzero q (le_refl q)⟩
  let t := Nat.find hex
  refine ⟨t, Nat.find_min' hex (hzero q (le_refl q)), ?_, ?_⟩
  · intro i hi
    have hn := Nat.find_min hex hi
    omega
  · intro i hi
    have hz : e t = 0 := Nat.find_spec hex
    have hl := he hi
    omega

private theorem prefix_after_zero {e : ℕ → ℕ} {t : ℕ}
    (hzero : ∀ i, t ≤ i → e i = 0) (n : ℕ) (hn : t ≤ n) :
    prefixSum e n = prefixSum e t := by
  induction n with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    rfl
  | succ n ih =>
    by_cases ht : t ≤ n
    · rw [prefix_succ, ih ht, hzero n ht, Nat.add_zero]
    · have ht : t = n+1 := by omega
      rw [ht]

private def trimLast (v : ℕ → ℕ) (j i : ℕ) : ℕ := v i - if i = j then 1 else 0

private theorem trimLast_antitone {v : ℕ → ℕ} (hv : Antitone v) (j : ℕ)
    (hlast : ∀ i, j < i → v i = 0) : Antitone (trimLast v j) := by
  intro i k hik
  by_cases hi : i = j
  · subst i
    by_cases hk : k = j
    · subst k; rfl
    · have hz := hlast k (by omega)
      simp [trimLast,hk,hz]
  · by_cases hk : k = j
    · subst k
      have hh := hv hik
      simp only [trimLast,if_neg hi,Nat.sub_zero]
      omega
    · simpa [trimLast,hi,hk] using hv hik

private theorem trimLast_sum {v : ℕ → ℕ} {j q : ℕ} (hj : j < q) (hpos : 0 < v j) :
    prefixSum (trimLast v j) q + 1 = prefixSum v q := by
  have hpoint (i : ℕ) : trimLast v j i + (if i = j then 1 else 0) = v i := by
    by_cases hi : i = j
    · subst i
      simp [trimLast]
      omega
    · simp [trimLast,hi]
  have hs := congrArg (fun f : ℕ → ℕ => prefixSum f q) (funext hpoint)
  simpa [prefixSum,Finset.sum_add_distrib,hj] using hs

private theorem select_even {a : ℕ → ℕ} (ha : Antitone a) {q r : ℕ}
    (hpar : r % 2 = 0) (hbound : r ≤ 2*prefixSum (fun i => a i / 2) q) :
    ∃ e, Antitone e ∧ (∀ i, e i ≤ a i) ∧ (∀ i, q ≤ i → e i = 0) ∧
      prefixSum e q = r ∧ ColumnParity e 0 := by
  have hb : r/2 ≤ prefixSum (fun i => a i / 2) q := by omega
  refine ⟨evenFill a (r/2),evenFill_antitone ha _,evenFill_le a _,
    evenFill_zero ha _ q hb, ?_, ?_⟩
  · rw [evenFill_sum ha _ q hb]; omega
  · simpa [ColumnParity] using evenFill_even a (r/2)

private theorem select_odd_interior {a : ℕ → ℕ} (ha : Antitone a) {q r : ℕ}
    (hpar : r % 2 = 1) (hbound : r+1 ≤ 2*prefixSum (fun i => a i / 2) q) :
    ∃ e, Antitone e ∧ (∀ i, e i ≤ a i) ∧ (∀ i, q ≤ i → e i = 0) ∧
      prefixSum e q = r ∧ ColumnParity e 1 := by
  let b := r/2+1
  have hb : b ≤ prefixSum (fun i => a i / 2) q := by dsimp [b]; omega
  let v := evenFill a b
  have hv : Antitone v := evenFill_antitone ha b
  have hsum : prefixSum v q = r+1 := by
    rw [evenFill_sum ha b q hb]; dsimp [b]; omega
  obtain ⟨t,htq,hpos,hzero⟩ := positive_prefix hv (evenFill_zero ha b q hb)
  have ht : 0 < t := by
    by_contra hn
    have ht : t = 0 := by omega
    have hz (i : ℕ) : v i = 0 := hzero i (by omega)
    have hs : prefixSum v q = 0 := by simp [prefixSum,hz]
    omega
  let j := t-1
  have hjt : j < t := by dsimp [j]; omega
  have hjq : j < q := lt_of_lt_of_le hjt htq
  have hjpos : 0 < v j := hpos j hjt
  have hlast (i : ℕ) (hi : j < i) : v i = 0 := hzero i (by dsimp [j] at hi; omega)
  refine ⟨trimLast v j,trimLast_antitone hv j hlast, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (Nat.sub_le _ _).trans (evenFill_le a b i)
  · intro i hi
    have hz := hzero i (htq.trans hi)
    simp [trimLast,hz]
  · have hs := trimLast_sum hjq hjpos
    omega
  · simp only [ColumnParity,show (1:ℕ) ≠ 0 by decide,if_false]
    refine ⟨j, ?_, ?_⟩
    · have he := evenFill_even a b j
      dsimp [trimLast]
      rw [if_pos (Eq.refl j)]
      change (v j - 1) % 2 = 1
      change v j % 2 = 0 at he
      omega
    · intro i hi
      simpa [trimLast,hi] using evenFill_even a b i

private theorem select_odd_top {a : ℕ → ℕ} (ha : Antitone a) {q : ℕ}
    (hodd : ∃ j < q, a j % 2 = 1) :
    ∃ e, Antitone e ∧ (∀ i, e i ≤ a i) ∧ (∀ i, q ≤ i → e i = 0) ∧
      prefixSum e q = 2*prefixSum (fun i => a i / 2) q+1 ∧ ColumnParity e 1 := by
  classical
  let j := Nat.find hodd
  have hjq : j < q := (Nat.find_spec hodd).1
  have hjodd : a j % 2 = 1 := (Nat.find_spec hodd).2
  have hbefore (i : ℕ) (hi : i < j) : a i % 2 = 0 := by
    have hn := Nat.find_min hodd hi
    have hiq := hi.trans hjq
    have hnot : a i % 2 ≠ 1 := fun hm => hn ⟨hiq,hm⟩
    omega
  let P := prefixSum (fun i => a i / 2) q
  let v := evenFill a P
  let e := fun i => v i + if i = j then 1 else 0
  have hv : Antitone v := evenFill_antitone ha P
  have hej : e j = a j := by
    dsimp [e,v,P]
    rw [evenFill_full ha q j hjq]
    rw [if_pos (Eq.refl j)]
    omega
  have hei (i : ℕ) (hi : i < j) : e i = a i := by
    have hneq : i ≠ j := by omega
    dsimp [e,v,P]
    rw [evenFill_full ha q i (hi.trans hjq)]
    simp only [if_neg hneq,Nat.add_zero]
    have hh := hbefore i hi
    omega
  have hle (i : ℕ) : e i ≤ a i := by
    by_cases hi : i = j
    · subst i; rw [hej]
    · simpa [e,hi] using evenFill_le a P i
  refine ⟨e, ?_,hle, ?_, ?_, ?_⟩
  · intro i k hik
    by_cases hi : i = j
    · subst i; rw [hej]; exact (hle k).trans (ha hik)
    · by_cases hk : k = j
      · subst k; rw [hej,hei i (by omega)]; exact ha hik
      · simpa [e,hi,hk] using hv hik
  · intro i hi
    have hneq : i ≠ j := by omega
    have hz := evenFill_zero ha P q (le_refl P) i hi
    simpa [e,hneq] using hz
  · have hvsum := evenFill_sum ha P q (le_refl P)
    have hs : prefixSum e q = prefixSum v q+1 := by
      simp [e,prefixSum,Finset.sum_add_distrib,hjq]
    rw [hs,hvsum]
  · simp only [ColumnParity,show (1:ℕ) ≠ 0 by decide,if_false]
    refine ⟨j, ?_, ?_⟩
    · rw [hej]; exact hjodd
    · intro i hi
      simpa [e,hi] using evenFill_even a P i

/-- The original signed capacity suffices, including both odd branches. -/
theorem parity_selection {a : ℕ → ℕ} (ha : Antitone a) {q r delta : ℕ}
    (_hr : 0 < r) (hpar : r % 2 = delta)
    (hbound : (r : ℤ) ≤ parityCapacity a q delta) :
    ∃ e, Antitone e ∧ (∀ i, e i ≤ a i) ∧ (∀ i, q ≤ i → e i = 0) ∧
      prefixSum e q = r ∧ ColumnParity e delta := by
  classical
  by_cases hd : delta = 0
  · rw [hd] at hpar hbound ⊢
    apply select_even ha hpar
    simp [parityCapacity] at hbound
    omega
  · have hd1 : delta = 1 := by omega
    rw [hd1] at hpar hbound ⊢
    by_cases ho : ∃ j < q, a j % 2 = 1
    · simp only [parityCapacity,show (1:ℕ) ≠ 0 by decide,if_false,if_pos ho] at hbound
      by_cases hi : r+1 ≤ 2*prefixSum (fun i => a i / 2) q
      · exact select_odd_interior ha hpar hi
      · have ht : r = 2*prefixSum (fun i => a i / 2) q+1 := by omega
        rw [ht]
        exact select_odd_top ha ho
    · simp only [parityCapacity,show (1:ℕ) ≠ 0 by decide,if_false,if_neg ho] at hbound
      exact select_odd_interior ha hpar (by omega)

/-- Every feasible vector obeys the signed bound, even without antitonicity. -/
theorem parity_selection_bound {a e : ℕ → ℕ} {q delta : ℕ}
    (hle : ∀ i, e i ≤ a i) (hzero : ∀ i, q ≤ i → e i = 0)
    (hspec : ColumnParity e delta) :
    (prefixSum e q : ℤ) ≤ parityCapacity a q delta := by
  classical
  by_cases hd : delta = 0
  · have heven : ∀ i, e i % 2 = 0 := by simpa [ColumnParity,hd] using hspec
    have hpoint (i : ℕ) : e i ≤ 2*(a i / 2) := by
      have he := heven i
      have hl := hle i
      omega
    have hs := Finset.sum_le_sum (s := Finset.range q) (fun i _ => hpoint i)
    have hsum : prefixSum e q ≤ 2*prefixSum (fun i => a i / 2) q := by
      simpa [prefixSum,← Finset.mul_sum] using hs
    simp [parityCapacity,hd]
    omega
  · obtain ⟨j,hjodd,heven⟩ := (show ∃ j, e j % 2 = 1 ∧ ∀ i, i ≠ j → e i % 2 = 0 from
      by simpa [ColumnParity,hd] using hspec)
    have hjq : j < q := by
      by_contra hn
      have hz := hzero j (by omega)
      rw [hz] at hjodd
      omega
    by_cases ho : ∃ i < q, a i % 2 = 1
    · have hpoint (i : ℕ) : e i ≤ 2*(a i / 2)+(if i = j then 1 else 0) := by
        have hl := hle i
        by_cases hi : i = j
        · subst i
          simp
          omega
        · have he := heven i hi
          simp only [if_neg hi]
          omega
      have hs := Finset.sum_le_sum (s := Finset.range q) (fun i _ => hpoint i)
      have hsum : prefixSum e q ≤ 2*prefixSum (fun i => a i / 2) q+1 := by
        simpa [prefixSum,Finset.sum_add_distrib,← Finset.mul_sum,hjq] using hs
      simp [parityCapacity,hd,ho]
      omega
    · have hpoint (i : ℕ) (hi : i < q) :
          e i+(if i = j then 1 else 0) ≤ 2*(a i / 2) := by
        have hl := hle i
        have hnot : a i % 2 ≠ 1 := fun hm => ho ⟨i,hi,hm⟩
        by_cases hij : i = j
        · subst i
          simp
          omega
        · have he := heven i hij
          simp only [if_neg hij]
          omega
      have hs := Finset.sum_le_sum (s := Finset.range q)
        (fun i hi => hpoint i (Finset.mem_range.mp hi))
      have hsum : prefixSum e q+1 ≤ 2*prefixSum (fun i => a i / 2) q := by
        simpa [prefixSum,Finset.sum_add_distrib,← Finset.mul_sum,hjq] using hs
      simp [parityCapacity,hd,ho]
      omega

/-- Feasibility is characterized by the signed-capacity criterion. -/
theorem parity_capacity_iff {a : ℕ → ℕ} (ha : Antitone a) {q r delta : ℕ}
    (hr : 0 < r) (hpar : r % 2 = delta) :
    (r : ℤ) ≤ parityCapacity a q delta ↔
      ∃ e, Antitone e ∧ (∀ i, e i ≤ a i) ∧ (∀ i, q ≤ i → e i = 0) ∧
        prefixSum e q = r ∧ ColumnParity e delta := by
  constructor
  · exact parity_selection ha hr hpar
  · rintro ⟨e,_,hle,hzero,hsum,hspec⟩
    simpa only [hsum] using parity_selection_bound hle hzero hspec

/-- The negative sentinel is preserved, rather than truncated to natural zero. -/
theorem parityCapacity_empty (a : ℕ → ℕ) (q : ℕ)
    (hz : ∀ i < q, a i = 0) : parityCapacity a q 1 = -1 := by
  classical
  have hp : prefixSum (fun i => a i / 2) q = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hz i (Finset.mem_range.mp hi)]
  have ho : ¬ ∃ i < q, a i % 2 = 1 := by
    rintro ⟨i,hi,hodd⟩
    simp [hz i hi] at hodd
  simp [parityCapacity,hp,ho]

/-- Failure of the signed capacity gives the prefix bound, including C=-1. -/
theorem failed_capacity_prefix {h : ℕ → ℕ} {d q r delta : ℕ}
    (hpar : r % 2 = delta)
    (hfail : parityCapacity (fun i => h i-d) q delta < (r : ℤ)) :
    prefixSum h q + 1 ≤ q*d+r+q := by
  classical
  let P := prefixSum (fun i => (h i-d)/2) q
  have hp : 2*P+2 ≤ r+delta := by
    by_cases hd : delta = 0
    · simp only [parityCapacity,hd] at hfail
      change 2*(P : ℤ) < (r : ℤ) at hfail
      omega
    · by_cases ho : ∃ i < q, (h i-d) % 2 = 1
      · simp only [parityCapacity,if_neg hd,if_pos ho] at hfail
        change 2*(P : ℤ)+1 < (r : ℤ) at hfail
        omega
      · simp only [parityCapacity,if_neg hd,if_neg ho] at hfail
        change 2*(P : ℤ)-1 < (r : ℤ) at hfail
        have hPeven : (2*P)%2 = 0 := by omega
        omega
  have hs := Finset.sum_le_sum (s := Finset.range q)
    (fun i (_ : i ∈ Finset.range q) =>
      show h i ≤ d+2*((h i-d)/2)+1 by omega)
  have hsum : prefixSum h q ≤ q*d+2*P+q := by
    simpa [prefixSum,P,Finset.sum_add_distrib,← Finset.mul_sum,
      Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hs
  have hdelta : delta ≤ 1 := by omega
  omega

/-- Sharper signed failure bound for q>=2, including all-even odd capacity. -/
theorem failed_capacity_prefix_sharp {h : ℕ → ℕ} {d q r delta : ℕ}
    (hq : 2 ≤ q) (hpar : r % 2 = delta)
    (hfail : parityCapacity (fun i => h i-d) q delta < (r : ℤ)) :
    prefixSum h q + 2 + delta ≤ q*d+r+q := by
  classical
  let P := prefixSum (fun i => (h i-d)/2) q
  have hs := Finset.sum_le_sum (s := Finset.range q)
    (fun i (_ : i ∈ Finset.range q) =>
      show h i ≤ d+2*((h i-d)/2)+1 by omega)
  have hsum : prefixSum h q ≤ q*d+2*P+q := by
    simpa [prefixSum,P,Finset.sum_add_distrib,← Finset.mul_sum,
      Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hs
  by_cases hd : delta = 0
  · simp only [parityCapacity,hd] at hfail
    change 2*(P : ℤ) < (r : ℤ) at hfail
    omega
  · have hdelta : delta = 1 := by omega
    rw [hdelta] at hpar hfail ⊢
    by_cases ho : ∃ i < q, (h i-d) % 2 = 1
    · simp only [parityCapacity,if_neg (by decide : 1 ≠ 0),if_pos ho] at hfail
      change 2*(P : ℤ)+1 < (r : ℤ) at hfail
      omega
    · simp only [parityCapacity,if_neg (by decide : 1 ≠ 0),if_neg ho] at hfail
      change 2*(P : ℤ)-1 < (r : ℤ) at hfail
      have hs' := Finset.sum_le_sum (s := Finset.range q)
        (fun i hi => show h i ≤ d+2*((h i-d)/2) by
          have hm : (h i-d) % 2 ≠ 1 := fun hm => ho ⟨i,Finset.mem_range.mp hi,hm⟩
          omega)
      have hsum' : prefixSum h q ≤ q*d+2*P := by
        simpa [prefixSum,P,Finset.sum_add_distrib,← Finset.mul_sum,
          Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hs'
      omega

/-- Counting the same top-d cells by rows and by capped columns. -/
theorem row_prefix_eq_capped_columns (nu : YoungDiagram) (d : ℕ) :
    prefixSum nu.rowLen d = prefixSum (capacity nu.colLen d) (nu.rowLen 0) := by
  let hc : Antitone (capacity nu.colLen d) :=
    fun _ _ hij => min_le_min (le_refl d) (nu.colLen_antitone hij)
  let top := fromColumns (capacity nu.colLen d) hc (nu.rowLen 0)
  have hrect : top.transpose = fromColumns nu.rowLen nu.rowLen_antitone d := by
    apply SetLike.ext
    rintro ⟨i,j⟩
    rw [YoungDiagram.mem_transpose,mem_fromColumns,mem_fromColumns]
    change (i < nu.rowLen 0 ∧ j < min d (nu.colLen i)) ↔ (j < d ∧ i < nu.rowLen j)
    constructor
    · rintro ⟨_,hj⟩
      obtain ⟨hjd,hjc⟩ := lt_min_iff.mp hj
      exact ⟨hjd,YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hjc)⟩
    · rintro ⟨hjd,hji⟩
      have hp : (j,i) ∈ nu := YoungDiagram.mem_iff_lt_rowLen.mpr hji
      have htop : (0,i) ∈ nu := nu.up_left_mem (Nat.zero_le j) (le_refl i) hp
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mp htop,
        lt_min_iff.mpr ⟨hjd,YoungDiagram.mem_iff_lt_colLen.mp hp⟩⟩
  have hcard : top.transpose.card = top.card := by
    simp [YoungDiagram.transpose,YoungDiagram.card]
  rw [hrect,fromColumns_card] at hcard
  exact hcard.trans (fromColumns_card _ _ _)

/-- The capacity choice supplies the input to the target geometry.
No parity support or tensor contraction is assumed or claimed here. -/
theorem band_contained_target (nu : YoungDiagram) {d K q r delta : ℕ}
    (hr : 0 < r) (hpar : r % 2 = delta)
    (hbound : (r : ℤ) ≤ parityCapacity (fun i => nu.colLen i - d) q delta)
    (hrows : K ≤ prefixSum nu.rowLen d)
    (hclear : d*q+4 ≤ K) :
    ∃ (e : ℕ → ℕ) (t : ℕ),
      Antitone e ∧ ColumnParity e delta ∧ 0 < t ∧ t ≤ q ∧ t ≤ nu.rowLen 0 ∧
      (∀ i < t, 0 < e i ∧ d + e i ≤ nu.colLen i) ∧
      (∀ i, t ≤ i → e i = 0) ∧ prefixSum e (nu.rowLen 0) = r ∧
      ∃ pi theta : YoungDiagram,
        pi.card = K ∧ theta.card = K+r ∧ theta ≤ nu ∧
        (∀ i < t, pi.colLen i = d) ∧
        (∀ i < nu.rowLen 0, pi.colLen i ≤ d ∧ theta.colLen i = pi.colLen i + e i) := by
  have ha : Antitone (fun i => nu.colLen i - d) :=
    fun _ _ hij => Nat.sub_le_sub_right (nu.colLen_antitone hij) d
  have hcapacity := hrows
  rw [row_prefix_eq_capped_columns] at hcapacity
  obtain ⟨e,he,hle,hqzero,hsize,hodd⟩ := parity_selection ha hr hpar hbound
  obtain ⟨t,htq,hpos,hzero⟩ := positive_prefix he hqzero
  have htpos : 0 < t := by
    by_contra hn
    have hz (i : ℕ) : e i = 0 := hzero i (by omega)
    have hs : prefixSum e q = 0 := by simp [prefixSum,hz]
    omega
  have hmzero : nu.colLen (nu.rowLen 0) = 0 := by
    by_contra hn
    have hp : (0,nu.rowLen 0) ∈ nu := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have ht := YoungDiagram.mem_iff_lt_rowLen.mp hp
    omega
  have htm : t ≤ nu.rowLen 0 := by
    by_contra hn
    have hp := hpos (nu.rowLen 0) (by omega)
    have hl := hle (nu.rowLen 0)
    rw [hmzero,Nat.zero_sub] at hl
    omega
  have hroom (i : ℕ) (hi : i < t) : d + e i ≤ nu.colLen i := by
    have hp := hpos i hi
    have hl := hle i
    omega
  have hs : prefixSum e (nu.rowLen 0) = r := by
    rw [prefix_after_zero hzero _ htm]
    rw [prefix_after_zero hzero _ htq] at hsize
    exact hsize
  have hguard : t*d+4 ≤ K := by
    have ht := Nat.mul_le_mul_right d htq
    rw [Nat.mul_comm d q] at hclear
    omega
  refine ⟨e,t,he,hodd,htpos,htq,htm, ?_,hzero,hs, ?_⟩
  · intro i hi
    exact ⟨hpos i hi,hroom i hi⟩
  · exact contained_target_in nu he htm hroom hzero hs hcapacity hguard

#print axioms parity_selection
#print axioms parity_capacity_iff
#print axioms parityCapacity_empty
#print axioms failed_capacity_prefix
#print axioms failed_capacity_prefix_sharp
#print axioms row_prefix_eq_capped_columns
#print axioms band_contained_target
end HSTZ
