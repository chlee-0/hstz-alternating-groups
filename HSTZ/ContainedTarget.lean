import HSTZ.YoungDiagramCompat
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-!
The greedy contained-target construction.
It simplifies the attachment argument of the HSTZ/OpenAI proof. It is purely
geometric and proves no tensor-support statement.
Column indices are zero based; subtraction in ℕ is truncated at zero.
-/
namespace HSTZ
open scoped BigOperators

/-- Sum over the first n indices. -/
def prefixSum (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, f i

@[simp] theorem prefix_zero (f : ℕ → ℕ) : prefixSum f 0 = 0 := by simp [prefixSum]

theorem prefix_succ (f : ℕ → ℕ) (n : ℕ) :
    prefixSum f (n+1) = prefixSum f n + f n := by simp [prefixSum, Finset.sum_range_succ]

theorem prefix_mono (f : ℕ → ℕ) : Monotone (prefixSum f) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [prefix_succ]
  omega

/-- Path-height capacity at each target column. -/
def capacity (h : ℕ → ℕ) (d : ℕ) (i : ℕ) : ℕ := min d (h i)

/-- The greedy fill π_i = min(c_i, max(K − ∑_{j<i} c_j, 0)). -/
def greedy (h : ℕ → ℕ) (d K i : ℕ) : ℕ :=
  min (capacity h d i) (K - prefixSum (capacity h d) i)

theorem greedy_le_capacity (h : ℕ → ℕ) (d K i : ℕ) :
    greedy h d K i ≤ capacity h d i := Nat.min_le_left _ _

theorem greedy_le_height (h : ℕ → ℕ) (d K i : ℕ) :
    greedy h d K i ≤ h i :=
  (greedy_le_capacity h d K i).trans (Nat.min_le_right _ _)

theorem greedy_le_depth (h : ℕ → ℕ) (d K i : ℕ) :
    greedy h d K i ≤ d :=
  (greedy_le_capacity h d K i).trans (Nat.min_le_left _ _)

theorem greedy_antitone {h : ℕ → ℕ} (hh : Antitone h) (d K : ℕ) :
    Antitone (greedy h d K) := by
  intro i j hij
  exact min_le_min (min_le_min (le_refl d) (hh hij))
    (Nat.sub_le_sub_left (prefix_mono (capacity h d) hij) K)

/-- Total greedy fill, including the case where K exceeds total capacity. -/
theorem prefix_greedy (h : ℕ → ℕ) (d K m : ℕ) :
    prefixSum (greedy h d K) m = min K (prefixSum (capacity h d) m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prefix_succ, ih, prefix_succ]
    unfold greedy
    omega

theorem prefix_capacity_le (h : ℕ → ℕ) (d m : ℕ) :
    prefixSum (capacity h d) m ≤ m*d := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prefix_succ, Nat.succ_mul]
    have hc : capacity h d m ≤ d := Nat.min_le_left _ _
    omega

/-- Every reserved initial attachment column is fully filled by path cells. -/
theorem greedy_eq_depth {h e : ℕ → ℕ} {d K t : ℕ}
    (hroom : ∀ i < t, d + e i ≤ h i) (hK : t*d ≤ K) {i : ℕ} (hi : i < t) :
    greedy h d K i = d := by
  have hh := hroom i hi
  have hc : capacity h d i = d := Nat.min_eq_left (by omega)
  have hp := prefix_capacity_le h d i
  have hm : (i+1)*d ≤ t*d := Nat.mul_le_mul_right d (by omega)
  rw [greedy, hc]
  apply Nat.min_eq_left
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

/-- Add the attachment heights, which vanish after its column count t. -/
def attached (h e : ℕ → ℕ) (d K i : ℕ) : ℕ := greedy h d K i + e i

theorem attached_antitone {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    (d K : ℕ) : Antitone (attached h e d K) := by
  intro i j hij
  exact Nat.add_le_add (greedy_antitone hh d K hij) (he hij)

theorem attached_le_height {h e : ℕ → ℕ} {d K t : ℕ}
    (hroom : ∀ i < t, d + e i ≤ h i) (hzero : ∀ i, t ≤ i → e i = 0)
    (hK : t*d ≤ K) (i : ℕ) : attached h e d K i ≤ h i := by
  by_cases hi : i < t
  · rw [attached, greedy_eq_depth hroom hK hi]
    exact hroom i hi
  · simp only [attached, hzero i (by omega), Nat.add_zero]
    exact greedy_le_height h d K i

theorem prefix_attached (h e : ℕ → ℕ) (d K m : ℕ)
    (hcapacity : K ≤ prefixSum (capacity h d) m) :
    prefixSum (attached h e d K) m = K + prefixSum e m := by
  simp only [prefixSum, attached, Finset.sum_add_distrib]
  change prefixSum (greedy h d K) m + prefixSum e m = _
  rw [prefix_greedy, Nat.min_eq_left hcapacity]
  rfl

/-- Finite Young diagram with the first m column heights h. -/
def fromColumns (h : ℕ → ℕ) (hh : Antitone h) (m : ℕ) : YoungDiagram where
  cells := (Finset.range m).biUnion (fun j => Finset.range (h j) ×ˢ {j})
  isLowerSet := by
    rintro ⟨i₂,j₂⟩ ⟨i₁,j₁⟩ ⟨hi,hj⟩ hcell
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_product, Finset.mem_singleton] at hcell ⊢
    obtain ⟨j,hjm,hij,rfl⟩ := hcell
    exact ⟨j₁, lt_of_le_of_lt hj hjm, lt_of_le_of_lt hi (lt_of_lt_of_le hij (hh hj)), rfl⟩

@[simp] theorem mem_fromColumns (h : ℕ → ℕ) (hh : Antitone h) (m i j : ℕ) :
    (i,j) ∈ fromColumns h hh m ↔ j < m ∧ i < h j := by
  simp [fromColumns, and_comm]

theorem fromColumns_card (h : ℕ → ℕ) (hh : Antitone h) (m : ℕ) :
    (fromColumns h hh m).card = prefixSum h m := by
  change ((Finset.range m).biUnion (fun j => Finset.range (h j) ×ˢ {j})).card = _
  rw [Finset.card_biUnion]
  · simp [prefixSum]
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [Finset.mem_product, Finset.mem_singleton] at hp hq
    exact hij (hp.2.symm.trans hq.2)

theorem fromColumns_colLen (h : ℕ → ℕ) (hh : Antitone h) {m j : ℕ} (hj : j < m) :
    (fromColumns h hh m).colLen j = h j := by
  have hiff (i : ℕ) : i < (fromColumns h hh m).colLen j ↔ i < h j := by
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_fromColumns]
    simp [hj]
  have h₁ := hiff (h j)
  have h₂ := hiff ((fromColumns h hh m).colLen j)
  omega

theorem fromColumns_le {a b : ℕ → ℕ} (ha : Antitone a) (hb : Antitone b)
    (m : ℕ) (hab : ∀ i < m, a i ≤ b i) :
    fromColumns a ha m ≤ fromColumns b hb m := by
  intro p hp
  obtain ⟨hj,hi⟩ := (mem_fromColumns a ha m p.1 p.2).mp hp
  exact (mem_fromColumns b hb m p.1 p.2).mpr ⟨hj, hi.trans_le (hab p.2 hj)⟩

/-- The geometric interface of the contained-target construction. Support and
attachment parity are separate representation-theoretic obligations. Four reserved
positions are retained. -/
theorem contained_target {h e : ℕ → ℕ} {d K t m : ℕ}
    (hh : Antitone h) (he : Antitone e) (htm : t ≤ m)
    (hroom : ∀ i < t, d + e i ≤ h i) (hzero : ∀ i, t ≤ i → e i = 0)
    (hcapacity : K ≤ prefixSum (capacity h d) m) (hclear : t*d+4 ≤ K) :
    ∃ pi theta : YoungDiagram,
      pi.card = K ∧ theta.card = K + prefixSum e m ∧
      theta ≤ fromColumns h hh m ∧
      (∀ i < t, pi.colLen i = d) ∧
      (∀ i < m, pi.colLen i ≤ d ∧ theta.colLen i = pi.colLen i + e i) := by
  let pi := fromColumns (greedy h d K) (greedy_antitone hh d K) m
  let theta := fromColumns (attached h e d K) (attached_antitone hh he d K) m
  have hK : t*d ≤ K := by omega
  refine ⟨pi,theta, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fromColumns_card, prefix_greedy, Nat.min_eq_left hcapacity]
  · exact (fromColumns_card _ _ _).trans (prefix_attached h e d K m hcapacity)
  · exact fromColumns_le _ _ m (fun i _ => attached_le_height hroom hzero hK i)
  · intro i hi
    rw [fromColumns_colLen _ _ (lt_of_lt_of_le hi htm)]
    exact greedy_eq_depth hroom hK hi
  · intro i hi
    simp only [pi,theta,fromColumns_colLen _ _ hi]
    exact ⟨greedy_le_depth h d K i, rfl⟩

/-- Recover an existing target from all of its columns, including zero padding. -/
theorem fromColumns_target (nu : YoungDiagram) :
    fromColumns nu.colLen nu.colLen_antitone (nu.rowLen 0) = nu := by
  apply SetLike.ext
  rintro ⟨i,j⟩
  rw [mem_fromColumns]
  constructor
  · rintro ⟨_,hi⟩
    exact YoungDiagram.mem_iff_lt_colLen.mpr hi
  · intro hp
    have htop : (0,j) ∈ nu := nu.up_left_mem (Nat.zero_le i) (le_refl j) hp
    exact ⟨YoungDiagram.mem_iff_lt_rowLen.mp htop,
      YoungDiagram.mem_iff_lt_colLen.mp hp⟩

/-- The constructed θ is contained in ν, and the attachment has total size r.
Support and parity are not addressed here. -/
theorem contained_target_in (nu : YoungDiagram) {e : ℕ → ℕ} {d K t r : ℕ}
    (he : Antitone e) (htm : t ≤ nu.rowLen 0)
    (hroom : ∀ i < t, d + e i ≤ nu.colLen i)
    (hzero : ∀ i, t ≤ i → e i = 0)
    (hsize : prefixSum e (nu.rowLen 0) = r)
    (hcapacity : K ≤ prefixSum (capacity nu.colLen d) (nu.rowLen 0))
    (hclear : t*d+4 ≤ K) :
    ∃ pi theta : YoungDiagram,
      pi.card = K ∧ theta.card = K+r ∧ theta ≤ nu ∧
      (∀ i < t, pi.colLen i = d) ∧
      (∀ i < nu.rowLen 0, pi.colLen i ≤ d ∧ theta.colLen i = pi.colLen i + e i) := by
  simpa only [fromColumns_target, hsize] using
    (contained_target nu.colLen_antitone he htm hroom hzero hcapacity hclear)

#print axioms contained_target
#print axioms contained_target_in
end HSTZ
