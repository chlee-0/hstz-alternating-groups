import HSTZ.MurnaghanNakayama.Compute
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Encoding and zero trimming

`decodeRows` is the row expression used by `decodeBeta` before zero rows are
filtered out. The identities below relate it to `beta` and make the treatment of
trailing zero rows explicit before the geometric bead-move argument.
-/
namespace HSTZ.MurnaghanNakayama

def decodeRows (bs : List ℕ) : List ℕ :=
  bs.zipIdx.map (fun bi => bi.1 + bi.2 + 1 - bs.length)

@[simp] theorem beta_length (lam : Shape) : (beta lam).length = lam.length := by
  simp [beta]

@[simp] theorem beta_cons (a : ℕ) (lam : Shape) :
    beta (a :: lam) = (a + lam.length) :: beta lam := by
  apply List.ext_getElem
  · simp [beta]
  · intro i hi hj
    cases i <;> simp [beta] <;> omega

@[simp] theorem decodeRows_cons (a : ℕ) (bs : List ℕ) :
    decodeRows (a :: bs) = (a - bs.length) :: decodeRows bs := by
  apply List.ext_getElem
  · simp [decodeRows]
  · intro i hi hj
    cases i <;> simp [decodeRows] <;> omega

/-- Keep all zero rows for this identity; no partition hypothesis is needed. -/
theorem decodeRows_beta (lam : Shape) : decodeRows (beta lam) = lam := by
  induction lam with
  | nil => rfl
  | cons a lam ih =>
      simpa [beta_cons, decodeRows_cons, beta_length] using congrArg (List.cons a) ih

/-- The decoder `decodeBeta` drops exactly the zero rows of the original list. -/
theorem decodeBeta_beta (lam : Shape) :
    decodeBeta (beta lam) = lam.filter (fun a => decide (0 < a)) := by
  change (decodeRows (beta lam)).filter (fun a => decide (0 < a)) = _
  rw [decodeRows_beta]

theorem decodeBeta_beta_of_pos (lam : Shape) (h : ∀ a ∈ lam, 0 < a) :
    decodeBeta (beta lam) = lam := by
  rw [decodeBeta_beta]
  simpa only [List.filter_eq_self, decide_eq_true_eq] using h

/-- A row bound gives the strict bound needed below the leading bead. -/
theorem beta_lt_of_le (t : ℕ) (lam : Shape) :
    (∀ a ∈ lam, a ≤ t) → ∀ b ∈ beta lam, b < t + lam.length := by
  induction lam with
  | nil => intro h b hb; simp [beta] at hb
  | cons a lam ih =>
      intro h b hb
      rw [beta_cons] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have ha := h a (by simp)
        simp only [List.length_cons]
        omega
      · have ht : ∀ c ∈ lam, c ≤ t := by
          intro c hc
          exact h c (by simp [hc])
        have hh := ih ht b hb
        simp only [List.length_cons]
        omega

theorem beta_pairwise (lam : Shape) :
    lam.Pairwise (fun a b => b ≤ a) →
      (beta lam).Pairwise (fun a b => b < a) := by
  induction lam with
  | nil => intro h; simp [beta]
  | cons a lam ih =>
      intro h
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      rw [beta_cons]
      apply List.pairwise_cons.mpr
      exact ⟨beta_lt_of_le a lam ha, ih ht⟩

theorem beta_nodup (lam : Shape) :
    lam.Pairwise (fun a b => b ≤ a) → (beta lam).Nodup := by
  induction lam with
  | nil => intro h; simp [beta]
  | cons a lam ih =>
      intro h
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      rw [beta_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, ih ht⟩
      intro hb
      have hh := beta_lt_of_le a lam ha (a + lam.length) hb
      omega

@[simp] theorem decodeRows_length (bs : List ℕ) :
    (decodeRows bs).length = bs.length := by simp [decodeRows]

/-- A strict nonnegative list contains enough room below its first bead. -/
theorem strict_head_bound (a : ℕ) (bs : List ℕ) :
    (a :: bs).Pairwise (fun x y => y < x) → bs.length ≤ a := by
  induction bs generalizing a with
  | nil => intro h; simp
  | cons b bs ih =>
      intro h
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      have hab := ha b (by simp)
      have hb := ih b ht
      simp only [List.length_cons]
      omega

/-- The inverse direction keeps zero rows, hence preserves the bead count. -/
theorem beta_decodeRows (bs : List ℕ)
    (h : bs.Pairwise (fun x y => y < x)) : beta (decodeRows bs) = bs := by
  revert h
  induction bs with
  | nil => intro h; rfl
  | cons a bs ih =>
      intro h
      have ha := strict_head_bound a bs h
      have ht := (List.pairwise_cons.mp h).2
      rw [decodeRows_cons, beta_cons, decodeRows_length,
        Nat.sub_add_cancel ha, ih ht]

theorem decodeRows_pairwise (bs : List ℕ)
    (h : bs.Pairwise (fun x y => y < x)) :
    (decodeRows bs).Pairwise (fun x y => y ≤ x) := by
  revert h
  induction bs with
  | nil => simp [decodeRows]
  | cons a bs ih =>
      intro h
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      have hd := ih ht
      cases bs with
      | nil => simp [decodeRows_cons, decodeRows]
      | cons b cs =>
          have hab := ha b (by simp)
          have hb := strict_head_bound b cs ht
          have hstep : b - cs.length ≤ a - (cs.length + 1) := by omega
          have hd' := hd
          rw [decodeRows_cons] at hd'
          obtain ⟨hbrow, hrows⟩ := List.pairwise_cons.mp hd'
          rw [decodeRows_cons]
          apply List.pairwise_cons.mpr
          refine ⟨?_, hd⟩
          intro c hc
          rw [decodeRows_cons] at hc
          rcases List.mem_cons.mp hc with rfl | hc
          · simpa only [List.length_cons] using hstep
          · have hh := (hbrow c hc).trans hstep
            simpa only [List.length_cons] using hh

/-- The staircase offset is independent of the row values, including zeros. -/
theorem beta_sum (lam : Shape) :
    (beta lam).sum = lam.sum + (List.range lam.length).sum := by
  induction lam with
  | nil => simp [beta]
  | cons a lam ih =>
      simp only [beta_cons, List.sum_cons, List.length_cons,
        List.range_succ, List.sum_append, List.sum_nil, Nat.add_zero, ih]
      omega

theorem filter_positive_sum (xs : List ℕ) :
    (xs.filter (fun a => decide (0 < a))).sum = xs.sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases ha : 0 < a
      · simp [List.filter, ha, ih]
      · have hz : a = 0 := by omega
        simp [hz, ih]

/-- Decoding a strict bead list loses no size when trailing zeros are trimmed. -/
theorem decodeBeta_sum (bs : List ℕ)
    (h : bs.Pairwise (fun x y => y < x)) :
    bs.sum = (decodeBeta bs).sum + (List.range bs.length).sum := by
  have hh := beta_sum (decodeRows bs)
  rw [beta_decodeRows bs h, decodeRows_length] at hh
  change bs.sum = ((decodeRows bs).filter (fun a => decide (0 < a))).sum + _
  rw [filter_positive_sum]
  exact hh

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.beta_cons
#print axioms HSTZ.MurnaghanNakayama.decodeRows_cons
#print axioms HSTZ.MurnaghanNakayama.decodeRows_beta
#print axioms HSTZ.MurnaghanNakayama.decodeBeta_beta
#print axioms HSTZ.MurnaghanNakayama.decodeBeta_beta_of_pos

#print axioms HSTZ.MurnaghanNakayama.beta_lt_of_le
#print axioms HSTZ.MurnaghanNakayama.beta_pairwise
#print axioms HSTZ.MurnaghanNakayama.beta_nodup
#print axioms HSTZ.MurnaghanNakayama.strict_head_bound
#print axioms HSTZ.MurnaghanNakayama.beta_decodeRows
#print axioms HSTZ.MurnaghanNakayama.decodeRows_pairwise
#print axioms HSTZ.MurnaghanNakayama.beta_sum
#print axioms HSTZ.MurnaghanNakayama.decodeBeta_sum
