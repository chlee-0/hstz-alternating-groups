import HSTZ.MurnaghanNakayama.Compute
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Invariants of the transparent bead sorter

These unconditional list lemmas supply the sorting step in the bead/rim-hook
bijection: legal replacement preserves distinctness, length and the bead sum,
and the output is decreasing.
-/
namespace HSTZ.MurnaghanNakayama

theorem insertDesc_perm (a : ℕ) (xs : List ℕ) :
    (insertDesc a xs).Perm (a :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons b xs ih =>
      by_cases h : b ≤ a
      · simp only [insertDesc, if_pos h]
        exact List.Perm.refl _
      · simp only [insertDesc, if_neg h]
        exact (List.Perm.cons b ih).trans (List.Perm.swap _ _ _)

theorem sortDesc_perm (xs : List ℕ) : (sortDesc xs).Perm xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons a xs ih =>
      exact (insertDesc_perm a (sortDesc xs)).trans (List.Perm.cons a ih)

theorem mem_insertDesc_iff (a c : ℕ) (xs : List ℕ) :
    c ∈ insertDesc a xs ↔ c = a ∨ c ∈ xs := by
  have h : c ∈ insertDesc a xs ↔ c ∈ a :: xs := (insertDesc_perm a xs).mem_iff
  simpa only [List.mem_cons] using h

theorem insertDesc_pairwise (a : ℕ) (xs : List ℕ) :
    xs.Pairwise (fun x y => y ≤ x) →
      (insertDesc a xs).Pairwise (fun x y => y ≤ x) := by
  induction xs with
  | nil => intro h; simp [insertDesc]
  | cons b xs ih =>
      intro h
      obtain ⟨hb, hxs⟩ := List.pairwise_cons.mp h
      by_cases hba : b ≤ a
      · simp only [insertDesc, if_pos hba]
        apply List.pairwise_cons.mpr
        refine ⟨?_, h⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hba
        · exact (hb c hc).trans hba
      · simp only [insertDesc, if_neg hba]
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih hxs⟩
        intro c hc
        rcases (mem_insertDesc_iff a c xs).mp hc with rfl | hc
        · exact (Nat.lt_of_not_ge hba).le
        · exact hb c hc

theorem sortDesc_pairwise (xs : List ℕ) :
    (sortDesc xs).Pairwise (fun x y => y ≤ x) := by
  induction xs with
  | nil => simp [sortDesc]
  | cons a xs ih => exact insertDesc_pairwise a (sortDesc xs) ih

theorem sortDesc_nodup {xs : List ℕ} (h : xs.Nodup) : (sortDesc xs).Nodup :=
  (sortDesc_perm xs).nodup_iff.mpr h

theorem sortDesc_length (xs : List ℕ) : (sortDesc xs).length = xs.length :=
  (sortDesc_perm xs).length_eq

theorem sortDesc_sum (xs : List ℕ) : (sortDesc xs).sum = xs.sum :=
  (sortDesc_perm xs).sum_eq

@[simp] theorem insertDesc_length (a : ℕ) (xs : List ℕ) :
    (insertDesc a xs).length = xs.length + 1 := by
  simpa using (insertDesc_perm a xs).length_eq

theorem sortDesc_eq_self (xs : List ℕ)
    (h : xs.Pairwise (fun x y => y ≤ x)) : sortDesc xs = xs := by
  revert h
  induction xs with
  | nil => intro h; rfl
  | cons a xs ih =>
      intro h
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      change insertDesc a (sortDesc xs) = a :: xs
      rw [ih ht]
      cases xs with
      | nil => rfl
      | cons b bs =>
          simp only [insertDesc, if_pos (ha b (by simp))]

/-- Distinctness upgrades the sorter's weak order to the strict bead order. -/
theorem pairwise_lt_of_le_nodup (xs : List ℕ)
    (hord : xs.Pairwise (fun x y => y ≤ x)) (hdup : xs.Nodup) :
    xs.Pairwise (fun x y => y < x) := by
  revert hord hdup
  induction xs with
  | nil => simp
  | cons a xs ih =>
      intro hord hdup
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hord
      obtain ⟨hna, hnd⟩ := List.nodup_cons.mp hdup
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih ht hnd⟩
      intro b hb
      have hle := ha b hb
      have hne : b ≠ a := by
        intro h
        subst b
        exact hna hb
      omega

theorem sortDesc_strict {xs : List ℕ} (h : xs.Nodup) :
    (sortDesc xs).Pairwise (fun x y => y < x) :=
  pairwise_lt_of_le_nodup _ (sortDesc_pairwise xs) (sortDesc_nodup h)

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.sortDesc_perm
#print axioms HSTZ.MurnaghanNakayama.sortDesc_pairwise
#print axioms HSTZ.MurnaghanNakayama.sortDesc_nodup
#print axioms HSTZ.MurnaghanNakayama.sortDesc_length
#print axioms HSTZ.MurnaghanNakayama.sortDesc_sum
#print axioms HSTZ.MurnaghanNakayama.sortDesc_strict
#print axioms HSTZ.MurnaghanNakayama.sortDesc_eq_self
