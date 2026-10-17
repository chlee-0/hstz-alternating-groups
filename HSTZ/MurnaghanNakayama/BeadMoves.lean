import HSTZ.MurnaghanNakayama.BeadSorting
import HSTZ.MurnaghanNakayama.BeadEncoding
import HSTZ.MurnaghanNakayama.Geometry

/-!
# Partition and size invariants of legal bead moves

These theorems show that every output of the enumerator `moves` is a partition
and that its size drops by the requested amount. Containment, connectivity, the
no-2-by-2 condition, the leg count, completeness and distinctness of moves are
proved in later files.
-/
namespace HSTZ.MurnaghanNakayama

theorem decodeBeta_isShape (bs : List ℕ)
    (h : bs.Pairwise (fun x y => y < x)) : IsShape (decodeBeta bs) := by
  have hd := decodeRows_pairwise bs h
  constructor
  · change ((decodeRows bs).filter (fun a => decide (0 < a))).Pairwise _
    exact hd.filter _
  · intro a ha
    change a ∈ (decodeRows bs).filter (fun b => decide (0 < b)) at ha
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp ha).2

/-- Restoring an erased occurrence preserves the multiset, without requiring
distinctness. This also makes the length and sum bookkeeping explicit. -/
theorem restore_erase_perm (bs : List ℕ) (a : ℕ) (ha : a ∈ bs) :
    (a :: bs.erase a).Perm bs := by
  revert ha
  induction bs with
  | nil => simp
  | cons b bs ih =>
      intro ha
      by_cases hab : a = b
      · subst b
        simp
      · have ht : a ∈ bs := (List.mem_cons.mp ha).resolve_left hab
        have he : (b :: bs).erase a = b :: bs.erase a := by
          simp [List.erase, beq_false_of_ne (Ne.symm hab)]
        rw [he]
        exact (List.Perm.swap _ _ _).trans (List.Perm.cons b (ih ht))

theorem replacement_nodup (bs : List ℕ) (a b : ℕ)
    (h : bs.Nodup) (ha : a ∈ bs) (hb : b ∉ bs) :
    (b :: bs.erase a).Nodup := by
  have hp := restore_erase_perm bs a ha
  have hn := List.nodup_cons.mp (hp.nodup_iff.mpr h)
  apply List.nodup_cons.mpr
  refine ⟨?_, hn.2⟩
  intro hbe
  exact hb (hp.mem_iff.mp (List.mem_cons_of_mem a hbe))

theorem moveBead_isShape (lam : Shape) (hlam : IsShape lam) (r a : ℕ)
    (ha : a ∈ beta lam) (m : Move) (hm : moveBead (beta lam) r a = some m) :
    IsShape m.shape := by
  by_cases h : 0 < r ∧ r ≤ a ∧ a - r ∉ beta lam
  · simp only [moveBead, if_pos h, Option.some.injEq] at hm
    rw [← hm]
    exact decodeBeta_isShape _ (sortDesc_strict
      (replacement_nodup _ a (a - r) (beta_nodup lam hlam.1) ha h.2.2))
  · simp [moveBead, h] at hm

theorem moveBead_size (lam : Shape) (hlam : IsShape lam) (r a : ℕ)
    (ha : a ∈ beta lam) (m : Move) (hm : moveBead (beta lam) r a = some m) :
    m.shape.sum + r = lam.sum := by
  by_cases h : 0 < r ∧ r ≤ a ∧ a - r ∉ beta lam
  · simp only [moveBead, if_pos h, Option.some.injEq] at hm
    rw [← hm]
    have hp := restore_erase_perm (beta lam) a ha
    have hs := hp.sum_eq
    have hl := hp.length_eq
    simp only [List.sum_cons] at hs
    simp only [List.length_cons, beta_length] at hl
    have hnd := replacement_nodup _ a (a - r) (beta_nodup lam hlam.1) ha h.2.2
    have hd := decodeBeta_sum _ (sortDesc_strict hnd)
    rw [sortDesc_sum, sortDesc_length] at hd
    simp only [List.sum_cons, List.length_cons] at hd
    rw [hl] at hd
    have hsum := beta_sum lam
    change (decodeBeta (sortDesc ((a - r) :: (beta lam).erase a))).sum + r = _
    omega
  · simp [moveBead, h] at hm

theorem mem_moves_isShape (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) : IsShape m.shape := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hm
  exact moveBead_isShape lam hlam r a ha m hm

theorem mem_moves_size (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) : m.shape.sum + r = lam.sum := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hm
  exact moveBead_size lam hlam r a ha m hm

/-- The enumerator returns no moves when the removal length exceeds the size. -/
theorem moves_eq_nil_of_size_lt (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (hr : lam.sum < r) : moves lam r = [] := by
  cases hs : moves lam r with
  | nil => rfl
  | cons m ms =>
      have hm : m ∈ moves lam r := by rw [hs]; simp
      have hh := mem_moves_size lam hlam r m hm
      omega

theorem weightedSum_eq_zero (f : Shape → ℤ) (ms : List Move)
    (h : ∀ m ∈ ms, f m.shape = 0) : weightedSum f ms = 0 := by
  revert h
  induction ms with
  | nil => intro h; rfl
  | cons m ms ih =>
      intro h
      have ht : ∀ x ∈ ms, f x.shape = 0 := by
        intro x hx
        exact h x (by simp [hx])
      rw [weightedSum, h m (by simp), ih ht]
      simp

/-- The recurrence `mn` vanishes unless the shape and the cycle list have the same
size. This is a fact about the recurrence alone, independent of any character
interpretation. -/
theorem mn_eq_zero_of_size_ne (rho : List ℕ) :
    ∀ lam : Shape, IsShape lam → lam.sum ≠ rho.sum → mn lam rho = 0 := by
  induction rho with
  | nil =>
      intro lam hlam h
      have hn : lam ≠ [] := by
        intro he
        subst lam
        exact h rfl
      simp [mn_nil, baseValue, hn]
  | cons r rho ih =>
      intro lam hlam h
      rw [mn_cons]
      apply weightedSum_eq_zero
      intro m hm
      apply ih m.shape (mem_moves_isShape lam hlam r m hm)
      intro he
      apply h
      have hs := mem_moves_size lam hlam r m hm
      simp only [List.sum_cons]
      omega

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.decodeBeta_isShape
#print axioms HSTZ.MurnaghanNakayama.restore_erase_perm
#print axioms HSTZ.MurnaghanNakayama.replacement_nodup
#print axioms HSTZ.MurnaghanNakayama.moveBead_isShape
#print axioms HSTZ.MurnaghanNakayama.moveBead_size
#print axioms HSTZ.MurnaghanNakayama.mem_moves_isShape
#print axioms HSTZ.MurnaghanNakayama.mem_moves_size
#print axioms HSTZ.MurnaghanNakayama.moves_eq_nil_of_size_lt
#print axioms HSTZ.MurnaghanNakayama.mn_eq_zero_of_size_ne
