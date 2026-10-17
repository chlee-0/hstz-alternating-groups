import HSTZ.MurnaghanNakayama.BeadMoves
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Insertion rows and containment

The insertion algorithm `insertDesc` crosses a prefix of beads above the new
position. Decoding lowers those rows by one, inserts one row, and leaves the
suffix unchanged. Lowering a bead in a sorted list also gives pointwise smaller
padded rows. Zero trimming is treated separately, so the final statements bound
the rows of the enumerator's outputs and give cell containment.
-/
namespace HSTZ.MurnaghanNakayama

private theorem forall₂_le_self (xs : List ℕ) :
    List.Forall₂ (fun x y => x ≤ y) xs xs := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons a xs ih => exact List.Forall₂.cons (Nat.le_refl a) ih

/-- Exact row formula for insertion, including zero rows and empty prefixes.
No sorting hypothesis is needed for this identity. -/
theorem decodeRows_insertDesc (b : ℕ) (bs : List ℕ) :
    decodeRows (insertDesc b bs) =
      ((decodeRows bs).take
        (bs.takeWhile (fun c => decide (b < c))).length).map (fun x => x - 1) ++
      (b - (bs.dropWhile (fun c => decide (b < c))).length) ::
        (decodeRows bs).drop (bs.takeWhile (fun c => decide (b < c))).length := by
  induction bs with
  | nil => simp [insertDesc, decodeRows]
  | cons a bs ih =>
      by_cases h : a ≤ b
      · have hn : ¬ b < a := Nat.not_lt.mpr h
        simp [insertDesc, h, hn, decodeRows_cons, List.takeWhile, List.dropWhile]
      · have hb : b < a := Nat.lt_of_not_ge h
        simp [insertDesc, h, hb, decodeRows_cons, List.takeWhile, List.dropWhile,
          insertDesc_length, ih, Nat.sub_sub]

/-- A sorted erased list is already fixed by the transparent sorter. -/
theorem sorted_replacement (bs : List ℕ)
    (h : bs.Pairwise (fun x y => y ≤ x)) (a b : ℕ) :
    sortDesc (b :: bs.erase a) = insertDesc b (bs.erase a) := by
  change insertDesc b (sortDesc (bs.erase a)) = _
  rw [sortDesc_eq_self _ (h.sublist (List.erase_sublist))]

/-- Moving the leading bead crosses exactly an initial segment of tail rows. -/
theorem decodeRows_head_replacement (a : ℕ) (lam : Shape)
    (h : lam.Pairwise (fun x y => y ≤ x)) (b : ℕ) :
    decodeRows (sortDesc (b :: (beta (a :: lam)).erase (a + lam.length))) =
      (lam.take ((beta lam).takeWhile (fun c => decide (b < c))).length).map
        (fun x => x - 1) ++
      (b - ((beta lam).dropWhile (fun c => decide (b < c))).length) ::
        lam.drop ((beta lam).takeWhile (fun c => decide (b < c))).length := by
  rw [beta_cons, List.erase_cons_head]
  change decodeRows (insertDesc b (sortDesc (beta lam))) = _
  have hw : (beta lam).Pairwise (fun x y => y ≤ x) :=
    (beta_pairwise lam h).imp (fun hh => hh.le)
  rw [sortDesc_eq_self _ hw, decodeRows_insertDesc, decodeRows_beta]

/-- The padded insertion rows fit beneath the row replaced by the old bead. -/
theorem decodeRows_insertDesc_le (bs : List ℕ) (a b : ℕ) :
    b ≤ a → (a :: bs).Pairwise (fun x y => y ≤ x) →
      List.Forall₂ (fun x y => x ≤ y)
        (decodeRows (insertDesc b bs)) (decodeRows (a :: bs)) := by
  induction bs generalizing a with
  | nil =>
      intro h hsort
      simpa [insertDesc, decodeRows] using
        (List.Forall₂.cons h (List.Forall₂.nil : List.Forall₂ (fun x y : ℕ => x ≤ y) [] []))
  | cons c bs ih =>
      intro h hsort
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hsort
      by_cases hc : c ≤ b
      · simp only [insertDesc, if_pos hc, decodeRows_cons]
        apply List.Forall₂.cons (Nat.sub_le_sub_right h _)
        exact forall₂_le_self _
      · simp only [insertDesc, if_neg hc, decodeRows_cons, insertDesc_length,
          List.length_cons]
        apply List.Forall₂.cons (Nat.sub_le_sub_right (ha c (by simp)) _)
        simpa only [decodeRows_cons] using ih c (Nat.lt_of_not_ge hc).le ht

/-- Any lowered member of a decreasing bead list gives smaller padded rows. -/
theorem decodeRows_replacement_le (bs : List ℕ) (a b : ℕ) :
    bs.Pairwise (fun x y => y ≤ x) → a ∈ bs → b ≤ a →
      List.Forall₂ (fun x y => x ≤ y)
        (decodeRows (sortDesc (b :: bs.erase a))) (decodeRows bs) := by
  induction bs with
  | nil => intro h ha; simp at ha
  | cons c bs ih =>
      intro h ha hb
      have hfull := h
      obtain ⟨hc, ht⟩ := List.pairwise_cons.mp h
      rw [sorted_replacement _ hfull]
      by_cases hac : a = c
      · subst c
        rw [List.erase_cons_head]
        exact decodeRows_insertDesc_le bs a b hb hfull
      · have hat : a ∈ bs := (List.mem_cons.mp ha).resolve_left hac
        have hlt : b < c := by
          have hh := hc a hat
          omega
        have he : (c :: bs).erase a = c :: bs.erase a := by
          simp [List.erase, beq_false_of_ne (Ne.symm hac)]
        rw [he]
        simp only [insertDesc, if_neg (show ¬ c ≤ b by omega), decodeRows_cons,
          insertDesc_length]
        have hl := (restore_erase_perm bs a hat).length_eq
        simp only [List.length_cons] at hl
        rw [hl]
        apply List.Forall₂.cons (Nat.le_refl _)
        have hh := ih ht hat hb
        rw [sorted_replacement _ ht] at hh
        exact hh

/-- All-zero tails disappear without changing any default-zero row value. -/
theorem zero_rows_filter_getD (xs : List ℕ) (h : ∀ a ∈ xs, a = 0) :
    xs.filter (fun a => decide (0 < a)) = [] ∧
      ∀ i : ℕ, (xs[i]?).getD 0 = 0 := by
  revert h
  induction xs with
  | nil => intro h; simp
  | cons a xs ih =>
      intro h
      have ha := h a (by simp)
      have ht : ∀ b ∈ xs, b = 0 := by
        intro b hb
        exact h b (by simp [hb])
      obtain ⟨hf, hg⟩ := ih ht
      constructor
      · simp [ha, hf]
      · intro i
        cases i <;> simp [ha, hg]

/-- Trimming zeros from decreasing rows preserves the indexed diagram heights. -/
theorem filter_positive_getD (xs : List ℕ)
    (h : xs.Pairwise (fun x y => y ≤ x)) (i : ℕ) :
    ((xs.filter (fun a => decide (0 < a)))[i]?).getD 0 = (xs[i]?).getD 0 := by
  revert h i
  induction xs with
  | nil => intro h i; simp
  | cons a xs ih =>
      intro h i
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      by_cases hz : a = 0
      · have hall : ∀ b ∈ a :: xs, b = 0 := by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hz
          · have hh := ha b hb
            omega
        obtain ⟨hf, hg⟩ := zero_rows_filter_getD (a :: xs) hall
        rw [hf, hg i]
        simp
      · have hp : 0 < a := by omega
        cases i <;> simp [List.filter, hp, ih ht]

theorem forall₂_getD_le (xs ys : List ℕ)
    (h : List.Forall₂ (fun x y => x ≤ y) xs ys) (i : ℕ) :
    (xs[i]?).getD 0 ≤ (ys[i]?).getD 0 := by
  induction h generalizing i with
  | nil => simp
  | cons hab h ih =>
      cases i <;> simp [hab, ih]

/-- The output of a move, after zero trimming, fits in every row of the original shape. -/
theorem moveBead_row_le (lam : Shape) (hlam : IsShape lam) (r a : ℕ)
    (ha : a ∈ beta lam) (m : Move) (hm : moveBead (beta lam) r a = some m)
    (i : ℕ) : (m.shape[i]?).getD 0 ≤ (lam[i]?).getD 0 := by
  by_cases h : 0 < r ∧ r ≤ a ∧ a - r ∉ beta lam
  · simp only [moveBead, if_pos h, Option.some.injEq] at hm
    rw [← hm]
    have hbs : (beta lam).Pairwise (fun x y => y ≤ x) :=
      (beta_pairwise lam hlam.1).imp (fun hh => hh.le)
    have hh := decodeRows_replacement_le (beta lam) a (a - r) hbs ha (Nat.sub_le ..)
    rw [decodeRows_beta] at hh
    have hnd := replacement_nodup _ a (a - r) (beta_nodup lam hlam.1) ha h.2.2
    have ho := decodeRows_pairwise _ (sortDesc_strict hnd)
    change (((decodeRows (sortDesc ((a - r) :: (beta lam).erase a))).filter
      (fun x => decide (0 < x)))[i]?).getD 0 ≤ _
    rw [filter_positive_getD _ ho]
    exact forall₂_getD_le _ _ hh i
  · simp [moveBead, h] at hm

theorem mem_moves_row_le (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) (i : ℕ) :
    (m.shape[i]?).getD 0 ≤ (lam[i]?).getD 0 := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hm
  exact moveBead_row_le lam hlam r a ha m hm i

theorem row_getD_zero_of_length_le (lam : Shape) (i : ℕ)
    (h : lam.length ≤ i) : (lam[i]?).getD 0 = 0 := by
  revert i
  induction lam with
  | nil => intro i h; simp
  | cons a lam ih =>
      intro i h
      cases i with
      | zero => simp at h
      | succ i =>
          have ht : lam.length ≤ i := by simpa using h
          simpa using ih i ht

/-- Default-zero rows give a membership test for the cell set `cellSet`. -/
theorem mem_cellSet_iff (lam : Shape) (i j : ℕ) :
    (i, j) ∈ cellSet lam ↔ j < (lam[i]?).getD 0 := by
  constructor
  · intro h
    obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp h
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hki : k = i := congrArg Prod.fst he
    have hlj : l = j := congrArg Prod.snd he
    simpa only [hki, hlj] using Finset.mem_range.mp hl
  · intro h
    have hi : i < lam.length := by
      by_contra hn
      have hz := row_getD_zero_of_length_le lam i (Nat.le_of_not_gt hn)
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr h, rfl⟩

/-- Cell containment for every output of the enumerator. -/
theorem mem_moves_cellSet_subset (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) : cellSet m.shape ⊆ cellSet lam := by
  intro c hc
  obtain ⟨i, j⟩ := c
  apply (mem_cellSet_iff lam i j).mpr
  exact ((mem_cellSet_iff m.shape i j).mp hc).trans_le
    (mem_moves_row_le lam hlam r m hm i)

theorem rowSum_range (lam : Shape) :
    (∑ i ∈ Finset.range lam.length, (lam[i]?).getD 0) = lam.sum := by
  induction lam with
  | nil => simp
  | cons a lam ih =>
      change (∑ i ∈ Finset.range (lam.length + 1), ((a :: lam)[i]?).getD 0) = _
      rw [Finset.sum_range_succ']
      simpa [Nat.add_comm] using congrArg (fun x => x + a) ih

/-- The number of cells agrees with the row sum, for arbitrary row lists. -/
theorem cellSet_card (lam : Shape) : (cellSet lam).card = lam.sum := by
  have hd : ((Finset.range lam.length : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i => (Finset.range ((lam[i]?).getD 0)).image (fun j => (i, j))) := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro c hic hjc
    obtain ⟨x, hx, hix⟩ := Finset.mem_image.mp hic
    obtain ⟨y, hy, hjy⟩ := Finset.mem_image.mp hjc
    exact hne (congrArg Prod.fst (hix.trans hjy.symm))
  have hr (i : ℕ) :
      ((Finset.range ((lam[i]?).getD 0)).image (fun j => (i, j))).card =
        (lam[i]?).getD 0 := by
    rw [Finset.card_image_of_injective _ (fun x y h => congrArg Prod.snd h)]
    exact Finset.card_range _
  unfold cellSet
  rw [Finset.card_biUnion hd]
  simp_rw [hr]
  exact rowSum_range lam

/-- An enumerated move removes exactly the requested number of cells. -/
theorem mem_moves_removed_card (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) :
    (cellSet lam \ cellSet m.shape).card = r := by
  rw [Finset.card_sdiff_of_subset (mem_moves_cellSet_subset lam hlam r m hm),
    cellSet_card, cellSet_card]
  have hs := mem_moves_size lam hlam r m hm
  omega

theorem mem_moves_pos (lam : Shape) (r : ℕ) (m : Move)
    (hm : m ∈ moves lam r) : 0 < r := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hm
  by_cases h : 0 < r ∧ r ≤ a ∧ a - r ∉ beta lam
  · exact h.1
  · simp [moveBead, h] at hm

/-- The first five clauses of `IsRimRemoval`. Connectivity and the no-2-by-2
condition are proved in `RimValidity`, the leg count in `BeadProfile`. -/
theorem mem_moves_basic (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) :
    IsShape lam ∧ IsShape m.shape ∧ cellSet m.shape ⊆ cellSet lam ∧
      0 < r ∧ (cellSet lam \ cellSet m.shape).card = r :=
  ⟨hlam, mem_moves_isShape lam hlam r m hm,
    mem_moves_cellSet_subset lam hlam r m hm, mem_moves_pos lam r m hm,
    mem_moves_removed_card lam hlam r m hm⟩

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.decodeRows_insertDesc
#print axioms HSTZ.MurnaghanNakayama.sorted_replacement
#print axioms HSTZ.MurnaghanNakayama.decodeRows_head_replacement
#print axioms HSTZ.MurnaghanNakayama.decodeRows_insertDesc_le
#print axioms HSTZ.MurnaghanNakayama.decodeRows_replacement_le
#print axioms HSTZ.MurnaghanNakayama.filter_positive_getD
#print axioms HSTZ.MurnaghanNakayama.moveBead_row_le
#print axioms HSTZ.MurnaghanNakayama.mem_moves_row_le
#print axioms HSTZ.MurnaghanNakayama.mem_cellSet_iff
#print axioms HSTZ.MurnaghanNakayama.mem_moves_cellSet_subset
#print axioms HSTZ.MurnaghanNakayama.rowSum_range
#print axioms HSTZ.MurnaghanNakayama.cellSet_card
#print axioms HSTZ.MurnaghanNakayama.mem_moves_removed_card
#print axioms HSTZ.MurnaghanNakayama.mem_moves_pos
#print axioms HSTZ.MurnaghanNakayama.mem_moves_basic
