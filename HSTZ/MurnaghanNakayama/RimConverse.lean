import HSTZ.MurnaghanNakayama.RimValidity
import Mathlib.Data.Finset.Max

/-!
# Converse geometry of a rim-hook removal

A path crossing a row cut contains a vertical edge across it. Connectedness
therefore fills the interval between the first and last removed rows, and
the no-2-by-2 condition forces the adjacent single-overlap equation.
`BeadReconstruction` recovers a legal bead move from this profile.
-/
namespace HSTZ.MurnaghanNakayama

private theorem rowAt_le_of_forall (xs : Shape) (a : ℕ)
    (h : ∀ x ∈ xs, x ≤ a) (i : ℕ) : rowAt xs i ≤ a := by
  induction xs generalizing i with
  | nil => simp [rowAt]
  | cons x xs ih =>
      cases i with
      | zero => exact h x (by simp)
      | succ i =>
          exact ih (fun y hy => h y (by simp [hy])) i

theorem rowAt_antitone (xs : Shape) (h : xs.Pairwise (fun x y => y ≤ x))
    (i j : ℕ) (hij : i ≤ j) : rowAt xs j ≤ rowAt xs i := by
  induction xs generalizing i j with
  | nil => simp [rowAt]
  | cons a xs ih =>
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      cases i with
      | zero =>
          cases j with
          | zero => exact Nat.le_refl _
          | succ j => exact rowAt_le_of_forall xs a ha j
      | succ i =>
          cases j with
          | zero => omega
          | succ j => exact ih ht i j (by omega)

/-- Cell containment gives the inequality for every default-zero row. -/
theorem rowAt_le_of_cellSet_subset (lam mu : Shape) (h : cellSet mu ⊆ cellSet lam)
    (i : ℕ) : rowAt mu i ≤ rowAt lam i := by
  by_contra hn
  have hl : rowAt lam i < rowAt mu i := by omega
  have hc := h ((mem_cellSet_iff mu i (rowAt lam i)).mpr hl)
  exact (Nat.lt_irrefl _) ((mem_cellSet_iff lam i (rowAt lam i)).mp hc)

/-- Positive partition lists are determined by their default-zero row values.
Without positivity, trailing zeros would make this false. -/
theorem shape_eq_of_rowAt_eq (xs ys : Shape) :
    (∀ x ∈ xs, 0 < x) → (∀ y ∈ ys, 0 < y) →
    (∀ i, rowAt xs i = rowAt ys i) → xs = ys := by
  induction xs generalizing ys with
  | nil =>
      intro hx hy he
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hp := hy y (by simp)
          have hz := he 0
          simp [rowAt] at hz
          omega
  | cons x xs ih =>
      intro hx hy he
      cases ys with
      | nil =>
          have hp := hx x (by simp)
          have hz := he 0
          simp [rowAt] at hz
          omega
      | cons y ys =>
          have hh : x = y := he 0
          have ht : xs = ys := ih ys
            (fun a ha => hx a (by simp [ha]))
            (fun b hb => hy b (by simp [hb]))
            (fun i => he (i + 1))
          exact congrArg₂ List.cons hh ht

private theorem edge_crosses_row (a b : Cell) (k : ℕ) (h : EdgeAdjacent a b)
    (ha : a.1 ≤ k) (hb : k < b.1) : a.1 = k ∧ b.1 = k + 1 ∧ a.2 = b.2 := by
  rcases h with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · omega
  · rcases hr with hr | hr
    · exact ⟨by omega, by omega, hc⟩
    · omega

/-- A path crossing a row cut contains a vertical contact across it. -/
theorem path_crosses_row (d : Finset Cell) (a b : Cell) (k : ℕ)
    (h : Relation.ReflTransGen (fun x y => x ∈ d ∧ y ∈ d ∧ EdgeAdjacent x y) a b)
    (ha : a.1 ≤ k) (hb : k < b.1) : ∃ j, (k, j) ∈ d ∧ (k + 1, j) ∈ d := by
  revert hb
  induction h with
  | refl => intro hb; omega
  | @tail x y hxy hstep ih =>
      intro hb
      by_cases hx : k < x.1
      · exact ih hx
      · obtain ⟨hxd, hyd, he⟩ := hstep
        obtain ⟨hxr, hyr, hcol⟩ := edge_crosses_row x y k he (by omega) hb
        have hxx : x = (k, x.2) := Prod.ext hxr rfl
        have hyy : y = (k + 1, x.2) := Prod.ext hyr hcol.symm
        exact ⟨x.2, hxx ▸ hxd, hyy ▸ hyd⟩

private theorem mem_image_fst_iff (d : Finset Cell) (i : ℕ) :
    i ∈ d.image Prod.fst ↔ ∃ j, (i, j) ∈ d := by
  constructor
  · intro hi
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hi
    have hh : c = (i, c.2) := Prod.ext he rfl
    exact ⟨c.2, hh ▸ hc⟩
  · rintro ⟨j, hj⟩
    exact Finset.mem_image.mpr ⟨(i, j), hj, rfl⟩

/-- A geometric rim-hook removal satisfies the same indexed interval equations as a
bead move. -/
theorem isRimRemoval_rowInterval (lam mu : Shape) (r leg : ℕ)
    (h : IsRimRemoval lam mu r leg) :
    ∃ p q, p ≤ q ∧ q < lam.length ∧ RowInterval lam mu p q := by
  obtain ⟨hlam, hmu, hsub, hr, hcard, hconn, hno, hleg⟩ := h
  let d := cellSet lam \ cellSet mu
  let rows := d.image Prod.fst
  have hd : d.Nonempty := Finset.card_pos.mp (by change 0 < (cellSet lam \ cellSet mu).card; omega)
  have hrows : rows.Nonempty := by
    obtain ⟨c, hc⟩ := hd
    exact ⟨c.1, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  let p := rows.min' hrows
  let q := rows.max' hrows
  have hp : p ∈ rows := Finset.min'_mem rows hrows
  have hq : q ∈ rows := Finset.max'_mem rows hrows
  have hpq : p ≤ q := Finset.min'_le_max' rows hrows
  obtain ⟨jp, hpc⟩ := (mem_image_fst_iff d p).mp hp
  obtain ⟨jq, hqc⟩ := (mem_image_fst_iff d q).mp hq
  have hcontact (i : ℕ) (hpi : p ≤ i) (hiq : i < q) :
      ∃ j, (i, j) ∈ d ∧ (i + 1, j) ∈ d :=
    path_crosses_row d (p, jp) (q, jq) i (hconn _ hpc _ hqc) hpi hiq
  have hinterval (i : ℕ) : i ∈ rows ↔ p ≤ i ∧ i ≤ q := by
    constructor
    · intro hi
      exact ⟨Finset.min'_le rows i hi, Finset.le_max' rows i hi⟩
    · intro hi
      by_cases he : i = q
      · simpa only [he] using hq
      · obtain ⟨j, hj, hj'⟩ := hcontact i hi.1 (by omega)
        exact (mem_image_fst_iff d i).mpr ⟨j, hj⟩
  have hprofile : RowInterval lam mu p q := by
    constructor
    · intro i
      exact (mem_removed_rows_iff lam mu i).symm.trans (hinterval i)
    constructor
    · intro i hi
      have hle := rowAt_le_of_cellSet_subset lam mu hsub i
      have hnot : ¬ rowAt mu i < rowAt lam i := by
        intro hh
        have hm := (hinterval i).mp ((mem_removed_rows_iff lam mu i).mpr hh)
        omega
      omega
    · intro i hpi hiq
      obtain ⟨j, hj, hj'⟩ := hcontact i hpi hiq
      have hc := (mem_removed_cells_iff lam mu i j).mp hj
      have hc' := (mem_removed_cells_iff lam mu (i + 1) j).mp hj'
      have hl := rowAt_antitone lam hlam.1 i (i + 1) (by omega)
      have hm := rowAt_antitone mu hmu.1 i (i + 1) (by omega)
      have hbound : rowAt lam (i + 1) ≤ rowAt mu i + 1 := by
        by_contra hn
        apply hno i (rowAt mu i)
        exact ⟨(mem_removed_cells_iff lam mu i _).mpr ⟨by omega, by omega⟩,
          (mem_removed_cells_iff lam mu (i + 1) _).mpr ⟨by omega, by omega⟩,
          (mem_removed_cells_iff lam mu i _).mpr ⟨by omega, by omega⟩,
          (mem_removed_cells_iff lam mu (i + 1) _).mpr ⟨by omega, by omega⟩⟩
      omega
  have hqlen : q < lam.length := by
    have hlt := (hprofile.1 q).mpr ⟨hpq, Nat.le_refl _⟩
    by_contra hn
    have hz := row_getD_zero_of_length_le lam q (by omega)
    change rowAt lam q = 0 at hz
    omega
  exact ⟨p, q, hpq, hqlen, hprofile⟩

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.rowAt_antitone
#print axioms HSTZ.MurnaghanNakayama.rowAt_le_of_cellSet_subset
#print axioms HSTZ.MurnaghanNakayama.shape_eq_of_rowAt_eq
#print axioms HSTZ.MurnaghanNakayama.path_crosses_row
#print axioms HSTZ.MurnaghanNakayama.isRimRemoval_rowInterval
