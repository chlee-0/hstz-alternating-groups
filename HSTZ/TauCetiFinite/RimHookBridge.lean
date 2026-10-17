import HSTZ.TauCetiFinite.CharacterBridge
import HSTZ.MurnaghanNakayama.BeadReconstruction
import TauCeti.Combinatorics.Young.RimHook

/-!
List and cell geometry connecting the complete bead enumeration of rim-hook removals to
TauCeti's rim hooks and their heights. Uses TauCeti's Young-diagram rim-hook definitions.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

/-- The canonical partition list is the list of row lengths of its Young diagram. -/
theorem partitionRows_eq_rowLens {n : ℕ} (p : Nat.Partition n) :
    partitionRows p = (YoungDiagram.ofPartition p).rowLens := by
  exact (YoungDiagram.rowLens_ofPartition_eq_sort_parts p).symm

private theorem rows_shape (d : YoungDiagram) : IsShape d.rowLens := by
  exact ⟨d.rowLens_sorted.pairwise, d.pos_of_mem_rowLens⟩

private theorem rows_at (d : YoungDiagram) (i : ℕ) : rowAt d.rowLens i = d.rowLen i := by
  by_cases hi : i < d.rowLens.length
  · change (d.rowLens[i]?).getD 0 = d.rowLen i
    rw [List.getElem?_eq_getElem hi, Option.getD_some]
    exact YoungDiagram.get_rowLens
  · have hz := row_getD_zero_of_length_le d.rowLens i (by omega)
    have he : d.rowLen i = 0 := YoungDiagram.rowLen_eq_zero_of_colLen_le
      (by have := YoungDiagram.length_rowLens (μ := d); omega)
    exact hz.trans he.symm

/-- The cells of the row list are the cells of the Young diagram. -/
theorem partitionDiagram_cellSet (d : YoungDiagram) : cellSet d.rowLens = d.cells := by
  ext c
  obtain ⟨i,j⟩ := c
  rw [mem_cellSet_iff]
  change j < rowAt d.rowLens i ↔ (i,j) ∈ d.cells
  rw [rows_at]
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]

/-- The rows meeting the removed cells are exactly TauCeti's rim-hook rows. -/
theorem removedRows_eq_rimHookRows (d e : YoungDiagram) :
    ((cellSet d.rowLens \ cellSet e.rowLens).image Prod.fst) = d.rimHookRows e := by
  ext i
  rw [mem_removed_rows_iff, rows_at, rows_at, YoungDiagram.mem_rimHookRows]

private theorem rimHook_rowInterval {d e : YoungDiagram} (h : d.IsRimHook e) :
    ∃ a b, a ≤ b ∧ RowInterval d.rowLens e.rowLens a b := by
  obtain ⟨a,b,hab,hr⟩ := h.exists_rimHookRows_eq_Icc
  have hi (i : ℕ) : e.rowLen i < d.rowLen i ↔ a ≤ i ∧ i ≤ b := by
    rw [← YoungDiagram.mem_rimHookRows, hr, Finset.mem_Icc]
  refine ⟨a,b,hab,?_,?_,?_⟩
  · intro i
    simpa only [rows_at] using hi i
  · intro i hout
    have hn : i ∉ d.rimHookRows e := by rw [hr, Finset.mem_Icc]; omega
    simpa only [rows_at] using YoungDiagram.rowLen_eq_of_notMem_rimHookRows h.le hn
  · intro i hai hib
    have hs := h.rowLen_succ i ((hi i).mpr ⟨hai,by omega⟩)
      ((hi (i+1)).mpr ⟨by omega,by omega⟩)
    simpa only [rows_at] using hs.symm

/-- An executable rim removal is exactly a TauCeti rim hook of the same size and height. -/
theorem isRimRemoval_iff_tauRimHook (d e : YoungDiagram) (r leg : ℕ) :
    IsRimRemoval d.rowLens e.rowLens r leg ↔
      d.IsRimHook e ∧ d.card - e.card = r ∧ d.rimHookHeight e = leg := by
  constructor
  · intro h
    have hh := h
    obtain ⟨hd,he,hsub,hr,hcard,hconn,hno,hleg⟩ := hh
    have hle : e ≤ d := by
      rw [partitionDiagram_cellSet, partitionDiagram_cellSet] at hsub
      exact (YoungDiagram.cells_subset_iff).mp hsub
    obtain ⟨a,b,hab,hblen,hprofile⟩ := isRimRemoval_rowInterval _ _ r leg h
    have hi (i : ℕ) : e.rowLen i < d.rowLen i ↔ a ≤ i ∧ i ≤ b := by
      simpa only [rows_at] using hprofile.1 i
    have hrim : d.IsRimHook e := by
      refine ⟨hle,?_,?_,?_⟩
      · intro heq
        have hz : cellSet d.rowLens \ cellSet e.rowLens = ∅ := by rw [heq]; simp
        rw [hz, Finset.card_empty] at hcard
        omega
      · have hs : {i | e.rowLen i < d.rowLen i} = Set.Icc a b := by
          ext i
          exact hi i
        rw [hs]
        exact Set.ordConnected_Icc
      · intro i h1 h2
        have h1' := (hi i).mp h1
        have h2' := (hi (i+1)).mp h2
        have hs := hprofile.2.2 i h1'.1 (by omega)
        simpa only [rows_at] using hs.symm
    refine ⟨hrim,?_,?_⟩
    · rw [partitionDiagram_cellSet, partitionDiagram_cellSet] at hcard
      simpa only [YoungDiagram.card, Finset.card_sdiff_of_subset hle] using hcard
    · rw [removedRows_eq_rimHookRows] at hleg
      dsimp [YoungDiagram.rimHookHeight]
      omega
  · rintro ⟨hrim,hcard,hleg⟩
    obtain ⟨a,b,hab,hprofile⟩ := rimHook_rowInterval hrim
    have hpos := hrim.card_lt
    have hsub : cellSet e.rowLens ⊆ cellSet d.rowLens := by
      rw [partitionDiagram_cellSet, partitionDiagram_cellSet]
      exact (YoungDiagram.cells_subset_iff).mpr hrim.le
    refine ⟨rows_shape d, rows_shape e, hsub,by omega,?_,
      rowInterval_connected _ _ a b hprofile,
      rowInterval_noTwoByTwo _ _ a b hprofile,?_⟩
    · rw [partitionDiagram_cellSet, partitionDiagram_cellSet, Finset.card_sdiff_of_subset hrim.le]
      exact hcard
    · rw [removedRows_eq_rimHookRows]
      have hp := Finset.card_pos.mpr hrim.rimHookRows_nonempty
      dsimp [YoungDiagram.rimHookHeight] at hleg
      omega

/-- The moves are exactly the TauCeti rim-hook removals of size `r`; duplicate-freeness
is supplied by the enumerator. -/
theorem mem_moves_iff_tauRimHook {n m : ℕ} (lam : Nat.Partition n)
    (nu : Nat.Partition m) (r leg : ℕ) (hr : 0 < r) :
    (⟨partitionRows nu,leg⟩ : Move) ∈ moves (partitionRows lam) r ↔
      (YoungDiagram.ofPartition lam).IsRimHook (YoungDiagram.ofPartition nu) ∧
      (YoungDiagram.ofPartition lam).card - (YoungDiagram.ofPartition nu).card = r ∧
      (YoungDiagram.ofPartition lam).rimHookHeight (YoungDiagram.ofPartition nu) = leg := by
  rw [partitionRows_eq_rowLens, partitionRows_eq_rowLens,
    (moveEnumerationCorrect _ (rows_shape _) r hr).2,
    isRimRemoval_iff_tauRimHook]

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.partitionRows_eq_rowLens
#print axioms HSTZ.TauCetiFinite.partitionDiagram_cellSet
#print axioms HSTZ.TauCetiFinite.removedRows_eq_rimHookRows
#print axioms HSTZ.TauCetiFinite.isRimRemoval_iff_tauRimHook
#print axioms HSTZ.TauCetiFinite.mem_moves_iff_tauRimHook
