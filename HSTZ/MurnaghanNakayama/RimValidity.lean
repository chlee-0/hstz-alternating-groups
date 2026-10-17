import HSTZ.MurnaghanNakayama.BeadProfile

/-!
# Forward rim-hook validity

Every output of the bead enumerator `moves` is a geometric rim-hook removal, with
the leg computed by `moveBead`. The converse is proved in `BeadReconstruction`
and the absence of duplicate moves in `MoveUniqueness`.
-/
namespace HSTZ.MurnaghanNakayama

theorem mem_removed_cells_iff (lam mu : Shape) (i j : ℕ) :
    (i, j) ∈ cellSet lam \ cellSet mu ↔ rowAt mu i ≤ j ∧ j < rowAt lam i := by
  constructor
  · intro h
    obtain ⟨hl, hm⟩ := Finset.mem_sdiff.mp h
    have hh : ¬ j < rowAt mu i := by
      intro hj
      exact hm ((mem_cellSet_iff mu i j).mpr hj)
    exact ⟨Nat.le_of_not_gt hh, (mem_cellSet_iff lam i j).mp hl⟩
  · intro h
    apply Finset.mem_sdiff.mpr
    exact ⟨(mem_cellSet_iff lam i j).mpr h.2,
      fun hm => (Nat.not_lt.mpr h.1) ((mem_cellSet_iff mu i j).mp hm)⟩

theorem rowInterval_noTwoByTwo (lam mu : Shape) (p q : ℕ)
    (h : RowInterval lam mu p q) : NoTwoByTwo (cellSet lam \ cellSet mu) := by
  intro i j hc
  obtain ⟨h00, h10, h01, h11⟩ := hc
  have hh00 := (mem_removed_cells_iff lam mu i j).mp h00
  have hh10 := (mem_removed_cells_iff lam mu (i + 1) j).mp h10
  have hh11 := (mem_removed_cells_iff lam mu (i + 1) (j + 1)).mp h11
  have hi := (h.1 i).mp (by omega)
  have hi' := (h.1 (i + 1)).mp (by omega)
  have he := h.2.2 i hi.1 (by omega)
  omega

private abbrev RemovedPath (lam mu : Shape) (a b : Cell) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ cellSet lam \ cellSet mu ∧
    y ∈ cellSet lam \ cellSet mu ∧ EdgeAdjacent x y) a b

private theorem edgeAdjacent_symm (a b : Cell) (h : EdgeAdjacent a b) :
    EdgeAdjacent b a := by
  rcases h with ⟨he, h⟩ | ⟨he, h⟩
  · exact Or.inl ⟨he.symm, h.elim Or.inr Or.inl⟩
  · exact Or.inr ⟨he.symm, h.elim Or.inr Or.inl⟩

private theorem removedPath_symm (lam mu : Shape) (a b : Cell)
    (h : RemovedPath lam mu a b) : RemovedPath lam mu b a := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih =>
      exact ih.head ⟨hbc.2.1, hbc.1, edgeAdjacent_symm _ _ hbc.2.2⟩

private theorem horizontal_path_add (lam mu : Shape) (i j n : ℕ)
    (hj : (i, j) ∈ cellSet lam \ cellSet mu)
    (hn : (i, j + n) ∈ cellSet lam \ cellSet mu) :
    RemovedPath lam mu (i, j) (i, j + n) := by
  revert hn
  induction n with
  | zero => intro hn; exact .refl
  | succ n ih =>
      intro hn
      have hleft := (mem_removed_cells_iff lam mu i j).mp hj
      have hright := (mem_removed_cells_iff lam mu i (j + (n + 1))).mp hn
      have hmid : (i, j + n) ∈ cellSet lam \ cellSet mu :=
        (mem_removed_cells_iff lam mu i _).mpr ⟨by omega, by omega⟩
      have he : EdgeAdjacent (i, j + n) (i, j + (n + 1)) :=
        Or.inl ⟨rfl, Or.inl (by simp [Nat.add_assoc])⟩
      exact (ih hmid).tail ⟨hmid, hn, he⟩

private theorem horizontal_path (lam mu : Shape) (i j k : ℕ)
    (hj : (i, j) ∈ cellSet lam \ cellSet mu)
    (hk : (i, k) ∈ cellSet lam \ cellSet mu) : RemovedPath lam mu (i, j) (i, k) := by
  by_cases h : j ≤ k
  · have he : j + (k - j) = k := by omega
    have hp := horizontal_path_add lam mu i j (k - j) hj (by simpa only [he] using hk)
    simpa only [he] using hp
  · have he : k + (j - k) = j := by omega
    have hp := horizontal_path_add lam mu i k (j - k) hk (by simpa only [he] using hj)
    exact removedPath_symm lam mu _ _ (by simpa only [he] using hp)

/-- Cross one row at its unique overlap column, and iterate. -/
private theorem rowInterval_path_forward (lam mu : Shape) (p q : ℕ)
    (h : RowInterval lam mu p q) (i j : ℕ)
    (ha : (i, j) ∈ cellSet lam \ cellSet mu) (n k : ℕ)
    (hb : (i + n, k) ∈ cellSet lam \ cellSet mu) :
    RemovedPath lam mu (i, j) (i + n, k) := by
  induction n generalizing k with
  | zero => simpa using horizontal_path lam mu i j k ha hb
  | succ n ih =>
      have hstart := (mem_removed_cells_iff lam mu i j).mp ha
      have hend := (mem_removed_cells_iff lam mu (i + (n + 1)) k).mp hb
      have hlo := ((h.1 i).mp (by omega)).1
      have hup := ((h.1 (i + (n + 1))).mp (by omega)).2
      have hstrict := (h.1 (i + n)).mpr ⟨by omega, by omega⟩
      have hnext : rowAt mu (i + n + 1) < rowAt lam (i + n + 1) := by
        simpa [Nat.add_assoc] using (show rowAt mu (i + (n + 1)) <
          rowAt lam (i + (n + 1)) by omega)
      have he := h.2.2 (i + n) (by omega) (by omega)
      have hc : (i + n, rowAt mu (i + n)) ∈ cellSet lam \ cellSet mu :=
        (mem_removed_cells_iff lam mu _ _).mpr ⟨Nat.le_refl _, hstrict⟩
      have hd : (i + n + 1, rowAt mu (i + n)) ∈ cellSet lam \ cellSet mu :=
        (mem_removed_cells_iff lam mu _ _).mpr ⟨by omega, by omega⟩
      have hp := ih _ hc
      have hv : EdgeAdjacent (i + n, rowAt mu (i + n))
          (i + n + 1, rowAt mu (i + n)) := Or.inr ⟨rfl, Or.inl rfl⟩
      have ht := hp.tail ⟨hc, hd, hv⟩
      have hb' : (i + n + 1, k) ∈ cellSet lam \ cellSet mu := by
        simpa [Nat.add_assoc] using hb
      simpa only [Nat.add_assoc] using ht.trans (horizontal_path lam mu _ _ k hd hb')

theorem rowInterval_connected (lam mu : Shape) (p q : ℕ)
    (h : RowInterval lam mu p q) : ConnectedWithin (cellSet lam \ cellSet mu) := by
  intro a ha b hb
  obtain ⟨i, j⟩ := a
  obtain ⟨k, l⟩ := b
  by_cases hik : i ≤ k
  · have he : i + (k - i) = k := by omega
    have hp := rowInterval_path_forward lam mu p q h i j ha (k - i) l
      (by simpa only [he] using hb)
    simpa only [he] using hp
  · have he : k + (i - k) = i := by omega
    have hp := rowInterval_path_forward lam mu p q h k l hb (i - k) j
      (by simpa only [he] using ha)
    exact removedPath_symm lam mu _ _ (by simpa only [he] using hp)

/-- Forward validity for the enumerator: every clause of `IsRimRemoval`, including
connectivity, the no-2-by-2 condition and the occupied-row leg count. -/
theorem mem_moves_isRimRemoval (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) : IsRimRemoval lam m.shape r m.leg := by
  obtain ⟨a, ha, hm'⟩ := List.mem_filterMap.mp hm
  have hp := moveBead_rowInterval lam hlam r a ha m hm'
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := mem_moves_basic lam hlam r m hm
  exact ⟨h₁, h₂, h₃, h₄, h₅, rowInterval_connected _ _ _ _ hp,
    rowInterval_noTwoByTwo _ _ _ _ hp, mem_moves_leg_card lam hlam r m hm⟩

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.mem_removed_cells_iff
#print axioms HSTZ.MurnaghanNakayama.rowInterval_noTwoByTwo
#print axioms HSTZ.MurnaghanNakayama.rowInterval_connected
#print axioms HSTZ.MurnaghanNakayama.mem_moves_isRimRemoval
