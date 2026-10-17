import HSTZ.YoungDiagramCompat
import HSTZ.ContainedTarget

/-! Remove one bottom cell in a terminal interval of nonempty columns.
Pure geometry, using natural subtraction. -/
namespace HSTZ

/-- Heights after trimming columns with index at least q. Zero heights stay zero. -/
def trimSuffix (h : ℕ → ℕ) (q i : ℕ) : ℕ := if q ≤ i then h i-1 else h i

theorem trimSuffix_antitone {h : ℕ → ℕ} (hh : Antitone h) (q : ℕ) :
    Antitone (trimSuffix h q) := by
  intro i j hij
  by_cases hi : q ≤ i
  · have hj : q ≤ j := hi.trans hij
    simp only [trimSuffix, if_pos hi, if_pos hj]
    exact Nat.sub_le_sub_right (hh hij) 1
  · by_cases hj : q ≤ j
    · simp only [trimSuffix, if_neg hi, if_pos hj]
      exact (Nat.sub_le _ _).trans (hh hij)
    · simpa only [trimSuffix, if_neg hi, if_neg hj] using hh hij

theorem trimSuffix_le (h : ℕ → ℕ) (q i : ℕ) : trimSuffix h q i ≤ h i := by
  unfold trimSuffix
  split_ifs <;> omega

theorem trimSuffix_prefix (h : ℕ → ℕ) (q : ℕ) : ∀ n,
    (∀ i < n, q ≤ i → 0 < h i) →
    prefixSum h n = prefixSum (trimSuffix h q) n + (n-q) := by
  intro n
  induction n with
  | zero => intro hp; simp
  | succ n ih =>
    intro hp
    have he := ih (fun i hi hqi => hp i (by omega) hqi)
    rw [prefix_succ, prefix_succ]
    by_cases hn : q ≤ n
    · have hnpos := hp n (by omega) hn
      simp only [trimSuffix, if_pos hn]
      omega
    · simp only [trimSuffix, if_neg hn]
      omega

/-- The contained diagram obtained by trimming the rightmost m nonempty columns. -/
def rightStripDiagram (mu : YoungDiagram) (m : ℕ) : YoungDiagram :=
  fromColumns (trimSuffix mu.colLen (mu.rowLen 0-m))
    (trimSuffix_antitone mu.colLen_antitone _) (mu.rowLen 0)

theorem rightStripDiagram_le (mu : YoungDiagram) (m : ℕ) :
    rightStripDiagram mu m ≤ mu := by
  have he := fromColumns_le (trimSuffix_antitone mu.colLen_antitone (mu.rowLen 0-m))
    mu.colLen_antitone (mu.rowLen 0) (fun i _ => trimSuffix_le mu.colLen _ i)
  rw [fromColumns_target] at he
  exact he

theorem rightStripDiagram_card (mu : YoungDiagram) {m : ℕ} (hm : m ≤ mu.rowLen 0) :
    (rightStripDiagram mu m).card + m = mu.card := by
  have hp : ∀ i < mu.rowLen 0, mu.rowLen 0-m ≤ i → 0 < mu.colLen i := by
    intro i hi _
    exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hi)
  have he := trimSuffix_prefix mu.colLen (mu.rowLen 0-m) (mu.rowLen 0) hp
  have hc := fromColumns_card mu.colLen mu.colLen_antitone (mu.rowLen 0)
  rw [fromColumns_target] at hc
  rw [rightStripDiagram, fromColumns_card]
  have hs : mu.rowLen 0-(mu.rowLen 0-m) = m := by omega
  omega

/-- A removed cell is exactly the bottom cell of a selected column. -/
theorem rightStripDiagram_removed (mu : YoungDiagram) (m : ℕ) {x : ℕ × ℕ}
    (hx : x ∈ mu) (hn : x ∉ rightStripDiagram mu m) :
    mu.rowLen 0-m ≤ x.2 ∧ x.1+1 = mu.colLen x.2 := by
  have hj : x.2 < mu.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
    (mu.up_left_mem (Nat.zero_le _) (le_refl _) hx)
  have hi := YoungDiagram.mem_iff_lt_colLen.mp hx
  have ht : ¬ x.1 < trimSuffix mu.colLen (mu.rowLen 0-m) x.2 := by
    intro hh
    exact hn ((mem_fromColumns _ _ _ _ _).mpr ⟨hj,hh⟩)
  by_cases hq : mu.rowLen 0-m ≤ x.2
  · simp only [trimSuffix, if_pos hq] at ht
    exact ⟨hq, by omega⟩
  · simp only [trimSuffix, if_neg hq] at ht
    exact False.elim (ht hi)

theorem rightStripDiagram_removed_column (mu : YoungDiagram) (m : ℕ)
    {x y : ℕ × ℕ} (hx : x ∈ mu) (hnx : x ∉ rightStripDiagram mu m)
    (hy : y ∈ mu) (hny : y ∉ rightStripDiagram mu m) (hcol : x.2 = y.2) : x = y := by
  have h₁ := (rightStripDiagram_removed mu m hx hnx).2
  have h₂ := (rightStripDiagram_removed mu m hy hny).2
  apply Prod.ext
  · rw [← hcol] at h₂
    omega
  · exact hcol

/-- Removing zero columns gives back the original diagram. -/
theorem rightStripDiagram_zero (mu : YoungDiagram) : rightStripDiagram mu 0 = mu := by
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    exact rightStripDiagram_le mu 0 hx
  · intro hx
    by_contra hn
    have he := rightStripDiagram_removed mu 0 hx hn
    have hj : x.2 < mu.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
      (mu.up_left_mem (Nat.zero_le _) (le_refl _) hx)
    simp only [Nat.sub_zero] at he
    omega

end HSTZ
#print axioms HSTZ.trimSuffix_antitone
#print axioms HSTZ.trimSuffix_prefix
#print axioms HSTZ.rightStripDiagram_le
#print axioms HSTZ.rightStripDiagram_card
#print axioms HSTZ.rightStripDiagram_removed
#print axioms HSTZ.rightStripDiagram_removed_column

#print axioms HSTZ.rightStripDiagram_zero
