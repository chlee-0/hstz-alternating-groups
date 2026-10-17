import HSTZ.StaircaseRowGeometry
import Mathlib.Data.List.Sort

/-! The paper's ordered asymmetric witness diagram, built with
`YoungDiagram.ofRowLens` without sorting or a small-k extension. This geometry is
new to HSTZ and does not identify the witness with the native symmetric
staircase. -/
namespace HSTZ
open OAI.Saxl

def witnessRow (k b delta i : ℕ) : ℕ :=
  k-i + if i=0 then b+delta else if i=1 then b else 0

def witnessRows (k b delta : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin k => witnessRow k b delta i)

theorem witnessRow_strict {k b delta i j : ℕ} (hij : i<j) (hj : j<k) :
    witnessRow k b delta j < witnessRow k b delta i := by
  unfold witnessRow
  split_ifs <;> omega

theorem witnessRows_sorted (k b delta : ℕ) : (witnessRows k b delta).SortedGE := by
  apply List.sortedGE_ofFn_iff.mpr
  intro i j hij
  obtain he | hl := eq_or_lt_of_le hij
  · subst j; rfl
  · exact (witnessRow_strict hl j.isLt).le

theorem witnessRows_positive (k b delta : ℕ) :
    ∀ x ∈ witnessRows k b delta, 0<x := by
  intro x hx
  simp only [witnessRows, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  have hi := i.isLt
  unfold witnessRow
  split_ifs <;> omega

def witnessDiagram (k b delta : ℕ) (_hk : 5 ≤ k) : YoungDiagram :=
  YoungDiagram.ofRowLens (witnessRows k b delta) (witnessRows_sorted k b delta)

theorem witnessDiagram_height (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessDiagram k b delta hk).colLen 0 = k := by
  rw [← YoungDiagram.length_rowLens]
  exact (YoungDiagram.rowLens_length_ofRowLens (witnessRows_positive k b delta)).trans
    List.length_ofFn

theorem witnessDiagram_row_length (k b delta i : ℕ) (hk : 5 ≤ k) :
    (witnessDiagram k b delta hk).rowLen i = witnessRow k b delta i := by
  by_cases hi : i<k
  · have he := YoungDiagram.rowLen_ofRowLens
      (w := witnessRows k b delta) (hw := witnessRows_sorted k b delta)
      ⟨i, by simpa [witnessRows] using hi⟩
    simpa [witnessDiagram, witnessRows] using he
  · have hn : (i,0) ∉ witnessDiagram k b delta hk := by
      intro hx
      obtain ⟨hh, _⟩ := YoungDiagram.mem_ofRowLens.mp hx
      simp only [witnessRows, List.length_ofFn] at hh
      omega
    have hr : (witnessDiagram k b delta hk).rowLen i = 0 := by
      by_contra h
      exact hn (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
    rw [hr]
    unfold witnessRow
    split_ifs <;> omega

theorem witnessDiagram_width (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessDiagram k b delta hk).rowLen 0 = k+b+delta := by
  rw [witnessDiagram_row_length]
  simp [witnessRow, Nat.add_assoc]

theorem witnessDiagram_prefix (k b delta : ℕ) (hk : 5 ≤ k) (q : ℕ) :
    prefixSum (witnessDiagram k b delta hk).rowLen (2+q) =
      prefixSum (staircase k).rowLen (2+q) + 2*b+delta := by
  induction q with
  | zero =>
    simp only [Nat.add_zero, prefix_succ, prefix_zero,
      witnessDiagram_row_length, staircase_row_length]
    simp [witnessRow]
    omega
  | succ q ih =>
    have hstep : 2+(q+1) = (2+q)+1 := by omega
    rw [hstep, prefix_succ, prefix_succ, ih, witnessDiagram_row_length,
      staircase_row_length]
    have hrow : witnessRow k b delta (2+q) = k-(2+q) := by
      unfold witnessRow
      split_ifs <;> omega
    rw [hrow]
    omega

theorem witnessDiagram_card (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessDiagram k b delta hk).card = k*(k+1)/2 + 2*b+delta := by
  have hs : (staircase k).colLen 0 ≤ k := by
    by_contra hn
    have hx : (k,0) ∈ staircase k :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    rw [mem_staircase] at hx
    omega
  have hp := witnessDiagram_prefix k b delta hk (k-2)
  have he : 2+(k-2)=k := by omega
  rw [he, row_prefix_full _ (by rw [witnessDiagram_height]),
    row_prefix_full _ hs, staircase_card] at hp
  exact hp

theorem witnessDiagram_not_self_conjugate (k b delta : ℕ) (hk : 5 ≤ k)
    (hr : 1≤2*b+delta) :
    (witnessDiagram k b delta hk).transpose ≠ witnessDiagram k b delta hk := by
  intro he
  have hw := congrArg (fun mu : YoungDiagram => mu.rowLen 0) he
  rw [YoungDiagram.rowLen_transpose, witnessDiagram_height, witnessDiagram_width] at hw
  omega

end HSTZ
#print axioms HSTZ.witnessRows_sorted
#print axioms HSTZ.witnessDiagram_height
#print axioms HSTZ.witnessDiagram_row_length
#print axioms HSTZ.witnessDiagram_width
#print axioms HSTZ.witnessDiagram_card
#print axioms HSTZ.witnessDiagram_not_self_conjugate
