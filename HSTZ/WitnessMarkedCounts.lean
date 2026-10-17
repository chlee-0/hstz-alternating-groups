import HSTZ.WitnessMarkedLetters
import Mathlib.Order.Interval.Finset.Fin
import OAI.RepresentationTheory.Saxl.PositionSplit

/-! Finite-set marked counts in every witness row and column block, including the zero
tail. This is not common-position rigidity or word support. -/
namespace HSTZ
open OAI.Saxl

theorem fin_initial_count (n q : ℕ) (hq : q≤n) :
    (Finset.univ.filter (fun i : Fin n => i.val<q)).card=q := by
  by_cases hlt : q<n
  · have he : Finset.univ.filter (fun i : Fin n => i.val<q) =
        Finset.Iio (⟨q,hlt⟩ : Fin n) := by
      ext i
      simp [Fin.lt_def]
    rw [he,Fin.card_Iio]
  · have heq : q=n := by omega
    subst q
    have he : Finset.univ.filter (fun i : Fin n => i.val<n)=Finset.univ := by
      ext i
      simp
    rw [he]
    simp

theorem witnessMarkedRowLetter_in_row (k b delta : ℕ) (hk : 5 ≤ k)
    (r : ℕ) (i : Fin (k-2)) :
    (witnessMarkedRowLetter k b delta hk i).val <
      (witnessDiagram k b delta hk).rowLen r ↔ i.val<k-2-r := by
  rw [witnessDiagram_row_length]
  have hi := i.isLt
  change (if i.val=k-3 then k+b-1 else i.val+2) < witnessRow k b delta r ↔ _
  unfold witnessRow
  split_ifs <;> omega

theorem witnessMarkedColumnLetter_in_column (k b delta : ℕ) (hk : 5 ≤ k)
    (c : ℕ) (i : Fin (k-2)) :
    (witnessMarkedColumnLetter k hk i).val <
      (witnessDiagram k b delta hk).colLen c ↔ i.val<k-2-c := by
  rw [← YoungDiagram.mem_iff_lt_colLen,YoungDiagram.mem_iff_lt_rowLen,
    witnessDiagram_row_length]
  have hs : witnessRow k b delta (i.val+2)=k-(i.val+2) := by
    have h0 : i.val+2≠0 := by omega
    have h1 : i.val+2≠1 := by omega
    simp only [witnessRow,if_neg h0,if_neg h1,Nat.add_zero]
  change c < witnessRow k b delta (i.val+2) ↔ i.val<k-2-c
  rw [hs]
  omega

noncomputable def witnessRowMarkSet (k b delta : ℕ) (hk : 5 ≤ k) :
    Finset (Fin (k+b+delta)) := Finset.univ.map (witnessMarkedRowEmbedding k b delta hk)

noncomputable def witnessColumnMarkSet (k : ℕ) (hk : 5 ≤ k) : Finset (Fin k) :=
  Finset.univ.map (witnessMarkedColumnEmbedding k hk)

theorem mem_witnessRowMarkSet (k b delta : ℕ) (hk : 5 ≤ k)
    (a : Fin (k+b+delta)) :
    a ∈ witnessRowMarkSet k b delta hk ↔ witnessRowMarked k b a.val := by
  simp only [witnessRowMarkSet,Finset.mem_map,Finset.mem_univ,true_and]
  exact witnessMarkedRowLetter_range k b delta hk a

theorem mem_witnessColumnMarkSet (k : ℕ) (hk : 5 ≤ k) (a : Fin k) :
    a ∈ witnessColumnMarkSet k hk ↔ witnessColumnMarked k a.val := by
  simp only [witnessColumnMarkSet,Finset.mem_map,Finset.mem_univ,true_and]
  exact witnessMarkedColumnLetter_range k hk a

theorem witness_row_marked_count (k b delta : ℕ) (hk : 5 ≤ k) (r : ℕ) :
    ((witnessRowMarkSet k b delta hk).filter
      (fun a => a.val<(witnessDiagram k b delta hk).rowLen r)).card =
      (staircase (k-2)).rowLen r := by
  classical
  rw [witnessRowMarkSet,Finset.filter_map,Finset.card_map]
  calc
    _ = (Finset.univ.filter (fun i : Fin (k-2) => i.val<k-2-r)).card := by
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply]
      exact witnessMarkedRowLetter_in_row k b delta hk r i
    _ = (staircase (k-2)).rowLen r := by
      rw [fin_initial_count _ _ (by omega),staircase_row_length]

theorem witness_column_marked_count (k b delta : ℕ) (hk : 5 ≤ k) (c : ℕ) :
    ((witnessColumnMarkSet k hk).filter
      (fun a => a.val<(witnessDiagram k b delta hk).colLen c)).card =
      (staircase (k-2)).colLen c := by
  classical
  rw [witnessColumnMarkSet,Finset.filter_map,Finset.card_map]
  calc
    _ = (Finset.univ.filter (fun i : Fin (k-2) => i.val<k-2-c)).card := by
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply]
      exact witnessMarkedColumnLetter_in_column k b delta hk c i
    _ = (staircase (k-2)).colLen c := by
      rw [fin_initial_count _ _ (by omega),staircase_colLen]

end HSTZ
#print axioms HSTZ.fin_initial_count
#print axioms HSTZ.witnessMarkedRowLetter_in_row
#print axioms HSTZ.witnessMarkedColumnLetter_in_column
#print axioms HSTZ.mem_witnessRowMarkSet
#print axioms HSTZ.mem_witnessColumnMarkSet
#print axioms HSTZ.witness_row_marked_count
#print axioms HSTZ.witness_column_marked_count
