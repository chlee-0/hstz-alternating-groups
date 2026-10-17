import HSTZ.TauCetiFinite.MomentFolds

/-! Explicit class catalogs, checked against the proved partition count.
This avoids reducing a large nested finite-set union during each arithmetic check.
A catalog passing `checkClasses` is proved to list every partition exactly once. -/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

local instance (xs : Shape) : Decidable (IsShape xs) := by
  unfold IsShape
  infer_instance

def checkClasses (n : ℕ) (xs : List Shape) : Bool :=
  decide (xs.Nodup ∧ (∀ s ∈ xs, IsShape s ∧ s.sum = n) ∧
    xs.length = partitionCount n n n)

theorem checkClasses_eq (n : ℕ) (xs : List Shape) (hx : checkClasses n xs = true) :
    xs.toFinset = partitionShapes n n n := by
  have hh := of_decide_eq_true hx
  have hsub : xs.toFinset ⊆ partitionShapes n n n := by
    intro s hs
    have h := hh.2.1 s (List.mem_toFinset.mp hs)
    let p := rowsPartition s h.1 h.2
    have he : partitionRows p = s := rowsPartition_rows _ _ _
    simpa only [he] using partitionRows_mem_partitionShapes p
  have hc : xs.toFinset.card = (partitionShapes n n n).card := by
    calc
      _ = xs.length := List.toFinset_card_of_nodup hh.1
      _ = partitionCount n n n := hh.2.2
      _ = _ := (card_partitionShapes n n n).symm
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

theorem checkClasses_complete {n : ℕ} (xs : List Shape) (hx : checkClasses n xs = true)
    (p : Nat.Partition n) : partitionRows p ∈ xs := by
  apply List.mem_toFinset.mp
  rw [checkClasses_eq n xs hx]
  exact partitionRows_mem_partitionShapes p

private theorem sum_map_nodup (xs : List Shape) (hx : xs.Nodup) (f : Shape → ℤ) :
    (xs.map f).sum = ∑ s ∈ xs.toFinset, f s := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := List.nodup_cons.mp hx
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hh.1), ih hh.2]

theorem checkClasses_sum {n : ℕ} (xs : List Shape) (hx : checkClasses n xs = true)
    (f : Shape → ℤ) :
    (xs.map f).sum = ∑ p : Nat.Partition n, f (partitionRows p) := by
  have hn := (of_decide_eq_true hx).1
  rw [sum_map_nodup xs hn f, checkClasses_eq n xs hx, sum_partitionShapes]

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.checkClasses_eq
#print axioms HSTZ.TauCetiFinite.checkClasses_complete
#print axioms HSTZ.TauCetiFinite.checkClasses_sum
