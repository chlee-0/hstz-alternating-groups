import HSTZ.TauCetiFinite.RimHookBridge
import TauCeti.Combinatorics.Young.Partitions

/-!
Reindexes the complete, duplicate-free executable move list by canonical partitions,
keeping its integer signs and all summands, and compares the resulting sum with
TauCeti's rim-hook sum (`canonical_move_sum`). Uses TauCeti's rim-hook definitions.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama
open scoped Classical
noncomputable section

theorem partitionRows_isShape {n : ℕ} (p : Nat.Partition n) : IsShape (partitionRows p) := by
  rw [partitionRows_eq_rowLens]
  exact ⟨(YoungDiagram.ofPartition p).rowLens_sorted.pairwise,
    (YoungDiagram.ofPartition p).pos_of_mem_rowLens⟩

theorem partitionRows_sum {n : ℕ} (p : Nat.Partition n) : (partitionRows p).sum = n := by
  rw [← Multiset.sum_coe, partitionRows_parts, p.parts_sum]

theorem partitionRows_injective {n : ℕ} :
    Function.Injective (partitionRows (n := n)) := by
  intro p q he
  apply Nat.Partition.ext
  have hh := congrArg (fun xs : List ℕ => (xs : Multiset ℕ)) he
  simpa only [partitionRows_parts] using hh

/-- Repackage a positive sorted list as a partition with the same parts. -/
def rowsPartition {m : ℕ} (xs : Shape) (hx : IsShape xs) (hs : xs.sum = m) :
    Nat.Partition m where
  parts := xs
  parts_pos := by
    intro a ha
    exact hx.2 a (by simpa only [Multiset.mem_coe] using ha)
  parts_sum := by simpa only [Multiset.sum_coe] using hs

theorem rowsPartition_rows {m : ℕ} (xs : Shape) (hx : IsShape xs) (hs : xs.sum = m) :
    partitionRows (rowsPartition xs hx hs) = xs := by
  change (xs : Multiset ℕ).sort (· ≥ ·) = xs
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hx.1

/-- The executable parity sign equals the integer power `(-1) ^ leg` used by TauCeti. -/
theorem legSign_eq_pow (leg : ℕ) : legSign leg = (-1 : ℤ) ^ leg := by
  rw [neg_one_pow_eq_pow_mod_two]
  unfold legSign
  split_ifs with h
  · rw [h]
    norm_num
  · have hm : leg % 2 = 1 := by omega
    rw [hm]
    norm_num

theorem weightedSum_toFinset (f : Shape → ℤ) (ms : List Move) (hn : ms.Nodup) :
    weightedSum f ms = ∑ x ∈ ms.toFinset, legSign x.leg * f x.shape := by
  induction ms with
  | nil => simp [weightedSum]
  | cons x xs ih =>
    have hh := List.nodup_cons.mp hn
    rw [weightedSum, List.toFinset_cons, Finset.sum_insert]
    · rw [ih hh.2]
    · simpa only [List.mem_toFinset] using hh.1

/-- The full weighted move sum equals TauCeti's sum over all rim-hook removals. -/
theorem canonical_move_sum {n m r : ℕ} (lam : Nat.Partition n)
    (hn : n = m + r) (hr : 0 < r) (f : Shape → ℤ) :
    weightedSum f (moves (partitionRows lam) r) =
      ∑ nu : Nat.Partition m with
          (YoungDiagram.ofPartition lam).IsRimHook (YoungDiagram.ofPartition nu),
        (-1 : ℤ) ^ (YoungDiagram.ofPartition lam).rimHookHeight
          (YoungDiagram.ofPartition nu) * f (partitionRows nu) := by
  classical
  rw [weightedSum_toFinset _ _ (moveEnumerationCorrect _ (partitionRows_isShape lam) r hr).1]
  symm
  apply Finset.sum_bij (fun nu _ =>
    (⟨partitionRows nu, (YoungDiagram.ofPartition lam).rimHookHeight
      (YoungDiagram.ofPartition nu)⟩ : Move))
  · intro nu hnu
    apply List.mem_toFinset.mpr
    apply (mem_moves_iff_tauRimHook lam nu r _ hr).mpr
    refine ⟨(Finset.mem_filter.mp hnu).2,?_,rfl⟩
    simp only [YoungDiagram.card_ofPartition]
    omega
  · intro nu hnu eta heta he
    exact partitionRows_injective (congrArg Move.shape he)
  · intro x hx
    have hx' : x ∈ moves (partitionRows lam) r := List.mem_toFinset.mp hx
    have hs := mem_moves_isShape _ (partitionRows_isShape lam) r x hx'
    have hsize := mem_moves_size _ (partitionRows_isShape lam) r x hx'
    rw [partitionRows_sum] at hsize
    have hm : x.shape.sum = m := by omega
    let nu := rowsPartition x.shape hs hm
    have hrows : partitionRows nu = x.shape := rowsPartition_rows _ _ _
    have hmem : (⟨partitionRows nu,x.leg⟩ : Move) ∈ moves (partitionRows lam) r := by
      simpa only [hrows] using hx'
    have hh := (mem_moves_iff_tauRimHook lam nu r x.leg hr).mp hmem
    refine ⟨nu, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1⟩,?_⟩
    calc
      _ = Move.mk x.shape x.leg := congrArg₂ Move.mk hrows hh.2.2
      _ = x := by cases x; rfl
  · intro nu hnu
    simp only [legSign_eq_pow]

end
end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.partitionRows_isShape
#print axioms HSTZ.TauCetiFinite.partitionRows_sum
#print axioms HSTZ.TauCetiFinite.partitionRows_injective
#print axioms HSTZ.TauCetiFinite.rowsPartition_rows
#print axioms HSTZ.TauCetiFinite.legSign_eq_pow
#print axioms HSTZ.TauCetiFinite.weightedSum_toFinset
#print axioms HSTZ.TauCetiFinite.canonical_move_sum
