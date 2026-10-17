import HSTZ.TauCetiFinite.MomentFolds
import HSTZ.TauCetiFinite.DegreeFiveCertificate

/-!
Checks the degree-five character sums for the witness (3,2) using the 66-entry
certificate in `DegreeFiveCertificate`. The statement for every target partition follows from the
proved completeness of the partition enumeration, not from the 49 listed queries.
The check is a kernel `decide`; no external computation or compiler-trust axiom is used.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

def witness5 : Nat.Partition 5 where
  parts := [3,2]
  parts_pos := by decide
  parts_sum := rfl

theorem witness5_rows : partitionRows witness5 = [3,2] := by
  change ([3,2] : Multiset ℕ).sort (· ≥ ·) = [3,2]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simp)

/-- All class rows are present, the norm sum is 120, and all seven cover sums are nonzero
modulo 1000000007. -/
theorem degree_five_moments_checked :
    classRowPresent DegreeFive.a5Certificate 5 [3,2] = true ∧
    cachedNorm DegreeFive.a5Certificate 5 [3,2] = 120 ∧
    ∀ nu ∈ partitionShapes 5 5 5,
      classRowPresent DegreeFive.a5Certificate 5 nu = true ∧
      cachedCover DegreeFive.a5Certificate 5 [3,2] nu % 1000000007 ≠ 0 := by
  decide

theorem degree_five_norm : evenNormNumerator witness5 = ((5 : ℕ).factorial : ℤ) := by
  have hv : verify DegreeFive.a5Certificate = true := by
    have hh : verify DegreeFive.a5Certificate = true ∧
        queriesPresent DegreeFive.a5Certificate DegreeFive.a5Queries = true := by
      simpa only [checkBatch, Bool.and_eq_true] using DegreeFive.a5_batch_checked
    exact hh.1
  have hp : classRowPresent DegreeFive.a5Certificate 5 (partitionRows witness5) = true := by
    rw [witness5_rows]; exact degree_five_moments_checked.1
  rw [← cachedNorm_eq_evenNorm (by decide) DegreeFive.a5Certificate witness5 hv hp,
    witness5_rows]
  exact degree_five_moments_checked.2.1

/-- The cover numerator is nonzero modulo 1000000007 for every partition of five. -/
theorem degree_five_cover_residue (nu : Nat.Partition 5) :
    evenCoverNumerator witness5 nu % 1000000007 ≠ 0 := by
  have hv : verify DegreeFive.a5Certificate = true := by
    have hh : verify DegreeFive.a5Certificate = true ∧
        queriesPresent DegreeFive.a5Certificate DegreeFive.a5Queries = true := by
      simpa only [checkBatch, Bool.and_eq_true] using DegreeFive.a5_batch_checked
    exact hh.1
  have hp : classRowPresent DegreeFive.a5Certificate 5 (partitionRows witness5) = true := by
    rw [witness5_rows]; exact degree_five_moments_checked.1
  have ht := degree_five_moments_checked.2.2 (partitionRows nu)
    (partitionRows_mem_partitionShapes nu)
  rw [← cachedCover_eq_evenCover (by decide) DegreeFive.a5Certificate witness5 nu hv hp ht.1,
    witness5_rows]
  exact ht.2

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.degree_five_moments_checked
#print axioms HSTZ.TauCetiFinite.degree_five_norm
#print axioms HSTZ.TauCetiFinite.degree_five_cover_residue
