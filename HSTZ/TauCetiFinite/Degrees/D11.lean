import HSTZ.TauCetiFinite.Degrees.D11.Table
import HSTZ.TauCetiFinite.Degrees.D11.Segments
import HSTZ.TauCetiFinite.SegmentedClasses
import HSTZ.TauCetiFinite.Degrees.D11.Checks00
import HSTZ.TauCetiFinite.Degrees.D11.Checks01
import HSTZ.TauCetiFinite.Degrees.D11.Moments00
import HSTZ.TauCetiFinite.Degrees.D11.Moments01
import HSTZ.TauCetiFinite.Degrees.D11.Moments02
import HSTZ.TauCetiFinite.Degrees.D11.Moments03
import HSTZ.TauCetiFinite.Degrees.D11.Moments04
import HSTZ.TauCetiFinite.Degrees.D11.Moments05
import HSTZ.TauCetiFinite.Degrees.D11.Moments06
import HSTZ.TauCetiFinite.Degrees.D11.Targets00
import HSTZ.TauCetiFinite.Degrees.D11.Targets01
import HSTZ.TauCetiFinite.Degrees.D11.Targets02
import HSTZ.TauCetiFinite.Degrees.D11.Targets03

/-! The degree-11 finite character certificate, assembled from the modules in
`Degrees/D11/`, which are kept separate to bound memory use. -/
namespace HSTZ.TauCetiFinite.D11
open HSTZ.MurnaghanNakayama

local instance (xs : Shape) : Decidable (IsShape xs) := by
  unfold IsShape
  infer_instance

theorem table_checked : checkIndexedTable table = true := by
  unfold checkIndexedTable
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 16 := by simpa [table] using List.mem_range.mp hk
  interval_cases k
  · exact group0_checked
  · exact group1_checked
  · exact group2_checked
  · exact group3_checked
  · exact group4_checked
  · exact group5_checked
  · exact group6_checked
  · exact group7_checked
  · exact group8_checked
  · exact group9_checked
  · exact group10_checked
  · exact group11_checked
  · exact group12_checked
  · exact group13_checked
  · exact group14_checked
  · exact group15_checked

theorem classes_checked : checkClasses 11 classes = true := by
  apply checkClasses_of_facts
  · change (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))).Nodup
    exact (catalog_nodup_append classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) (by decide) (catalog_nodup_append classSegment1 (classSegment2 ++ classSegment3) (by decide) (catalog_nodup_append classSegment2 classSegment3 (by decide) (by decide) (by change ∀ a ∈ classSegment2, a ∉ classSegment3; decide)) (by change ∀ a ∈ classSegment1, a ∉ (classSegment2 ++ classSegment3); decide)) (by change ∀ a ∈ classSegment0, a ∉ (classSegment1 ++ (classSegment2 ++ classSegment3)); decide))
  · change ∀ s ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))), IsShape s ∧ s.sum = 11
    exact (catalog_valid_append 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) (by decide) (catalog_valid_append 11 classSegment1 (classSegment2 ++ classSegment3) (by decide) (catalog_valid_append 11 classSegment2 classSegment3 (by decide) (by decide))))
  · change 56 = partitionCount 11 11 11
    decide

theorem norm_checked : 2 * indexedNormSum table 11 classes refs23 = ((11 : ℕ).factorial : ℤ) := by
  change 2 * indexedNormSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) = ((11 : ℕ).factorial : ℤ)
  rw [indexedNormSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) (by decide),
    indexedNormSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) (by decide),
    indexedNormSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 (by decide)]
  decide

theorem targets_checked : ∀ nu ∈ classes, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 11 classes refs23 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  change nu ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) at hnu
  simp only [List.mem_append] at hnu
  rcases hnu with h0 | h1 | h2 | h3
  · exact targetsSegment0 nu h0
  · exact targetsSegment1 nu h1
  · exact targetsSegment2 nu h2
  · exact targetsSegment3 nu h3

def witness : Nat.Partition 11 where
  parts := [5,3,2,1]
  parts_pos := by decide
  parts_sum := rfl

theorem witness_rows : partitionRows witness = [5,3,2,1] := by
  change ([5,3,2,1] : Multiset ℕ).sort (· ≥ ·) = [5,3,2,1]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simp)

theorem norm : evenNormNumerator witness = ((11 : ℕ).factorial : ℤ) := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs23 = true := by
    rw [witness_rows]; exact row23_checked
  rw [← indexedNorm_eq_evenNorm (by decide) table table_checked classes classes_checked witness refs23 hr]
  exact norm_checked

theorem cover_residue (nu : Nat.Partition 11) :
    evenCoverNumerator witness nu % 1000000007 ≠ 0 := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs23 = true := by
    rw [witness_rows]; exact row23_checked
  obtain ⟨refs, hp, he⟩ := targets_checked (partitionRows nu)
    (checkClasses_complete classes classes_checked nu)
  rw [← indexedCover_eq_evenCover (by decide) table table_checked classes classes_checked witness nu refs23 refs hr hp]
  exact he

end HSTZ.TauCetiFinite.D11
#print axioms HSTZ.TauCetiFinite.D11.table_checked
#print axioms HSTZ.TauCetiFinite.D11.classes_checked
#print axioms HSTZ.TauCetiFinite.D11.norm_checked
#print axioms HSTZ.TauCetiFinite.D11.targets_checked
#print axioms HSTZ.TauCetiFinite.D11.norm
#print axioms HSTZ.TauCetiFinite.D11.cover_residue
