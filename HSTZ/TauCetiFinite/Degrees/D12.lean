import HSTZ.TauCetiFinite.Degrees.D12.Table
import HSTZ.TauCetiFinite.Degrees.D12.Segments
import HSTZ.TauCetiFinite.SegmentedClasses
import HSTZ.TauCetiFinite.Degrees.D12.Checks00
import HSTZ.TauCetiFinite.Degrees.D12.Checks01
import HSTZ.TauCetiFinite.Degrees.D12.Checks02
import HSTZ.TauCetiFinite.Degrees.D12.Checks03
import HSTZ.TauCetiFinite.Degrees.D12.Moments00
import HSTZ.TauCetiFinite.Degrees.D12.Moments01
import HSTZ.TauCetiFinite.Degrees.D12.Moments02
import HSTZ.TauCetiFinite.Degrees.D12.Moments03
import HSTZ.TauCetiFinite.Degrees.D12.Moments04
import HSTZ.TauCetiFinite.Degrees.D12.Moments05
import HSTZ.TauCetiFinite.Degrees.D12.Moments06
import HSTZ.TauCetiFinite.Degrees.D12.Moments07
import HSTZ.TauCetiFinite.Degrees.D12.Moments08
import HSTZ.TauCetiFinite.Degrees.D12.Moments09
import HSTZ.TauCetiFinite.Degrees.D12.Targets00
import HSTZ.TauCetiFinite.Degrees.D12.Targets01
import HSTZ.TauCetiFinite.Degrees.D12.Targets02
import HSTZ.TauCetiFinite.Degrees.D12.Targets03
import HSTZ.TauCetiFinite.Degrees.D12.Targets04

/-! The degree-12 finite character certificate, assembled from the modules in
`Degrees/D12/`, which are kept separate to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

local instance (xs : Shape) : Decidable (IsShape xs) := by
  unfold IsShape
  infer_instance

theorem table_checked : checkIndexedTable table = true := by
  unfold checkIndexedTable
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 29 := by simpa [table] using List.mem_range.mp hk
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
  · exact group16_checked
  · exact group17_checked
  · exact group18_checked
  · exact group19_checked
  · exact group20_checked
  · exact group21_checked
  · exact group22_checked
  · exact group23_checked
  · exact group24_checked
  · exact group25_checked
  · exact group26_checked
  · exact group27_checked
  · exact group28_checked

theorem classes_checked : checkClasses 12 classes = true := by
  apply checkClasses_of_facts
  · change (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))).Nodup
    exact (catalog_nodup_append classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) (by decide) (catalog_nodup_append classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) (by decide) (catalog_nodup_append classSegment2 (classSegment3 ++ classSegment4) (by decide) (catalog_nodup_append classSegment3 classSegment4 (by decide) (by decide) (by change ∀ a ∈ classSegment3, a ∉ classSegment4; decide)) (by change ∀ a ∈ classSegment2, a ∉ (classSegment3 ++ classSegment4); decide)) (by change ∀ a ∈ classSegment1, a ∉ (classSegment2 ++ (classSegment3 ++ classSegment4)); decide)) (by change ∀ a ∈ classSegment0, a ∉ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))); decide))
  · change ∀ s ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))), IsShape s ∧ s.sum = 12
    exact (catalog_valid_append 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) (by decide) (catalog_valid_append 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) (by decide) (catalog_valid_append 12 classSegment2 (classSegment3 ++ classSegment4) (by decide) (catalog_valid_append 12 classSegment3 classSegment4 (by decide) (by decide)))))
  · change 77 = partitionCount 12 12 12
    decide

theorem norm_checked : 2 * indexedNormSum table 12 classes refs33 = ((12 : ℕ).factorial : ℤ) := by
  change 2 * indexedNormSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) = ((12 : ℕ).factorial : ℤ)
  rw [indexedNormSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) (by decide),
    indexedNormSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) (by decide),
    indexedNormSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) (by decide),
    indexedNormSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 (by decide)]
  decide

theorem targets_checked : ∀ nu ∈ classes, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 12 classes refs33 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  change nu ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) at hnu
  simp only [List.mem_append] at hnu
  rcases hnu with h0 | h1 | h2 | h3 | h4
  · exact targetsSegment0 nu h0
  · exact targetsSegment1 nu h1
  · exact targetsSegment2 nu h2
  · exact targetsSegment3 nu h3
  · exact targetsSegment4 nu h4

def witness : Nat.Partition 12 where
  parts := [5,4,2,1]
  parts_pos := by decide
  parts_sum := rfl

theorem witness_rows : partitionRows witness = [5,4,2,1] := by
  change ([5,4,2,1] : Multiset ℕ).sort (· ≥ ·) = [5,4,2,1]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simp)

theorem norm : evenNormNumerator witness = ((12 : ℕ).factorial : ℤ) := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs33 = true := by
    rw [witness_rows]; exact row33_checked
  rw [← indexedNorm_eq_evenNorm (by decide) table table_checked classes classes_checked witness refs33 hr]
  exact norm_checked

theorem cover_residue (nu : Nat.Partition 12) :
    evenCoverNumerator witness nu % 1000000007 ≠ 0 := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs33 = true := by
    rw [witness_rows]; exact row33_checked
  obtain ⟨refs, hp, he⟩ := targets_checked (partitionRows nu)
    (checkClasses_complete classes classes_checked nu)
  rw [← indexedCover_eq_evenCover (by decide) table table_checked classes classes_checked witness nu refs33 refs hr hp]
  exact he

end HSTZ.TauCetiFinite.D12
#print axioms HSTZ.TauCetiFinite.D12.table_checked
#print axioms HSTZ.TauCetiFinite.D12.classes_checked
#print axioms HSTZ.TauCetiFinite.D12.norm_checked
#print axioms HSTZ.TauCetiFinite.D12.targets_checked
#print axioms HSTZ.TauCetiFinite.D12.norm
#print axioms HSTZ.TauCetiFinite.D12.cover_residue
