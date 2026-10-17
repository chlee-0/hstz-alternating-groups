import HSTZ.TauCetiFinite.Degrees.D13.Table
import HSTZ.TauCetiFinite.Degrees.D13.Segments
import HSTZ.TauCetiFinite.SegmentedClasses
import HSTZ.TauCetiFinite.Degrees.D13.Checks00
import HSTZ.TauCetiFinite.Degrees.D13.Checks01
import HSTZ.TauCetiFinite.Degrees.D13.Checks02
import HSTZ.TauCetiFinite.Degrees.D13.Checks03
import HSTZ.TauCetiFinite.Degrees.D13.Checks04
import HSTZ.TauCetiFinite.Degrees.D13.Checks05
import HSTZ.TauCetiFinite.Degrees.D13.Checks06
import HSTZ.TauCetiFinite.Degrees.D13.Moments00
import HSTZ.TauCetiFinite.Degrees.D13.Moments01
import HSTZ.TauCetiFinite.Degrees.D13.Moments02
import HSTZ.TauCetiFinite.Degrees.D13.Moments03
import HSTZ.TauCetiFinite.Degrees.D13.Moments04
import HSTZ.TauCetiFinite.Degrees.D13.Moments05
import HSTZ.TauCetiFinite.Degrees.D13.Moments06
import HSTZ.TauCetiFinite.Degrees.D13.Moments07
import HSTZ.TauCetiFinite.Degrees.D13.Moments08
import HSTZ.TauCetiFinite.Degrees.D13.Moments09
import HSTZ.TauCetiFinite.Degrees.D13.Moments10
import HSTZ.TauCetiFinite.Degrees.D13.Moments11
import HSTZ.TauCetiFinite.Degrees.D13.Moments12
import HSTZ.TauCetiFinite.Degrees.D13.Targets00
import HSTZ.TauCetiFinite.Degrees.D13.Targets01
import HSTZ.TauCetiFinite.Degrees.D13.Targets02
import HSTZ.TauCetiFinite.Degrees.D13.Targets03
import HSTZ.TauCetiFinite.Degrees.D13.Targets04
import HSTZ.TauCetiFinite.Degrees.D13.Targets05
import HSTZ.TauCetiFinite.Degrees.D13.Targets06

/-! The degree-13 finite character certificate, assembled from the modules in
`Degrees/D13/`, which are kept separate to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

local instance (xs : Shape) : Decidable (IsShape xs) := by
  unfold IsShape
  infer_instance

theorem table_checked : checkIndexedTable table = true := by
  unfold checkIndexedTable
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 50 := by simpa [table] using List.mem_range.mp hk
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
  · exact group29_checked
  · exact group30_checked
  · exact group31_checked
  · exact group32_checked
  · exact group33_checked
  · exact group34_checked
  · exact group35_checked
  · exact group36_checked
  · exact group37_checked
  · exact group38_checked
  · exact group39_checked
  · exact group40_checked
  · exact group41_checked
  · exact group42_checked
  · exact group43_checked
  · exact group44_checked
  · exact group45_checked
  · exact group46_checked
  · exact group47_checked
  · exact group48_checked
  · exact group49_checked

theorem classes_checked : checkClasses 13 classes = true := by
  apply checkClasses_of_facts
  · change (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))).Nodup
    exact (catalog_nodup_append classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) (by decide) (catalog_nodup_append classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) (by decide) (catalog_nodup_append classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) (by decide) (catalog_nodup_append classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) (by decide) (catalog_nodup_append classSegment4 (classSegment5 ++ classSegment6) (by decide) (catalog_nodup_append classSegment5 classSegment6 (by decide) (by decide) (by change ∀ a ∈ classSegment5, a ∉ classSegment6; decide)) (by change ∀ a ∈ classSegment4, a ∉ (classSegment5 ++ classSegment6); decide)) (by change ∀ a ∈ classSegment3, a ∉ (classSegment4 ++ (classSegment5 ++ classSegment6)); decide)) (by change ∀ a ∈ classSegment2, a ∉ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))); decide)) (by change ∀ a ∈ classSegment1, a ∉ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))); decide)) (by change ∀ a ∈ classSegment0, a ∉ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))); decide))
  · change ∀ s ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))), IsShape s ∧ s.sum = 13
    exact (catalog_valid_append 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) (by decide) (catalog_valid_append 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) (by decide) (catalog_valid_append 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) (by decide) (catalog_valid_append 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) (by decide) (catalog_valid_append 13 classSegment4 (classSegment5 ++ classSegment6) (by decide) (catalog_valid_append 13 classSegment5 classSegment6 (by decide) (by decide)))))))
  · change 101 = partitionCount 13 13 13
    decide

theorem norm_checked : 2 * indexedNormSum table 13 classes refs34 = ((13 : ℕ).factorial : ℤ) := by
  change 2 * indexedNormSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) = ((13 : ℕ).factorial : ℤ)
  rw [indexedNormSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) (by decide),
    indexedNormSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) (by decide),
    indexedNormSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) (by decide),
    indexedNormSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) (by decide),
    indexedNormSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) (by decide),
    indexedNormSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 (by decide)]
  decide

theorem targets_checked : ∀ nu ∈ classes, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 13 classes refs34 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  change nu ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) at hnu
  simp only [List.mem_append] at hnu
  rcases hnu with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · exact targetsSegment0 nu h0
  · exact targetsSegment1 nu h1
  · exact targetsSegment2 nu h2
  · exact targetsSegment3 nu h3
  · exact targetsSegment4 nu h4
  · exact targetsSegment5 nu h5
  · exact targetsSegment6 nu h6

def witness : Nat.Partition 13 where
  parts := [6,4,2,1]
  parts_pos := by decide
  parts_sum := rfl

theorem witness_rows : partitionRows witness = [6,4,2,1] := by
  change ([6,4,2,1] : Multiset ℕ).sort (· ≥ ·) = [6,4,2,1]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simp)

theorem norm : evenNormNumerator witness = ((13 : ℕ).factorial : ℤ) := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs34 = true := by
    rw [witness_rows]; exact row34_checked
  rw [← indexedNorm_eq_evenNorm (by decide) table table_checked classes classes_checked witness refs34 hr]
  exact norm_checked

theorem cover_residue (nu : Nat.Partition 13) :
    evenCoverNumerator witness nu % 1000000007 ≠ 0 := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs34 = true := by
    rw [witness_rows]; exact row34_checked
  obtain ⟨refs, hp, he⟩ := targets_checked (partitionRows nu)
    (checkClasses_complete classes classes_checked nu)
  rw [← indexedCover_eq_evenCover (by decide) table table_checked classes classes_checked witness nu refs34 refs hr hp]
  exact he

end HSTZ.TauCetiFinite.D13
#print axioms HSTZ.TauCetiFinite.D13.table_checked
#print axioms HSTZ.TauCetiFinite.D13.classes_checked
#print axioms HSTZ.TauCetiFinite.D13.norm_checked
#print axioms HSTZ.TauCetiFinite.D13.targets_checked
#print axioms HSTZ.TauCetiFinite.D13.norm
#print axioms HSTZ.TauCetiFinite.D13.cover_residue
