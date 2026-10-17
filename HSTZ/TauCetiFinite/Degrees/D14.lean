import HSTZ.TauCetiFinite.Degrees.D14.Table
import HSTZ.TauCetiFinite.Degrees.D14.Segments
import HSTZ.TauCetiFinite.SegmentedClasses
import HSTZ.TauCetiFinite.Degrees.D14.Checks00
import HSTZ.TauCetiFinite.Degrees.D14.Checks01
import HSTZ.TauCetiFinite.Degrees.D14.Checks02
import HSTZ.TauCetiFinite.Degrees.D14.Checks03
import HSTZ.TauCetiFinite.Degrees.D14.Checks04
import HSTZ.TauCetiFinite.Degrees.D14.Checks05
import HSTZ.TauCetiFinite.Degrees.D14.Checks06
import HSTZ.TauCetiFinite.Degrees.D14.Checks07
import HSTZ.TauCetiFinite.Degrees.D14.Checks08
import HSTZ.TauCetiFinite.Degrees.D14.Checks09
import HSTZ.TauCetiFinite.Degrees.D14.Checks10
import HSTZ.TauCetiFinite.Degrees.D14.Moments00
import HSTZ.TauCetiFinite.Degrees.D14.Moments01
import HSTZ.TauCetiFinite.Degrees.D14.Moments02
import HSTZ.TauCetiFinite.Degrees.D14.Moments03
import HSTZ.TauCetiFinite.Degrees.D14.Moments04
import HSTZ.TauCetiFinite.Degrees.D14.Moments05
import HSTZ.TauCetiFinite.Degrees.D14.Moments06
import HSTZ.TauCetiFinite.Degrees.D14.Moments07
import HSTZ.TauCetiFinite.Degrees.D14.Moments08
import HSTZ.TauCetiFinite.Degrees.D14.Moments09
import HSTZ.TauCetiFinite.Degrees.D14.Moments10
import HSTZ.TauCetiFinite.Degrees.D14.Moments11
import HSTZ.TauCetiFinite.Degrees.D14.Moments12
import HSTZ.TauCetiFinite.Degrees.D14.Moments13
import HSTZ.TauCetiFinite.Degrees.D14.Moments14
import HSTZ.TauCetiFinite.Degrees.D14.Moments15
import HSTZ.TauCetiFinite.Degrees.D14.Moments16
import HSTZ.TauCetiFinite.Degrees.D14.Targets00
import HSTZ.TauCetiFinite.Degrees.D14.Targets01
import HSTZ.TauCetiFinite.Degrees.D14.Targets02
import HSTZ.TauCetiFinite.Degrees.D14.Targets03
import HSTZ.TauCetiFinite.Degrees.D14.Targets04
import HSTZ.TauCetiFinite.Degrees.D14.Targets05
import HSTZ.TauCetiFinite.Degrees.D14.Targets06
import HSTZ.TauCetiFinite.Degrees.D14.Targets07
import HSTZ.TauCetiFinite.Degrees.D14.Targets08

/-! The degree-14 finite character certificate, assembled from the modules in
`Degrees/D14/`, which are kept separate to bound memory use. -/
namespace HSTZ.TauCetiFinite.D14
open HSTZ.MurnaghanNakayama

local instance (xs : Shape) : Decidable (IsShape xs) := by
  unfold IsShape
  infer_instance

theorem table_checked : checkIndexedTable table = true := by
  unfold checkIndexedTable
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 88 := by simpa [table] using List.mem_range.mp hk
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
  · exact group50_checked
  · exact group51_checked
  · exact group52_checked
  · exact group53_checked
  · exact group54_checked
  · exact group55_checked
  · exact group56_checked
  · exact group57_checked
  · exact group58_checked
  · exact group59_checked
  · exact group60_checked
  · exact group61_checked
  · exact group62_checked
  · exact group63_checked
  · exact group64_checked
  · exact group65_checked
  · exact group66_checked
  · exact group67_checked
  · exact group68_checked
  · exact group69_checked
  · exact group70_checked
  · exact group71_checked
  · exact group72_checked
  · exact group73_checked
  · exact group74_checked
  · exact group75_checked
  · exact group76_checked
  · exact group77_checked
  · exact group78_checked
  · exact group79_checked
  · exact group80_checked
  · exact group81_checked
  · exact group82_checked
  · exact group83_checked
  · exact group84_checked
  · exact group85_checked
  · exact group86_checked
  · exact group87_checked

theorem classes_checked : checkClasses 14 classes = true := by
  apply checkClasses_of_facts
  · change (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))))))).Nodup
    exact (catalog_nodup_append classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))))))) (by decide) (catalog_nodup_append classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))))) (by decide) (catalog_nodup_append classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))))) (by decide) (catalog_nodup_append classSegment3 (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))) (by decide) (catalog_nodup_append classSegment4 (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))) (by decide) (catalog_nodup_append classSegment5 (classSegment6 ++ (classSegment7 ++ classSegment8)) (by decide) (catalog_nodup_append classSegment6 (classSegment7 ++ classSegment8) (by decide) (catalog_nodup_append classSegment7 classSegment8 (by decide) (by decide) (by change ∀ a ∈ classSegment7, a ∉ classSegment8; decide)) (by change ∀ a ∈ classSegment6, a ∉ (classSegment7 ++ classSegment8); decide)) (by change ∀ a ∈ classSegment5, a ∉ (classSegment6 ++ (classSegment7 ++ classSegment8)); decide)) (by change ∀ a ∈ classSegment4, a ∉ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))); decide)) (by change ∀ a ∈ classSegment3, a ∉ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))); decide)) (by change ∀ a ∈ classSegment2, a ∉ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))))); decide)) (by change ∀ a ∈ classSegment1, a ∉ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))))); decide)) (by change ∀ a ∈ classSegment0, a ∉ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))))))); decide))
  · change ∀ s ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))))))), IsShape s ∧ s.sum = 14
    exact (catalog_valid_append 14 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))))))) (by decide) (catalog_valid_append 14 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))))) (by decide) (catalog_valid_append 14 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))))) (by decide) (catalog_valid_append 14 classSegment3 (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))) (by decide) (catalog_valid_append 14 classSegment4 (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))) (by decide) (catalog_valid_append 14 classSegment5 (classSegment6 ++ (classSegment7 ++ classSegment8)) (by decide) (catalog_valid_append 14 classSegment6 (classSegment7 ++ classSegment8) (by decide) (catalog_valid_append 14 classSegment7 classSegment8 (by decide) (by decide)))))))))
  · change 135 = partitionCount 14 14 14
    decide

theorem norm_checked : 2 * indexedNormSum table 14 classes refs48 = ((14 : ℕ).factorial : ℤ) := by
  change 2 * indexedNormSum table 14 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))))))) (refs48Segment0 ++ (refs48Segment1 ++ (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ (refs48Segment6 ++ (refs48Segment7 ++ refs48Segment8)))))))) = ((14 : ℕ).factorial : ℤ)
  rw [indexedNormSum_append table 14 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))))))) refs48Segment0 (refs48Segment1 ++ (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ (refs48Segment6 ++ (refs48Segment7 ++ refs48Segment8))))))) (by decide),
    indexedNormSum_append table 14 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))))) refs48Segment1 (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ (refs48Segment6 ++ (refs48Segment7 ++ refs48Segment8)))))) (by decide),
    indexedNormSum_append table 14 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))))) refs48Segment2 (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ (refs48Segment6 ++ (refs48Segment7 ++ refs48Segment8))))) (by decide),
    indexedNormSum_append table 14 classSegment3 (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))) refs48Segment3 (refs48Segment4 ++ (refs48Segment5 ++ (refs48Segment6 ++ (refs48Segment7 ++ refs48Segment8)))) (by decide),
    indexedNormSum_append table 14 classSegment4 (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8))) refs48Segment4 (refs48Segment5 ++ (refs48Segment6 ++ (refs48Segment7 ++ refs48Segment8))) (by decide),
    indexedNormSum_append table 14 classSegment5 (classSegment6 ++ (classSegment7 ++ classSegment8)) refs48Segment5 (refs48Segment6 ++ (refs48Segment7 ++ refs48Segment8)) (by decide),
    indexedNormSum_append table 14 classSegment6 (classSegment7 ++ classSegment8) refs48Segment6 (refs48Segment7 ++ refs48Segment8) (by decide),
    indexedNormSum_append table 14 classSegment7 classSegment8 refs48Segment7 refs48Segment8 (by decide)]
  decide

theorem targets_checked : ∀ nu ∈ classes, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 14 classes refs48 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  change nu ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ classSegment8)))))))) at hnu
  simp only [List.mem_append] at hnu
  rcases hnu with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact targetsSegment0 nu h0
  · exact targetsSegment1 nu h1
  · exact targetsSegment2 nu h2
  · exact targetsSegment3 nu h3
  · exact targetsSegment4 nu h4
  · exact targetsSegment5 nu h5
  · exact targetsSegment6 nu h6
  · exact targetsSegment7 nu h7
  · exact targetsSegment8 nu h8

def witness : Nat.Partition 14 where
  parts := [6,5,2,1]
  parts_pos := by decide
  parts_sum := rfl

theorem witness_rows : partitionRows witness = [6,5,2,1] := by
  change ([6,5,2,1] : Multiset ℕ).sort (· ≥ ·) = [6,5,2,1]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simp)

theorem norm : evenNormNumerator witness = ((14 : ℕ).factorial : ℤ) := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs48 = true := by
    rw [witness_rows]; exact row48_checked
  rw [← indexedNorm_eq_evenNorm (by decide) table table_checked classes classes_checked witness refs48 hr]
  exact norm_checked

theorem cover_residue (nu : Nat.Partition 14) :
    evenCoverNumerator witness nu % 1000000007 ≠ 0 := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs48 = true := by
    rw [witness_rows]; exact row48_checked
  obtain ⟨refs, hp, he⟩ := targets_checked (partitionRows nu)
    (checkClasses_complete classes classes_checked nu)
  rw [← indexedCover_eq_evenCover (by decide) table table_checked classes classes_checked witness nu refs48 refs hr hp]
  exact he

end HSTZ.TauCetiFinite.D14
#print axioms HSTZ.TauCetiFinite.D14.table_checked
#print axioms HSTZ.TauCetiFinite.D14.classes_checked
#print axioms HSTZ.TauCetiFinite.D14.norm_checked
#print axioms HSTZ.TauCetiFinite.D14.targets_checked
#print axioms HSTZ.TauCetiFinite.D14.norm
#print axioms HSTZ.TauCetiFinite.D14.cover_residue
