import HSTZ.TauCetiFinite.Degrees.D15.Table
import HSTZ.TauCetiFinite.Degrees.D15.Segments
import HSTZ.TauCetiFinite.SegmentedClasses
import HSTZ.TauCetiFinite.Degrees.D15.Checks00
import HSTZ.TauCetiFinite.Degrees.D15.Checks01
import HSTZ.TauCetiFinite.Degrees.D15.Checks02
import HSTZ.TauCetiFinite.Degrees.D15.Checks03
import HSTZ.TauCetiFinite.Degrees.D15.Checks04
import HSTZ.TauCetiFinite.Degrees.D15.Checks05
import HSTZ.TauCetiFinite.Degrees.D15.Checks06
import HSTZ.TauCetiFinite.Degrees.D15.Checks07
import HSTZ.TauCetiFinite.Degrees.D15.Checks08
import HSTZ.TauCetiFinite.Degrees.D15.Checks09
import HSTZ.TauCetiFinite.Degrees.D15.Checks10
import HSTZ.TauCetiFinite.Degrees.D15.Checks11
import HSTZ.TauCetiFinite.Degrees.D15.Checks12
import HSTZ.TauCetiFinite.Degrees.D15.Checks13
import HSTZ.TauCetiFinite.Degrees.D15.Checks14
import HSTZ.TauCetiFinite.Degrees.D15.Checks15
import HSTZ.TauCetiFinite.Degrees.D15.Checks16
import HSTZ.TauCetiFinite.Degrees.D15.Checks17
import HSTZ.TauCetiFinite.Degrees.D15.Checks18
import HSTZ.TauCetiFinite.Degrees.D15.Moments00
import HSTZ.TauCetiFinite.Degrees.D15.Moments01
import HSTZ.TauCetiFinite.Degrees.D15.Moments02
import HSTZ.TauCetiFinite.Degrees.D15.Moments03
import HSTZ.TauCetiFinite.Degrees.D15.Moments04
import HSTZ.TauCetiFinite.Degrees.D15.Moments05
import HSTZ.TauCetiFinite.Degrees.D15.Moments06
import HSTZ.TauCetiFinite.Degrees.D15.Moments07
import HSTZ.TauCetiFinite.Degrees.D15.Moments08
import HSTZ.TauCetiFinite.Degrees.D15.Moments09
import HSTZ.TauCetiFinite.Degrees.D15.Moments10
import HSTZ.TauCetiFinite.Degrees.D15.Moments11
import HSTZ.TauCetiFinite.Degrees.D15.Moments12
import HSTZ.TauCetiFinite.Degrees.D15.Moments13
import HSTZ.TauCetiFinite.Degrees.D15.Moments14
import HSTZ.TauCetiFinite.Degrees.D15.Moments15
import HSTZ.TauCetiFinite.Degrees.D15.Moments16
import HSTZ.TauCetiFinite.Degrees.D15.Moments17
import HSTZ.TauCetiFinite.Degrees.D15.Moments18
import HSTZ.TauCetiFinite.Degrees.D15.Moments19
import HSTZ.TauCetiFinite.Degrees.D15.Moments20
import HSTZ.TauCetiFinite.Degrees.D15.Moments21
import HSTZ.TauCetiFinite.Degrees.D15.Targets00
import HSTZ.TauCetiFinite.Degrees.D15.Targets01
import HSTZ.TauCetiFinite.Degrees.D15.Targets02
import HSTZ.TauCetiFinite.Degrees.D15.Targets03
import HSTZ.TauCetiFinite.Degrees.D15.Targets04
import HSTZ.TauCetiFinite.Degrees.D15.Targets05
import HSTZ.TauCetiFinite.Degrees.D15.Targets06
import HSTZ.TauCetiFinite.Degrees.D15.Targets07
import HSTZ.TauCetiFinite.Degrees.D15.Targets08
import HSTZ.TauCetiFinite.Degrees.D15.Targets09
import HSTZ.TauCetiFinite.Degrees.D15.Targets10

/-! The degree-15 finite character certificate, assembled from the modules in
`Degrees/D15/`, which are kept separate to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

local instance (xs : Shape) : Decidable (IsShape xs) := by
  unfold IsShape
  infer_instance

theorem table_checked : checkIndexedTable table = true := by
  unfold checkIndexedTable
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 148 := by simpa [table] using List.mem_range.mp hk
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
  · exact group88_checked
  · exact group89_checked
  · exact group90_checked
  · exact group91_checked
  · exact group92_checked
  · exact group93_checked
  · exact group94_checked
  · exact group95_checked
  · exact group96_checked
  · exact group97_checked
  · exact group98_checked
  · exact group99_checked
  · exact group100_checked
  · exact group101_checked
  · exact group102_checked
  · exact group103_checked
  · exact group104_checked
  · exact group105_checked
  · exact group106_checked
  · exact group107_checked
  · exact group108_checked
  · exact group109_checked
  · exact group110_checked
  · exact group111_checked
  · exact group112_checked
  · exact group113_checked
  · exact group114_checked
  · exact group115_checked
  · exact group116_checked
  · exact group117_checked
  · exact group118_checked
  · exact group119_checked
  · exact group120_checked
  · exact group121_checked
  · exact group122_checked
  · exact group123_checked
  · exact group124_checked
  · exact group125_checked
  · exact group126_checked
  · exact group127_checked
  · exact group128_checked
  · exact group129_checked
  · exact group130_checked
  · exact group131_checked
  · exact group132_checked
  · exact group133_checked
  · exact group134_checked
  · exact group135_checked
  · exact group136_checked
  · exact group137_checked
  · exact group138_checked
  · exact group139_checked
  · exact group140_checked
  · exact group141_checked
  · exact group142_checked
  · exact group143_checked
  · exact group144_checked
  · exact group145_checked
  · exact group146_checked
  · exact group147_checked

theorem classes_checked : checkClasses 15 classes = true := by
  apply checkClasses_of_facts
  · change (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))))))).Nodup
    exact (catalog_nodup_append classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))))))) (by decide) (catalog_nodup_append classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))))) (by decide) (catalog_nodup_append classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))))) (by decide) (catalog_nodup_append classSegment3 (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))) (by decide) (catalog_nodup_append classSegment4 (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))) (by decide) (catalog_nodup_append classSegment5 (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))) (by decide) (catalog_nodup_append classSegment6 (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))) (by decide) (catalog_nodup_append classSegment7 (classSegment8 ++ (classSegment9 ++ classSegment10)) (by decide) (catalog_nodup_append classSegment8 (classSegment9 ++ classSegment10) (by decide) (catalog_nodup_append classSegment9 classSegment10 (by decide) (by decide) (by change ∀ a ∈ classSegment9, a ∉ classSegment10; decide)) (by change ∀ a ∈ classSegment8, a ∉ (classSegment9 ++ classSegment10); decide)) (by change ∀ a ∈ classSegment7, a ∉ (classSegment8 ++ (classSegment9 ++ classSegment10)); decide)) (by change ∀ a ∈ classSegment6, a ∉ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))); decide)) (by change ∀ a ∈ classSegment5, a ∉ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))); decide)) (by change ∀ a ∈ classSegment4, a ∉ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))); decide)) (by change ∀ a ∈ classSegment3, a ∉ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))); decide)) (by change ∀ a ∈ classSegment2, a ∉ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))))); decide)) (by change ∀ a ∈ classSegment1, a ∉ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))))); decide)) (by change ∀ a ∈ classSegment0, a ∉ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))))))); decide))
  · change ∀ s ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))))))), IsShape s ∧ s.sum = 15
    exact (catalog_valid_append 15 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))))))) (by decide) (catalog_valid_append 15 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))))) (by decide) (catalog_valid_append 15 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))))) (by decide) (catalog_valid_append 15 classSegment3 (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))) (by decide) (catalog_valid_append 15 classSegment4 (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))) (by decide) (catalog_valid_append 15 classSegment5 (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))) (by decide) (catalog_valid_append 15 classSegment6 (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))) (by decide) (catalog_valid_append 15 classSegment7 (classSegment8 ++ (classSegment9 ++ classSegment10)) (by decide) (catalog_valid_append 15 classSegment8 (classSegment9 ++ classSegment10) (by decide) (catalog_valid_append 15 classSegment9 classSegment10 (by decide) (by decide)))))))))))
  · change 176 = partitionCount 15 15 15
    decide

theorem norm_checked : 2 * indexedNormSum table 15 classes refs49 = ((15 : ℕ).factorial : ℤ) := by
  change 2 * indexedNormSum table 15 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))))))) (refs49Segment0 ++ (refs49Segment1 ++ (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ (refs49Segment6 ++ (refs49Segment7 ++ (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10)))))))))) = ((15 : ℕ).factorial : ℤ)
  rw [indexedNormSum_append table 15 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))))))) refs49Segment0 (refs49Segment1 ++ (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ (refs49Segment6 ++ (refs49Segment7 ++ (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10))))))))) (by decide),
    indexedNormSum_append table 15 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))))) refs49Segment1 (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ (refs49Segment6 ++ (refs49Segment7 ++ (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10)))))))) (by decide),
    indexedNormSum_append table 15 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))))) refs49Segment2 (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ (refs49Segment6 ++ (refs49Segment7 ++ (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10))))))) (by decide),
    indexedNormSum_append table 15 classSegment3 (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))) refs49Segment3 (refs49Segment4 ++ (refs49Segment5 ++ (refs49Segment6 ++ (refs49Segment7 ++ (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10)))))) (by decide),
    indexedNormSum_append table 15 classSegment4 (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))))) refs49Segment4 (refs49Segment5 ++ (refs49Segment6 ++ (refs49Segment7 ++ (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10))))) (by decide),
    indexedNormSum_append table 15 classSegment5 (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))) refs49Segment5 (refs49Segment6 ++ (refs49Segment7 ++ (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10)))) (by decide),
    indexedNormSum_append table 15 classSegment6 (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10))) refs49Segment6 (refs49Segment7 ++ (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10))) (by decide),
    indexedNormSum_append table 15 classSegment7 (classSegment8 ++ (classSegment9 ++ classSegment10)) refs49Segment7 (refs49Segment8 ++ (refs49Segment9 ++ refs49Segment10)) (by decide),
    indexedNormSum_append table 15 classSegment8 (classSegment9 ++ classSegment10) refs49Segment8 (refs49Segment9 ++ refs49Segment10) (by decide),
    indexedNormSum_append table 15 classSegment9 classSegment10 refs49Segment9 refs49Segment10 (by decide)]
  decide

theorem targets_checked : ∀ nu ∈ classes, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 15 classes refs49 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  change nu ∈ (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ (classSegment6 ++ (classSegment7 ++ (classSegment8 ++ (classSegment9 ++ classSegment10)))))))))) at hnu
  simp only [List.mem_append] at hnu
  rcases hnu with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · exact targetsSegment0 nu h0
  · exact targetsSegment1 nu h1
  · exact targetsSegment2 nu h2
  · exact targetsSegment3 nu h3
  · exact targetsSegment4 nu h4
  · exact targetsSegment5 nu h5
  · exact targetsSegment6 nu h6
  · exact targetsSegment7 nu h7
  · exact targetsSegment8 nu h8
  · exact targetsSegment9 nu h9
  · exact targetsSegment10 nu h10

def witness : Nat.Partition 15 where
  parts := [7,5,2,1]
  parts_pos := by decide
  parts_sum := rfl

theorem witness_rows : partitionRows witness = [7,5,2,1] := by
  change ([7,5,2,1] : Multiset ℕ).sort (· ≥ ·) = [7,5,2,1]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simp)

theorem norm : evenNormNumerator witness = ((15 : ℕ).factorial : ℤ) := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs49 = true := by
    rw [witness_rows]; exact row49_checked
  rw [← indexedNorm_eq_evenNorm (by decide) table table_checked classes classes_checked witness refs49 hr]
  exact norm_checked

theorem cover_residue (nu : Nat.Partition 15) :
    evenCoverNumerator witness nu % 1000000007 ≠ 0 := by
  have hr : checkIndexedRow table (partitionRows witness) classes refs49 = true := by
    rw [witness_rows]; exact row49_checked
  obtain ⟨refs, hp, he⟩ := targets_checked (partitionRows nu)
    (checkClasses_complete classes classes_checked nu)
  rw [← indexedCover_eq_evenCover (by decide) table table_checked classes classes_checked witness nu refs49 refs hr hp]
  exact he

end HSTZ.TauCetiFinite.D15
#print axioms HSTZ.TauCetiFinite.D15.table_checked
#print axioms HSTZ.TauCetiFinite.D15.classes_checked
#print axioms HSTZ.TauCetiFinite.D15.norm_checked
#print axioms HSTZ.TauCetiFinite.D15.targets_checked
#print axioms HSTZ.TauCetiFinite.D15.norm
#print axioms HSTZ.TauCetiFinite.D15.cover_residue
