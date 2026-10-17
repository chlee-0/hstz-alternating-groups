import HSTZ.TauCetiFinite.Degrees.D12.Segments

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem row56_checked : checkIndexedRow table [4,2,1,1,1,1,1,1] classes refs56 = true := by
  change checkIndexedRow table [4,2,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs56Segment0 ++ (refs56Segment1 ++ (refs56Segment2 ++ (refs56Segment3 ++ refs56Segment4)))) = true
  rw [checkIndexedRow_append table [4,2,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs56Segment0 (refs56Segment1 ++ (refs56Segment2 ++ (refs56Segment3 ++ refs56Segment4))) (by decide),
    checkIndexedRow_append table [4,2,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs56Segment1 (refs56Segment2 ++ (refs56Segment3 ++ refs56Segment4)) (by decide),
    checkIndexedRow_append table [4,2,1,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs56Segment2 (refs56Segment3 ++ refs56Segment4) (by decide),
    checkIndexedRow_append table [4,2,1,1,1,1,1,1] classSegment3 classSegment4 refs56Segment3 refs56Segment4 (by decide)]
  decide

theorem residue56_checked : (2 * indexedCoverSum table 12 classes refs33 refs56) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs56Segment0 ++ (refs56Segment1 ++ (refs56Segment2 ++ (refs56Segment3 ++ refs56Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs56Segment0 (refs56Segment1 ++ (refs56Segment2 ++ (refs56Segment3 ++ refs56Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs56Segment1 (refs56Segment2 ++ (refs56Segment3 ++ refs56Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs56Segment2 (refs56Segment3 ++ refs56Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs56Segment3 refs56Segment4 (by decide) (by decide)]
  decide

theorem row57_checked : checkIndexedRow table [4,1,1,1,1,1,1,1,1] classes refs57 = true := by
  change checkIndexedRow table [4,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs57Segment0 ++ (refs57Segment1 ++ (refs57Segment2 ++ (refs57Segment3 ++ refs57Segment4)))) = true
  rw [checkIndexedRow_append table [4,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs57Segment0 (refs57Segment1 ++ (refs57Segment2 ++ (refs57Segment3 ++ refs57Segment4))) (by decide),
    checkIndexedRow_append table [4,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs57Segment1 (refs57Segment2 ++ (refs57Segment3 ++ refs57Segment4)) (by decide),
    checkIndexedRow_append table [4,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs57Segment2 (refs57Segment3 ++ refs57Segment4) (by decide),
    checkIndexedRow_append table [4,1,1,1,1,1,1,1,1] classSegment3 classSegment4 refs57Segment3 refs57Segment4 (by decide)]
  decide

theorem residue57_checked : (2 * indexedCoverSum table 12 classes refs33 refs57) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs57Segment0 ++ (refs57Segment1 ++ (refs57Segment2 ++ (refs57Segment3 ++ refs57Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs57Segment0 (refs57Segment1 ++ (refs57Segment2 ++ (refs57Segment3 ++ refs57Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs57Segment1 (refs57Segment2 ++ (refs57Segment3 ++ refs57Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs57Segment2 (refs57Segment3 ++ refs57Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs57Segment3 refs57Segment4 (by decide) (by decide)]
  decide

theorem row58_checked : checkIndexedRow table [3,3,3,3] classes refs58 = true := by
  change checkIndexedRow table [3,3,3,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs58Segment0 ++ (refs58Segment1 ++ (refs58Segment2 ++ (refs58Segment3 ++ refs58Segment4)))) = true
  rw [checkIndexedRow_append table [3,3,3,3] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs58Segment0 (refs58Segment1 ++ (refs58Segment2 ++ (refs58Segment3 ++ refs58Segment4))) (by decide),
    checkIndexedRow_append table [3,3,3,3] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs58Segment1 (refs58Segment2 ++ (refs58Segment3 ++ refs58Segment4)) (by decide),
    checkIndexedRow_append table [3,3,3,3] classSegment2 (classSegment3 ++ classSegment4) refs58Segment2 (refs58Segment3 ++ refs58Segment4) (by decide),
    checkIndexedRow_append table [3,3,3,3] classSegment3 classSegment4 refs58Segment3 refs58Segment4 (by decide)]
  decide

theorem residue58_checked : (2 * indexedCoverSum table 12 classes refs33 refs58) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs58Segment0 ++ (refs58Segment1 ++ (refs58Segment2 ++ (refs58Segment3 ++ refs58Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs58Segment0 (refs58Segment1 ++ (refs58Segment2 ++ (refs58Segment3 ++ refs58Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs58Segment1 (refs58Segment2 ++ (refs58Segment3 ++ refs58Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs58Segment2 (refs58Segment3 ++ refs58Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs58Segment3 refs58Segment4 (by decide) (by decide)]
  decide

theorem row59_checked : checkIndexedRow table [3,3,3,2,1] classes refs59 = true := by
  change checkIndexedRow table [3,3,3,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs59Segment0 ++ (refs59Segment1 ++ (refs59Segment2 ++ (refs59Segment3 ++ refs59Segment4)))) = true
  rw [checkIndexedRow_append table [3,3,3,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs59Segment0 (refs59Segment1 ++ (refs59Segment2 ++ (refs59Segment3 ++ refs59Segment4))) (by decide),
    checkIndexedRow_append table [3,3,3,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs59Segment1 (refs59Segment2 ++ (refs59Segment3 ++ refs59Segment4)) (by decide),
    checkIndexedRow_append table [3,3,3,2,1] classSegment2 (classSegment3 ++ classSegment4) refs59Segment2 (refs59Segment3 ++ refs59Segment4) (by decide),
    checkIndexedRow_append table [3,3,3,2,1] classSegment3 classSegment4 refs59Segment3 refs59Segment4 (by decide)]
  decide

theorem residue59_checked : (2 * indexedCoverSum table 12 classes refs33 refs59) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs59Segment0 ++ (refs59Segment1 ++ (refs59Segment2 ++ (refs59Segment3 ++ refs59Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs59Segment0 (refs59Segment1 ++ (refs59Segment2 ++ (refs59Segment3 ++ refs59Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs59Segment1 (refs59Segment2 ++ (refs59Segment3 ++ refs59Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs59Segment2 (refs59Segment3 ++ refs59Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs59Segment3 refs59Segment4 (by decide) (by decide)]
  decide

theorem row60_checked : checkIndexedRow table [3,3,3,1,1,1] classes refs60 = true := by
  change checkIndexedRow table [3,3,3,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs60Segment0 ++ (refs60Segment1 ++ (refs60Segment2 ++ (refs60Segment3 ++ refs60Segment4)))) = true
  rw [checkIndexedRow_append table [3,3,3,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs60Segment0 (refs60Segment1 ++ (refs60Segment2 ++ (refs60Segment3 ++ refs60Segment4))) (by decide),
    checkIndexedRow_append table [3,3,3,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs60Segment1 (refs60Segment2 ++ (refs60Segment3 ++ refs60Segment4)) (by decide),
    checkIndexedRow_append table [3,3,3,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs60Segment2 (refs60Segment3 ++ refs60Segment4) (by decide),
    checkIndexedRow_append table [3,3,3,1,1,1] classSegment3 classSegment4 refs60Segment3 refs60Segment4 (by decide)]
  decide

theorem residue60_checked : (2 * indexedCoverSum table 12 classes refs33 refs60) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs60Segment0 ++ (refs60Segment1 ++ (refs60Segment2 ++ (refs60Segment3 ++ refs60Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs60Segment0 (refs60Segment1 ++ (refs60Segment2 ++ (refs60Segment3 ++ refs60Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs60Segment1 (refs60Segment2 ++ (refs60Segment3 ++ refs60Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs60Segment2 (refs60Segment3 ++ refs60Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs60Segment3 refs60Segment4 (by decide) (by decide)]
  decide

theorem row61_checked : checkIndexedRow table [3,3,2,2,2] classes refs61 = true := by
  change checkIndexedRow table [3,3,2,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs61Segment0 ++ (refs61Segment1 ++ (refs61Segment2 ++ (refs61Segment3 ++ refs61Segment4)))) = true
  rw [checkIndexedRow_append table [3,3,2,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs61Segment0 (refs61Segment1 ++ (refs61Segment2 ++ (refs61Segment3 ++ refs61Segment4))) (by decide),
    checkIndexedRow_append table [3,3,2,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs61Segment1 (refs61Segment2 ++ (refs61Segment3 ++ refs61Segment4)) (by decide),
    checkIndexedRow_append table [3,3,2,2,2] classSegment2 (classSegment3 ++ classSegment4) refs61Segment2 (refs61Segment3 ++ refs61Segment4) (by decide),
    checkIndexedRow_append table [3,3,2,2,2] classSegment3 classSegment4 refs61Segment3 refs61Segment4 (by decide)]
  decide

theorem residue61_checked : (2 * indexedCoverSum table 12 classes refs33 refs61) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs61Segment0 ++ (refs61Segment1 ++ (refs61Segment2 ++ (refs61Segment3 ++ refs61Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs61Segment0 (refs61Segment1 ++ (refs61Segment2 ++ (refs61Segment3 ++ refs61Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs61Segment1 (refs61Segment2 ++ (refs61Segment3 ++ refs61Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs61Segment2 (refs61Segment3 ++ refs61Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs61Segment3 refs61Segment4 (by decide) (by decide)]
  decide

theorem row62_checked : checkIndexedRow table [3,3,2,2,1,1] classes refs62 = true := by
  change checkIndexedRow table [3,3,2,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs62Segment0 ++ (refs62Segment1 ++ (refs62Segment2 ++ (refs62Segment3 ++ refs62Segment4)))) = true
  rw [checkIndexedRow_append table [3,3,2,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs62Segment0 (refs62Segment1 ++ (refs62Segment2 ++ (refs62Segment3 ++ refs62Segment4))) (by decide),
    checkIndexedRow_append table [3,3,2,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs62Segment1 (refs62Segment2 ++ (refs62Segment3 ++ refs62Segment4)) (by decide),
    checkIndexedRow_append table [3,3,2,2,1,1] classSegment2 (classSegment3 ++ classSegment4) refs62Segment2 (refs62Segment3 ++ refs62Segment4) (by decide),
    checkIndexedRow_append table [3,3,2,2,1,1] classSegment3 classSegment4 refs62Segment3 refs62Segment4 (by decide)]
  decide

theorem residue62_checked : (2 * indexedCoverSum table 12 classes refs33 refs62) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs62Segment0 ++ (refs62Segment1 ++ (refs62Segment2 ++ (refs62Segment3 ++ refs62Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs62Segment0 (refs62Segment1 ++ (refs62Segment2 ++ (refs62Segment3 ++ refs62Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs62Segment1 (refs62Segment2 ++ (refs62Segment3 ++ refs62Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs62Segment2 (refs62Segment3 ++ refs62Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs62Segment3 refs62Segment4 (by decide) (by decide)]
  decide

theorem row63_checked : checkIndexedRow table [3,3,2,1,1,1,1] classes refs63 = true := by
  change checkIndexedRow table [3,3,2,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs63Segment0 ++ (refs63Segment1 ++ (refs63Segment2 ++ (refs63Segment3 ++ refs63Segment4)))) = true
  rw [checkIndexedRow_append table [3,3,2,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs63Segment0 (refs63Segment1 ++ (refs63Segment2 ++ (refs63Segment3 ++ refs63Segment4))) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs63Segment1 (refs63Segment2 ++ (refs63Segment3 ++ refs63Segment4)) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs63Segment2 (refs63Segment3 ++ refs63Segment4) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1,1] classSegment3 classSegment4 refs63Segment3 refs63Segment4 (by decide)]
  decide

theorem residue63_checked : (2 * indexedCoverSum table 12 classes refs33 refs63) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs63Segment0 ++ (refs63Segment1 ++ (refs63Segment2 ++ (refs63Segment3 ++ refs63Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs63Segment0 (refs63Segment1 ++ (refs63Segment2 ++ (refs63Segment3 ++ refs63Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs63Segment1 (refs63Segment2 ++ (refs63Segment3 ++ refs63Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs63Segment2 (refs63Segment3 ++ refs63Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs63Segment3 refs63Segment4 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D12
