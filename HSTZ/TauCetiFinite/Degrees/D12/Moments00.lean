import HSTZ.TauCetiFinite.Degrees.D12.Segments

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem row0_checked : checkIndexedRow table [12] classes refs0 = true := by
  change checkIndexedRow table [12] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs0Segment0 ++ (refs0Segment1 ++ (refs0Segment2 ++ (refs0Segment3 ++ refs0Segment4)))) = true
  rw [checkIndexedRow_append table [12] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs0Segment0 (refs0Segment1 ++ (refs0Segment2 ++ (refs0Segment3 ++ refs0Segment4))) (by decide),
    checkIndexedRow_append table [12] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs0Segment1 (refs0Segment2 ++ (refs0Segment3 ++ refs0Segment4)) (by decide),
    checkIndexedRow_append table [12] classSegment2 (classSegment3 ++ classSegment4) refs0Segment2 (refs0Segment3 ++ refs0Segment4) (by decide),
    checkIndexedRow_append table [12] classSegment3 classSegment4 refs0Segment3 refs0Segment4 (by decide)]
  decide

theorem residue0_checked : (2 * indexedCoverSum table 12 classes refs33 refs0) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs0Segment0 ++ (refs0Segment1 ++ (refs0Segment2 ++ (refs0Segment3 ++ refs0Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs0Segment0 (refs0Segment1 ++ (refs0Segment2 ++ (refs0Segment3 ++ refs0Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs0Segment1 (refs0Segment2 ++ (refs0Segment3 ++ refs0Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs0Segment2 (refs0Segment3 ++ refs0Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs0Segment3 refs0Segment4 (by decide) (by decide)]
  decide

theorem row1_checked : checkIndexedRow table [11,1] classes refs1 = true := by
  change checkIndexedRow table [11,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs1Segment0 ++ (refs1Segment1 ++ (refs1Segment2 ++ (refs1Segment3 ++ refs1Segment4)))) = true
  rw [checkIndexedRow_append table [11,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs1Segment0 (refs1Segment1 ++ (refs1Segment2 ++ (refs1Segment3 ++ refs1Segment4))) (by decide),
    checkIndexedRow_append table [11,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs1Segment1 (refs1Segment2 ++ (refs1Segment3 ++ refs1Segment4)) (by decide),
    checkIndexedRow_append table [11,1] classSegment2 (classSegment3 ++ classSegment4) refs1Segment2 (refs1Segment3 ++ refs1Segment4) (by decide),
    checkIndexedRow_append table [11,1] classSegment3 classSegment4 refs1Segment3 refs1Segment4 (by decide)]
  decide

theorem residue1_checked : (2 * indexedCoverSum table 12 classes refs33 refs1) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs1Segment0 ++ (refs1Segment1 ++ (refs1Segment2 ++ (refs1Segment3 ++ refs1Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs1Segment0 (refs1Segment1 ++ (refs1Segment2 ++ (refs1Segment3 ++ refs1Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs1Segment1 (refs1Segment2 ++ (refs1Segment3 ++ refs1Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs1Segment2 (refs1Segment3 ++ refs1Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs1Segment3 refs1Segment4 (by decide) (by decide)]
  decide

theorem row2_checked : checkIndexedRow table [10,2] classes refs2 = true := by
  change checkIndexedRow table [10,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs2Segment0 ++ (refs2Segment1 ++ (refs2Segment2 ++ (refs2Segment3 ++ refs2Segment4)))) = true
  rw [checkIndexedRow_append table [10,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs2Segment0 (refs2Segment1 ++ (refs2Segment2 ++ (refs2Segment3 ++ refs2Segment4))) (by decide),
    checkIndexedRow_append table [10,2] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs2Segment1 (refs2Segment2 ++ (refs2Segment3 ++ refs2Segment4)) (by decide),
    checkIndexedRow_append table [10,2] classSegment2 (classSegment3 ++ classSegment4) refs2Segment2 (refs2Segment3 ++ refs2Segment4) (by decide),
    checkIndexedRow_append table [10,2] classSegment3 classSegment4 refs2Segment3 refs2Segment4 (by decide)]
  decide

theorem residue2_checked : (2 * indexedCoverSum table 12 classes refs33 refs2) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs2Segment0 ++ (refs2Segment1 ++ (refs2Segment2 ++ (refs2Segment3 ++ refs2Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs2Segment0 (refs2Segment1 ++ (refs2Segment2 ++ (refs2Segment3 ++ refs2Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs2Segment1 (refs2Segment2 ++ (refs2Segment3 ++ refs2Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs2Segment2 (refs2Segment3 ++ refs2Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs2Segment3 refs2Segment4 (by decide) (by decide)]
  decide

theorem row3_checked : checkIndexedRow table [10,1,1] classes refs3 = true := by
  change checkIndexedRow table [10,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs3Segment0 ++ (refs3Segment1 ++ (refs3Segment2 ++ (refs3Segment3 ++ refs3Segment4)))) = true
  rw [checkIndexedRow_append table [10,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs3Segment0 (refs3Segment1 ++ (refs3Segment2 ++ (refs3Segment3 ++ refs3Segment4))) (by decide),
    checkIndexedRow_append table [10,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs3Segment1 (refs3Segment2 ++ (refs3Segment3 ++ refs3Segment4)) (by decide),
    checkIndexedRow_append table [10,1,1] classSegment2 (classSegment3 ++ classSegment4) refs3Segment2 (refs3Segment3 ++ refs3Segment4) (by decide),
    checkIndexedRow_append table [10,1,1] classSegment3 classSegment4 refs3Segment3 refs3Segment4 (by decide)]
  decide

theorem residue3_checked : (2 * indexedCoverSum table 12 classes refs33 refs3) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs3Segment0 ++ (refs3Segment1 ++ (refs3Segment2 ++ (refs3Segment3 ++ refs3Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs3Segment0 (refs3Segment1 ++ (refs3Segment2 ++ (refs3Segment3 ++ refs3Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs3Segment1 (refs3Segment2 ++ (refs3Segment3 ++ refs3Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs3Segment2 (refs3Segment3 ++ refs3Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs3Segment3 refs3Segment4 (by decide) (by decide)]
  decide

theorem row4_checked : checkIndexedRow table [9,3] classes refs4 = true := by
  change checkIndexedRow table [9,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs4Segment0 ++ (refs4Segment1 ++ (refs4Segment2 ++ (refs4Segment3 ++ refs4Segment4)))) = true
  rw [checkIndexedRow_append table [9,3] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs4Segment0 (refs4Segment1 ++ (refs4Segment2 ++ (refs4Segment3 ++ refs4Segment4))) (by decide),
    checkIndexedRow_append table [9,3] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs4Segment1 (refs4Segment2 ++ (refs4Segment3 ++ refs4Segment4)) (by decide),
    checkIndexedRow_append table [9,3] classSegment2 (classSegment3 ++ classSegment4) refs4Segment2 (refs4Segment3 ++ refs4Segment4) (by decide),
    checkIndexedRow_append table [9,3] classSegment3 classSegment4 refs4Segment3 refs4Segment4 (by decide)]
  decide

theorem residue4_checked : (2 * indexedCoverSum table 12 classes refs33 refs4) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs4Segment0 ++ (refs4Segment1 ++ (refs4Segment2 ++ (refs4Segment3 ++ refs4Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs4Segment0 (refs4Segment1 ++ (refs4Segment2 ++ (refs4Segment3 ++ refs4Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs4Segment1 (refs4Segment2 ++ (refs4Segment3 ++ refs4Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs4Segment2 (refs4Segment3 ++ refs4Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs4Segment3 refs4Segment4 (by decide) (by decide)]
  decide

theorem row5_checked : checkIndexedRow table [9,2,1] classes refs5 = true := by
  change checkIndexedRow table [9,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs5Segment0 ++ (refs5Segment1 ++ (refs5Segment2 ++ (refs5Segment3 ++ refs5Segment4)))) = true
  rw [checkIndexedRow_append table [9,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs5Segment0 (refs5Segment1 ++ (refs5Segment2 ++ (refs5Segment3 ++ refs5Segment4))) (by decide),
    checkIndexedRow_append table [9,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs5Segment1 (refs5Segment2 ++ (refs5Segment3 ++ refs5Segment4)) (by decide),
    checkIndexedRow_append table [9,2,1] classSegment2 (classSegment3 ++ classSegment4) refs5Segment2 (refs5Segment3 ++ refs5Segment4) (by decide),
    checkIndexedRow_append table [9,2,1] classSegment3 classSegment4 refs5Segment3 refs5Segment4 (by decide)]
  decide

theorem residue5_checked : (2 * indexedCoverSum table 12 classes refs33 refs5) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs5Segment0 ++ (refs5Segment1 ++ (refs5Segment2 ++ (refs5Segment3 ++ refs5Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs5Segment0 (refs5Segment1 ++ (refs5Segment2 ++ (refs5Segment3 ++ refs5Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs5Segment1 (refs5Segment2 ++ (refs5Segment3 ++ refs5Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs5Segment2 (refs5Segment3 ++ refs5Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs5Segment3 refs5Segment4 (by decide) (by decide)]
  decide

theorem row6_checked : checkIndexedRow table [9,1,1,1] classes refs6 = true := by
  change checkIndexedRow table [9,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs6Segment0 ++ (refs6Segment1 ++ (refs6Segment2 ++ (refs6Segment3 ++ refs6Segment4)))) = true
  rw [checkIndexedRow_append table [9,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs6Segment0 (refs6Segment1 ++ (refs6Segment2 ++ (refs6Segment3 ++ refs6Segment4))) (by decide),
    checkIndexedRow_append table [9,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs6Segment1 (refs6Segment2 ++ (refs6Segment3 ++ refs6Segment4)) (by decide),
    checkIndexedRow_append table [9,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs6Segment2 (refs6Segment3 ++ refs6Segment4) (by decide),
    checkIndexedRow_append table [9,1,1,1] classSegment3 classSegment4 refs6Segment3 refs6Segment4 (by decide)]
  decide

theorem residue6_checked : (2 * indexedCoverSum table 12 classes refs33 refs6) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs6Segment0 ++ (refs6Segment1 ++ (refs6Segment2 ++ (refs6Segment3 ++ refs6Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs6Segment0 (refs6Segment1 ++ (refs6Segment2 ++ (refs6Segment3 ++ refs6Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs6Segment1 (refs6Segment2 ++ (refs6Segment3 ++ refs6Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs6Segment2 (refs6Segment3 ++ refs6Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs6Segment3 refs6Segment4 (by decide) (by decide)]
  decide

theorem row7_checked : checkIndexedRow table [8,4] classes refs7 = true := by
  change checkIndexedRow table [8,4] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs7Segment0 ++ (refs7Segment1 ++ (refs7Segment2 ++ (refs7Segment3 ++ refs7Segment4)))) = true
  rw [checkIndexedRow_append table [8,4] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs7Segment0 (refs7Segment1 ++ (refs7Segment2 ++ (refs7Segment3 ++ refs7Segment4))) (by decide),
    checkIndexedRow_append table [8,4] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs7Segment1 (refs7Segment2 ++ (refs7Segment3 ++ refs7Segment4)) (by decide),
    checkIndexedRow_append table [8,4] classSegment2 (classSegment3 ++ classSegment4) refs7Segment2 (refs7Segment3 ++ refs7Segment4) (by decide),
    checkIndexedRow_append table [8,4] classSegment3 classSegment4 refs7Segment3 refs7Segment4 (by decide)]
  decide

theorem residue7_checked : (2 * indexedCoverSum table 12 classes refs33 refs7) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs7Segment0 ++ (refs7Segment1 ++ (refs7Segment2 ++ (refs7Segment3 ++ refs7Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs7Segment0 (refs7Segment1 ++ (refs7Segment2 ++ (refs7Segment3 ++ refs7Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs7Segment1 (refs7Segment2 ++ (refs7Segment3 ++ refs7Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs7Segment2 (refs7Segment3 ++ refs7Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs7Segment3 refs7Segment4 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D12
