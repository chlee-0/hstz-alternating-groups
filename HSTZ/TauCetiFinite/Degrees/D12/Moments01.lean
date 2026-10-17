import HSTZ.TauCetiFinite.Degrees.D12.Segments

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem row8_checked : checkIndexedRow table [8,3,1] classes refs8 = true := by
  change checkIndexedRow table [8,3,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs8Segment0 ++ (refs8Segment1 ++ (refs8Segment2 ++ (refs8Segment3 ++ refs8Segment4)))) = true
  rw [checkIndexedRow_append table [8,3,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs8Segment0 (refs8Segment1 ++ (refs8Segment2 ++ (refs8Segment3 ++ refs8Segment4))) (by decide),
    checkIndexedRow_append table [8,3,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs8Segment1 (refs8Segment2 ++ (refs8Segment3 ++ refs8Segment4)) (by decide),
    checkIndexedRow_append table [8,3,1] classSegment2 (classSegment3 ++ classSegment4) refs8Segment2 (refs8Segment3 ++ refs8Segment4) (by decide),
    checkIndexedRow_append table [8,3,1] classSegment3 classSegment4 refs8Segment3 refs8Segment4 (by decide)]
  decide

theorem residue8_checked : (2 * indexedCoverSum table 12 classes refs33 refs8) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs8Segment0 ++ (refs8Segment1 ++ (refs8Segment2 ++ (refs8Segment3 ++ refs8Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs8Segment0 (refs8Segment1 ++ (refs8Segment2 ++ (refs8Segment3 ++ refs8Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs8Segment1 (refs8Segment2 ++ (refs8Segment3 ++ refs8Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs8Segment2 (refs8Segment3 ++ refs8Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs8Segment3 refs8Segment4 (by decide) (by decide)]
  decide

theorem row9_checked : checkIndexedRow table [8,2,2] classes refs9 = true := by
  change checkIndexedRow table [8,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs9Segment0 ++ (refs9Segment1 ++ (refs9Segment2 ++ (refs9Segment3 ++ refs9Segment4)))) = true
  rw [checkIndexedRow_append table [8,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs9Segment0 (refs9Segment1 ++ (refs9Segment2 ++ (refs9Segment3 ++ refs9Segment4))) (by decide),
    checkIndexedRow_append table [8,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs9Segment1 (refs9Segment2 ++ (refs9Segment3 ++ refs9Segment4)) (by decide),
    checkIndexedRow_append table [8,2,2] classSegment2 (classSegment3 ++ classSegment4) refs9Segment2 (refs9Segment3 ++ refs9Segment4) (by decide),
    checkIndexedRow_append table [8,2,2] classSegment3 classSegment4 refs9Segment3 refs9Segment4 (by decide)]
  decide

theorem residue9_checked : (2 * indexedCoverSum table 12 classes refs33 refs9) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs9Segment0 ++ (refs9Segment1 ++ (refs9Segment2 ++ (refs9Segment3 ++ refs9Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs9Segment0 (refs9Segment1 ++ (refs9Segment2 ++ (refs9Segment3 ++ refs9Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs9Segment1 (refs9Segment2 ++ (refs9Segment3 ++ refs9Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs9Segment2 (refs9Segment3 ++ refs9Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs9Segment3 refs9Segment4 (by decide) (by decide)]
  decide

theorem row10_checked : checkIndexedRow table [8,2,1,1] classes refs10 = true := by
  change checkIndexedRow table [8,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs10Segment0 ++ (refs10Segment1 ++ (refs10Segment2 ++ (refs10Segment3 ++ refs10Segment4)))) = true
  rw [checkIndexedRow_append table [8,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs10Segment0 (refs10Segment1 ++ (refs10Segment2 ++ (refs10Segment3 ++ refs10Segment4))) (by decide),
    checkIndexedRow_append table [8,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs10Segment1 (refs10Segment2 ++ (refs10Segment3 ++ refs10Segment4)) (by decide),
    checkIndexedRow_append table [8,2,1,1] classSegment2 (classSegment3 ++ classSegment4) refs10Segment2 (refs10Segment3 ++ refs10Segment4) (by decide),
    checkIndexedRow_append table [8,2,1,1] classSegment3 classSegment4 refs10Segment3 refs10Segment4 (by decide)]
  decide

theorem residue10_checked : (2 * indexedCoverSum table 12 classes refs33 refs10) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs10Segment0 ++ (refs10Segment1 ++ (refs10Segment2 ++ (refs10Segment3 ++ refs10Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs10Segment0 (refs10Segment1 ++ (refs10Segment2 ++ (refs10Segment3 ++ refs10Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs10Segment1 (refs10Segment2 ++ (refs10Segment3 ++ refs10Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs10Segment2 (refs10Segment3 ++ refs10Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs10Segment3 refs10Segment4 (by decide) (by decide)]
  decide

theorem row11_checked : checkIndexedRow table [8,1,1,1,1] classes refs11 = true := by
  change checkIndexedRow table [8,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs11Segment0 ++ (refs11Segment1 ++ (refs11Segment2 ++ (refs11Segment3 ++ refs11Segment4)))) = true
  rw [checkIndexedRow_append table [8,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs11Segment0 (refs11Segment1 ++ (refs11Segment2 ++ (refs11Segment3 ++ refs11Segment4))) (by decide),
    checkIndexedRow_append table [8,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs11Segment1 (refs11Segment2 ++ (refs11Segment3 ++ refs11Segment4)) (by decide),
    checkIndexedRow_append table [8,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs11Segment2 (refs11Segment3 ++ refs11Segment4) (by decide),
    checkIndexedRow_append table [8,1,1,1,1] classSegment3 classSegment4 refs11Segment3 refs11Segment4 (by decide)]
  decide

theorem residue11_checked : (2 * indexedCoverSum table 12 classes refs33 refs11) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs11Segment0 ++ (refs11Segment1 ++ (refs11Segment2 ++ (refs11Segment3 ++ refs11Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs11Segment0 (refs11Segment1 ++ (refs11Segment2 ++ (refs11Segment3 ++ refs11Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs11Segment1 (refs11Segment2 ++ (refs11Segment3 ++ refs11Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs11Segment2 (refs11Segment3 ++ refs11Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs11Segment3 refs11Segment4 (by decide) (by decide)]
  decide

theorem row12_checked : checkIndexedRow table [7,5] classes refs12 = true := by
  change checkIndexedRow table [7,5] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs12Segment0 ++ (refs12Segment1 ++ (refs12Segment2 ++ (refs12Segment3 ++ refs12Segment4)))) = true
  rw [checkIndexedRow_append table [7,5] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs12Segment0 (refs12Segment1 ++ (refs12Segment2 ++ (refs12Segment3 ++ refs12Segment4))) (by decide),
    checkIndexedRow_append table [7,5] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs12Segment1 (refs12Segment2 ++ (refs12Segment3 ++ refs12Segment4)) (by decide),
    checkIndexedRow_append table [7,5] classSegment2 (classSegment3 ++ classSegment4) refs12Segment2 (refs12Segment3 ++ refs12Segment4) (by decide),
    checkIndexedRow_append table [7,5] classSegment3 classSegment4 refs12Segment3 refs12Segment4 (by decide)]
  decide

theorem residue12_checked : (2 * indexedCoverSum table 12 classes refs33 refs12) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs12Segment0 ++ (refs12Segment1 ++ (refs12Segment2 ++ (refs12Segment3 ++ refs12Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs12Segment0 (refs12Segment1 ++ (refs12Segment2 ++ (refs12Segment3 ++ refs12Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs12Segment1 (refs12Segment2 ++ (refs12Segment3 ++ refs12Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs12Segment2 (refs12Segment3 ++ refs12Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs12Segment3 refs12Segment4 (by decide) (by decide)]
  decide

theorem row13_checked : checkIndexedRow table [7,4,1] classes refs13 = true := by
  change checkIndexedRow table [7,4,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs13Segment0 ++ (refs13Segment1 ++ (refs13Segment2 ++ (refs13Segment3 ++ refs13Segment4)))) = true
  rw [checkIndexedRow_append table [7,4,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs13Segment0 (refs13Segment1 ++ (refs13Segment2 ++ (refs13Segment3 ++ refs13Segment4))) (by decide),
    checkIndexedRow_append table [7,4,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs13Segment1 (refs13Segment2 ++ (refs13Segment3 ++ refs13Segment4)) (by decide),
    checkIndexedRow_append table [7,4,1] classSegment2 (classSegment3 ++ classSegment4) refs13Segment2 (refs13Segment3 ++ refs13Segment4) (by decide),
    checkIndexedRow_append table [7,4,1] classSegment3 classSegment4 refs13Segment3 refs13Segment4 (by decide)]
  decide

theorem residue13_checked : (2 * indexedCoverSum table 12 classes refs33 refs13) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs13Segment0 ++ (refs13Segment1 ++ (refs13Segment2 ++ (refs13Segment3 ++ refs13Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs13Segment0 (refs13Segment1 ++ (refs13Segment2 ++ (refs13Segment3 ++ refs13Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs13Segment1 (refs13Segment2 ++ (refs13Segment3 ++ refs13Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs13Segment2 (refs13Segment3 ++ refs13Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs13Segment3 refs13Segment4 (by decide) (by decide)]
  decide

theorem row14_checked : checkIndexedRow table [7,3,2] classes refs14 = true := by
  change checkIndexedRow table [7,3,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs14Segment0 ++ (refs14Segment1 ++ (refs14Segment2 ++ (refs14Segment3 ++ refs14Segment4)))) = true
  rw [checkIndexedRow_append table [7,3,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs14Segment0 (refs14Segment1 ++ (refs14Segment2 ++ (refs14Segment3 ++ refs14Segment4))) (by decide),
    checkIndexedRow_append table [7,3,2] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs14Segment1 (refs14Segment2 ++ (refs14Segment3 ++ refs14Segment4)) (by decide),
    checkIndexedRow_append table [7,3,2] classSegment2 (classSegment3 ++ classSegment4) refs14Segment2 (refs14Segment3 ++ refs14Segment4) (by decide),
    checkIndexedRow_append table [7,3,2] classSegment3 classSegment4 refs14Segment3 refs14Segment4 (by decide)]
  decide

theorem residue14_checked : (2 * indexedCoverSum table 12 classes refs33 refs14) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs14Segment0 ++ (refs14Segment1 ++ (refs14Segment2 ++ (refs14Segment3 ++ refs14Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs14Segment0 (refs14Segment1 ++ (refs14Segment2 ++ (refs14Segment3 ++ refs14Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs14Segment1 (refs14Segment2 ++ (refs14Segment3 ++ refs14Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs14Segment2 (refs14Segment3 ++ refs14Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs14Segment3 refs14Segment4 (by decide) (by decide)]
  decide

theorem row15_checked : checkIndexedRow table [7,3,1,1] classes refs15 = true := by
  change checkIndexedRow table [7,3,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs15Segment0 ++ (refs15Segment1 ++ (refs15Segment2 ++ (refs15Segment3 ++ refs15Segment4)))) = true
  rw [checkIndexedRow_append table [7,3,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs15Segment0 (refs15Segment1 ++ (refs15Segment2 ++ (refs15Segment3 ++ refs15Segment4))) (by decide),
    checkIndexedRow_append table [7,3,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs15Segment1 (refs15Segment2 ++ (refs15Segment3 ++ refs15Segment4)) (by decide),
    checkIndexedRow_append table [7,3,1,1] classSegment2 (classSegment3 ++ classSegment4) refs15Segment2 (refs15Segment3 ++ refs15Segment4) (by decide),
    checkIndexedRow_append table [7,3,1,1] classSegment3 classSegment4 refs15Segment3 refs15Segment4 (by decide)]
  decide

theorem residue15_checked : (2 * indexedCoverSum table 12 classes refs33 refs15) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs15Segment0 ++ (refs15Segment1 ++ (refs15Segment2 ++ (refs15Segment3 ++ refs15Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs15Segment0 (refs15Segment1 ++ (refs15Segment2 ++ (refs15Segment3 ++ refs15Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs15Segment1 (refs15Segment2 ++ (refs15Segment3 ++ refs15Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs15Segment2 (refs15Segment3 ++ refs15Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs15Segment3 refs15Segment4 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D12
