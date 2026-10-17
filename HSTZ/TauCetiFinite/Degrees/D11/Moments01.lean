import HSTZ.TauCetiFinite.Degrees.D11.Segments

/-! Part of the degree-11 finite character certificate (`HSTZ.TauCetiFinite.D11`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D11
open HSTZ.MurnaghanNakayama

theorem row8_checked : checkIndexedRow table [7,3,1] classes refs8 = true := by
  change checkIndexedRow table [7,3,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs8Segment0 ++ (refs8Segment1 ++ (refs8Segment2 ++ refs8Segment3))) = true
  rw [checkIndexedRow_append table [7,3,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs8Segment0 (refs8Segment1 ++ (refs8Segment2 ++ refs8Segment3)) (by decide),
    checkIndexedRow_append table [7,3,1] classSegment1 (classSegment2 ++ classSegment3) refs8Segment1 (refs8Segment2 ++ refs8Segment3) (by decide),
    checkIndexedRow_append table [7,3,1] classSegment2 classSegment3 refs8Segment2 refs8Segment3 (by decide)]
  decide

theorem residue8_checked : (2 * indexedCoverSum table 11 classes refs23 refs8) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs8Segment0 ++ (refs8Segment1 ++ (refs8Segment2 ++ refs8Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs8Segment0 (refs8Segment1 ++ (refs8Segment2 ++ refs8Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs8Segment1 (refs8Segment2 ++ refs8Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs8Segment2 refs8Segment3 (by decide) (by decide)]
  decide

theorem row9_checked : checkIndexedRow table [7,2,2] classes refs9 = true := by
  change checkIndexedRow table [7,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs9Segment0 ++ (refs9Segment1 ++ (refs9Segment2 ++ refs9Segment3))) = true
  rw [checkIndexedRow_append table [7,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs9Segment0 (refs9Segment1 ++ (refs9Segment2 ++ refs9Segment3)) (by decide),
    checkIndexedRow_append table [7,2,2] classSegment1 (classSegment2 ++ classSegment3) refs9Segment1 (refs9Segment2 ++ refs9Segment3) (by decide),
    checkIndexedRow_append table [7,2,2] classSegment2 classSegment3 refs9Segment2 refs9Segment3 (by decide)]
  decide

theorem residue9_checked : (2 * indexedCoverSum table 11 classes refs23 refs9) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs9Segment0 ++ (refs9Segment1 ++ (refs9Segment2 ++ refs9Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs9Segment0 (refs9Segment1 ++ (refs9Segment2 ++ refs9Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs9Segment1 (refs9Segment2 ++ refs9Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs9Segment2 refs9Segment3 (by decide) (by decide)]
  decide

theorem row10_checked : checkIndexedRow table [7,2,1,1] classes refs10 = true := by
  change checkIndexedRow table [7,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs10Segment0 ++ (refs10Segment1 ++ (refs10Segment2 ++ refs10Segment3))) = true
  rw [checkIndexedRow_append table [7,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs10Segment0 (refs10Segment1 ++ (refs10Segment2 ++ refs10Segment3)) (by decide),
    checkIndexedRow_append table [7,2,1,1] classSegment1 (classSegment2 ++ classSegment3) refs10Segment1 (refs10Segment2 ++ refs10Segment3) (by decide),
    checkIndexedRow_append table [7,2,1,1] classSegment2 classSegment3 refs10Segment2 refs10Segment3 (by decide)]
  decide

theorem residue10_checked : (2 * indexedCoverSum table 11 classes refs23 refs10) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs10Segment0 ++ (refs10Segment1 ++ (refs10Segment2 ++ refs10Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs10Segment0 (refs10Segment1 ++ (refs10Segment2 ++ refs10Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs10Segment1 (refs10Segment2 ++ refs10Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs10Segment2 refs10Segment3 (by decide) (by decide)]
  decide

theorem row11_checked : checkIndexedRow table [7,1,1,1,1] classes refs11 = true := by
  change checkIndexedRow table [7,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs11Segment0 ++ (refs11Segment1 ++ (refs11Segment2 ++ refs11Segment3))) = true
  rw [checkIndexedRow_append table [7,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs11Segment0 (refs11Segment1 ++ (refs11Segment2 ++ refs11Segment3)) (by decide),
    checkIndexedRow_append table [7,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs11Segment1 (refs11Segment2 ++ refs11Segment3) (by decide),
    checkIndexedRow_append table [7,1,1,1,1] classSegment2 classSegment3 refs11Segment2 refs11Segment3 (by decide)]
  decide

theorem residue11_checked : (2 * indexedCoverSum table 11 classes refs23 refs11) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs11Segment0 ++ (refs11Segment1 ++ (refs11Segment2 ++ refs11Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs11Segment0 (refs11Segment1 ++ (refs11Segment2 ++ refs11Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs11Segment1 (refs11Segment2 ++ refs11Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs11Segment2 refs11Segment3 (by decide) (by decide)]
  decide

theorem row12_checked : checkIndexedRow table [6,5] classes refs12 = true := by
  change checkIndexedRow table [6,5] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs12Segment0 ++ (refs12Segment1 ++ (refs12Segment2 ++ refs12Segment3))) = true
  rw [checkIndexedRow_append table [6,5] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs12Segment0 (refs12Segment1 ++ (refs12Segment2 ++ refs12Segment3)) (by decide),
    checkIndexedRow_append table [6,5] classSegment1 (classSegment2 ++ classSegment3) refs12Segment1 (refs12Segment2 ++ refs12Segment3) (by decide),
    checkIndexedRow_append table [6,5] classSegment2 classSegment3 refs12Segment2 refs12Segment3 (by decide)]
  decide

theorem residue12_checked : (2 * indexedCoverSum table 11 classes refs23 refs12) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs12Segment0 ++ (refs12Segment1 ++ (refs12Segment2 ++ refs12Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs12Segment0 (refs12Segment1 ++ (refs12Segment2 ++ refs12Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs12Segment1 (refs12Segment2 ++ refs12Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs12Segment2 refs12Segment3 (by decide) (by decide)]
  decide

theorem row13_checked : checkIndexedRow table [6,4,1] classes refs13 = true := by
  change checkIndexedRow table [6,4,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs13Segment0 ++ (refs13Segment1 ++ (refs13Segment2 ++ refs13Segment3))) = true
  rw [checkIndexedRow_append table [6,4,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs13Segment0 (refs13Segment1 ++ (refs13Segment2 ++ refs13Segment3)) (by decide),
    checkIndexedRow_append table [6,4,1] classSegment1 (classSegment2 ++ classSegment3) refs13Segment1 (refs13Segment2 ++ refs13Segment3) (by decide),
    checkIndexedRow_append table [6,4,1] classSegment2 classSegment3 refs13Segment2 refs13Segment3 (by decide)]
  decide

theorem residue13_checked : (2 * indexedCoverSum table 11 classes refs23 refs13) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs13Segment0 ++ (refs13Segment1 ++ (refs13Segment2 ++ refs13Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs13Segment0 (refs13Segment1 ++ (refs13Segment2 ++ refs13Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs13Segment1 (refs13Segment2 ++ refs13Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs13Segment2 refs13Segment3 (by decide) (by decide)]
  decide

theorem row14_checked : checkIndexedRow table [6,3,2] classes refs14 = true := by
  change checkIndexedRow table [6,3,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs14Segment0 ++ (refs14Segment1 ++ (refs14Segment2 ++ refs14Segment3))) = true
  rw [checkIndexedRow_append table [6,3,2] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs14Segment0 (refs14Segment1 ++ (refs14Segment2 ++ refs14Segment3)) (by decide),
    checkIndexedRow_append table [6,3,2] classSegment1 (classSegment2 ++ classSegment3) refs14Segment1 (refs14Segment2 ++ refs14Segment3) (by decide),
    checkIndexedRow_append table [6,3,2] classSegment2 classSegment3 refs14Segment2 refs14Segment3 (by decide)]
  decide

theorem residue14_checked : (2 * indexedCoverSum table 11 classes refs23 refs14) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs14Segment0 ++ (refs14Segment1 ++ (refs14Segment2 ++ refs14Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs14Segment0 (refs14Segment1 ++ (refs14Segment2 ++ refs14Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs14Segment1 (refs14Segment2 ++ refs14Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs14Segment2 refs14Segment3 (by decide) (by decide)]
  decide

theorem row15_checked : checkIndexedRow table [6,3,1,1] classes refs15 = true := by
  change checkIndexedRow table [6,3,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs15Segment0 ++ (refs15Segment1 ++ (refs15Segment2 ++ refs15Segment3))) = true
  rw [checkIndexedRow_append table [6,3,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs15Segment0 (refs15Segment1 ++ (refs15Segment2 ++ refs15Segment3)) (by decide),
    checkIndexedRow_append table [6,3,1,1] classSegment1 (classSegment2 ++ classSegment3) refs15Segment1 (refs15Segment2 ++ refs15Segment3) (by decide),
    checkIndexedRow_append table [6,3,1,1] classSegment2 classSegment3 refs15Segment2 refs15Segment3 (by decide)]
  decide

theorem residue15_checked : (2 * indexedCoverSum table 11 classes refs23 refs15) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs15Segment0 ++ (refs15Segment1 ++ (refs15Segment2 ++ refs15Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs15Segment0 (refs15Segment1 ++ (refs15Segment2 ++ refs15Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs15Segment1 (refs15Segment2 ++ refs15Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs15Segment2 refs15Segment3 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D11
