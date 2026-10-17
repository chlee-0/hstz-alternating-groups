import HSTZ.TauCetiFinite.Degrees.D11.Segments

/-! Part of the degree-11 finite character certificate (`HSTZ.TauCetiFinite.D11`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D11
open HSTZ.MurnaghanNakayama

theorem row16_checked : checkIndexedRow table [6,2,2,1] classes refs16 = true := by
  change checkIndexedRow table [6,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs16Segment0 ++ (refs16Segment1 ++ (refs16Segment2 ++ refs16Segment3))) = true
  rw [checkIndexedRow_append table [6,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs16Segment0 (refs16Segment1 ++ (refs16Segment2 ++ refs16Segment3)) (by decide),
    checkIndexedRow_append table [6,2,2,1] classSegment1 (classSegment2 ++ classSegment3) refs16Segment1 (refs16Segment2 ++ refs16Segment3) (by decide),
    checkIndexedRow_append table [6,2,2,1] classSegment2 classSegment3 refs16Segment2 refs16Segment3 (by decide)]
  decide

theorem residue16_checked : (2 * indexedCoverSum table 11 classes refs23 refs16) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs16Segment0 ++ (refs16Segment1 ++ (refs16Segment2 ++ refs16Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs16Segment0 (refs16Segment1 ++ (refs16Segment2 ++ refs16Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs16Segment1 (refs16Segment2 ++ refs16Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs16Segment2 refs16Segment3 (by decide) (by decide)]
  decide

theorem row17_checked : checkIndexedRow table [6,2,1,1,1] classes refs17 = true := by
  change checkIndexedRow table [6,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs17Segment0 ++ (refs17Segment1 ++ (refs17Segment2 ++ refs17Segment3))) = true
  rw [checkIndexedRow_append table [6,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs17Segment0 (refs17Segment1 ++ (refs17Segment2 ++ refs17Segment3)) (by decide),
    checkIndexedRow_append table [6,2,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs17Segment1 (refs17Segment2 ++ refs17Segment3) (by decide),
    checkIndexedRow_append table [6,2,1,1,1] classSegment2 classSegment3 refs17Segment2 refs17Segment3 (by decide)]
  decide

theorem residue17_checked : (2 * indexedCoverSum table 11 classes refs23 refs17) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs17Segment0 ++ (refs17Segment1 ++ (refs17Segment2 ++ refs17Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs17Segment0 (refs17Segment1 ++ (refs17Segment2 ++ refs17Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs17Segment1 (refs17Segment2 ++ refs17Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs17Segment2 refs17Segment3 (by decide) (by decide)]
  decide

theorem row18_checked : checkIndexedRow table [6,1,1,1,1,1] classes refs18 = true := by
  change checkIndexedRow table [6,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs18Segment0 ++ (refs18Segment1 ++ (refs18Segment2 ++ refs18Segment3))) = true
  rw [checkIndexedRow_append table [6,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs18Segment0 (refs18Segment1 ++ (refs18Segment2 ++ refs18Segment3)) (by decide),
    checkIndexedRow_append table [6,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs18Segment1 (refs18Segment2 ++ refs18Segment3) (by decide),
    checkIndexedRow_append table [6,1,1,1,1,1] classSegment2 classSegment3 refs18Segment2 refs18Segment3 (by decide)]
  decide

theorem residue18_checked : (2 * indexedCoverSum table 11 classes refs23 refs18) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs18Segment0 ++ (refs18Segment1 ++ (refs18Segment2 ++ refs18Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs18Segment0 (refs18Segment1 ++ (refs18Segment2 ++ refs18Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs18Segment1 (refs18Segment2 ++ refs18Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs18Segment2 refs18Segment3 (by decide) (by decide)]
  decide

theorem row19_checked : checkIndexedRow table [5,5,1] classes refs19 = true := by
  change checkIndexedRow table [5,5,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs19Segment0 ++ (refs19Segment1 ++ (refs19Segment2 ++ refs19Segment3))) = true
  rw [checkIndexedRow_append table [5,5,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs19Segment0 (refs19Segment1 ++ (refs19Segment2 ++ refs19Segment3)) (by decide),
    checkIndexedRow_append table [5,5,1] classSegment1 (classSegment2 ++ classSegment3) refs19Segment1 (refs19Segment2 ++ refs19Segment3) (by decide),
    checkIndexedRow_append table [5,5,1] classSegment2 classSegment3 refs19Segment2 refs19Segment3 (by decide)]
  decide

theorem residue19_checked : (2 * indexedCoverSum table 11 classes refs23 refs19) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs19Segment0 ++ (refs19Segment1 ++ (refs19Segment2 ++ refs19Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs19Segment0 (refs19Segment1 ++ (refs19Segment2 ++ refs19Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs19Segment1 (refs19Segment2 ++ refs19Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs19Segment2 refs19Segment3 (by decide) (by decide)]
  decide

theorem row20_checked : checkIndexedRow table [5,4,2] classes refs20 = true := by
  change checkIndexedRow table [5,4,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs20Segment0 ++ (refs20Segment1 ++ (refs20Segment2 ++ refs20Segment3))) = true
  rw [checkIndexedRow_append table [5,4,2] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs20Segment0 (refs20Segment1 ++ (refs20Segment2 ++ refs20Segment3)) (by decide),
    checkIndexedRow_append table [5,4,2] classSegment1 (classSegment2 ++ classSegment3) refs20Segment1 (refs20Segment2 ++ refs20Segment3) (by decide),
    checkIndexedRow_append table [5,4,2] classSegment2 classSegment3 refs20Segment2 refs20Segment3 (by decide)]
  decide

theorem residue20_checked : (2 * indexedCoverSum table 11 classes refs23 refs20) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs20Segment0 ++ (refs20Segment1 ++ (refs20Segment2 ++ refs20Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs20Segment0 (refs20Segment1 ++ (refs20Segment2 ++ refs20Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs20Segment1 (refs20Segment2 ++ refs20Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs20Segment2 refs20Segment3 (by decide) (by decide)]
  decide

theorem row21_checked : checkIndexedRow table [5,4,1,1] classes refs21 = true := by
  change checkIndexedRow table [5,4,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs21Segment0 ++ (refs21Segment1 ++ (refs21Segment2 ++ refs21Segment3))) = true
  rw [checkIndexedRow_append table [5,4,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs21Segment0 (refs21Segment1 ++ (refs21Segment2 ++ refs21Segment3)) (by decide),
    checkIndexedRow_append table [5,4,1,1] classSegment1 (classSegment2 ++ classSegment3) refs21Segment1 (refs21Segment2 ++ refs21Segment3) (by decide),
    checkIndexedRow_append table [5,4,1,1] classSegment2 classSegment3 refs21Segment2 refs21Segment3 (by decide)]
  decide

theorem residue21_checked : (2 * indexedCoverSum table 11 classes refs23 refs21) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs21Segment0 ++ (refs21Segment1 ++ (refs21Segment2 ++ refs21Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs21Segment0 (refs21Segment1 ++ (refs21Segment2 ++ refs21Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs21Segment1 (refs21Segment2 ++ refs21Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs21Segment2 refs21Segment3 (by decide) (by decide)]
  decide

theorem row22_checked : checkIndexedRow table [5,3,3] classes refs22 = true := by
  change checkIndexedRow table [5,3,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs22Segment0 ++ (refs22Segment1 ++ (refs22Segment2 ++ refs22Segment3))) = true
  rw [checkIndexedRow_append table [5,3,3] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs22Segment0 (refs22Segment1 ++ (refs22Segment2 ++ refs22Segment3)) (by decide),
    checkIndexedRow_append table [5,3,3] classSegment1 (classSegment2 ++ classSegment3) refs22Segment1 (refs22Segment2 ++ refs22Segment3) (by decide),
    checkIndexedRow_append table [5,3,3] classSegment2 classSegment3 refs22Segment2 refs22Segment3 (by decide)]
  decide

theorem residue22_checked : (2 * indexedCoverSum table 11 classes refs23 refs22) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs22Segment0 ++ (refs22Segment1 ++ (refs22Segment2 ++ refs22Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs22Segment0 (refs22Segment1 ++ (refs22Segment2 ++ refs22Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs22Segment1 (refs22Segment2 ++ refs22Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs22Segment2 refs22Segment3 (by decide) (by decide)]
  decide

theorem row23_checked : checkIndexedRow table [5,3,2,1] classes refs23 = true := by
  change checkIndexedRow table [5,3,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) = true
  rw [checkIndexedRow_append table [5,3,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) (by decide),
    checkIndexedRow_append table [5,3,2,1] classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) (by decide),
    checkIndexedRow_append table [5,3,2,1] classSegment2 classSegment3 refs23Segment2 refs23Segment3 (by decide)]
  decide

theorem residue23_checked : (2 * indexedCoverSum table 11 classes refs23 refs23) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs23Segment2 refs23Segment3 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D11
