import HSTZ.TauCetiFinite.Degrees.D12.Segments

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem row16_checked : checkIndexedRow table [7,2,2,1] classes refs16 = true := by
  change checkIndexedRow table [7,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs16Segment0 ++ (refs16Segment1 ++ (refs16Segment2 ++ (refs16Segment3 ++ refs16Segment4)))) = true
  rw [checkIndexedRow_append table [7,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs16Segment0 (refs16Segment1 ++ (refs16Segment2 ++ (refs16Segment3 ++ refs16Segment4))) (by decide),
    checkIndexedRow_append table [7,2,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs16Segment1 (refs16Segment2 ++ (refs16Segment3 ++ refs16Segment4)) (by decide),
    checkIndexedRow_append table [7,2,2,1] classSegment2 (classSegment3 ++ classSegment4) refs16Segment2 (refs16Segment3 ++ refs16Segment4) (by decide),
    checkIndexedRow_append table [7,2,2,1] classSegment3 classSegment4 refs16Segment3 refs16Segment4 (by decide)]
  decide

theorem residue16_checked : (2 * indexedCoverSum table 12 classes refs33 refs16) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs16Segment0 ++ (refs16Segment1 ++ (refs16Segment2 ++ (refs16Segment3 ++ refs16Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs16Segment0 (refs16Segment1 ++ (refs16Segment2 ++ (refs16Segment3 ++ refs16Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs16Segment1 (refs16Segment2 ++ (refs16Segment3 ++ refs16Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs16Segment2 (refs16Segment3 ++ refs16Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs16Segment3 refs16Segment4 (by decide) (by decide)]
  decide

theorem row17_checked : checkIndexedRow table [7,2,1,1,1] classes refs17 = true := by
  change checkIndexedRow table [7,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs17Segment0 ++ (refs17Segment1 ++ (refs17Segment2 ++ (refs17Segment3 ++ refs17Segment4)))) = true
  rw [checkIndexedRow_append table [7,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs17Segment0 (refs17Segment1 ++ (refs17Segment2 ++ (refs17Segment3 ++ refs17Segment4))) (by decide),
    checkIndexedRow_append table [7,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs17Segment1 (refs17Segment2 ++ (refs17Segment3 ++ refs17Segment4)) (by decide),
    checkIndexedRow_append table [7,2,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs17Segment2 (refs17Segment3 ++ refs17Segment4) (by decide),
    checkIndexedRow_append table [7,2,1,1,1] classSegment3 classSegment4 refs17Segment3 refs17Segment4 (by decide)]
  decide

theorem residue17_checked : (2 * indexedCoverSum table 12 classes refs33 refs17) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs17Segment0 ++ (refs17Segment1 ++ (refs17Segment2 ++ (refs17Segment3 ++ refs17Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs17Segment0 (refs17Segment1 ++ (refs17Segment2 ++ (refs17Segment3 ++ refs17Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs17Segment1 (refs17Segment2 ++ (refs17Segment3 ++ refs17Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs17Segment2 (refs17Segment3 ++ refs17Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs17Segment3 refs17Segment4 (by decide) (by decide)]
  decide

theorem row18_checked : checkIndexedRow table [7,1,1,1,1,1] classes refs18 = true := by
  change checkIndexedRow table [7,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs18Segment0 ++ (refs18Segment1 ++ (refs18Segment2 ++ (refs18Segment3 ++ refs18Segment4)))) = true
  rw [checkIndexedRow_append table [7,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs18Segment0 (refs18Segment1 ++ (refs18Segment2 ++ (refs18Segment3 ++ refs18Segment4))) (by decide),
    checkIndexedRow_append table [7,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs18Segment1 (refs18Segment2 ++ (refs18Segment3 ++ refs18Segment4)) (by decide),
    checkIndexedRow_append table [7,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs18Segment2 (refs18Segment3 ++ refs18Segment4) (by decide),
    checkIndexedRow_append table [7,1,1,1,1,1] classSegment3 classSegment4 refs18Segment3 refs18Segment4 (by decide)]
  decide

theorem residue18_checked : (2 * indexedCoverSum table 12 classes refs33 refs18) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs18Segment0 ++ (refs18Segment1 ++ (refs18Segment2 ++ (refs18Segment3 ++ refs18Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs18Segment0 (refs18Segment1 ++ (refs18Segment2 ++ (refs18Segment3 ++ refs18Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs18Segment1 (refs18Segment2 ++ (refs18Segment3 ++ refs18Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs18Segment2 (refs18Segment3 ++ refs18Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs18Segment3 refs18Segment4 (by decide) (by decide)]
  decide

theorem row19_checked : checkIndexedRow table [6,6] classes refs19 = true := by
  change checkIndexedRow table [6,6] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs19Segment0 ++ (refs19Segment1 ++ (refs19Segment2 ++ (refs19Segment3 ++ refs19Segment4)))) = true
  rw [checkIndexedRow_append table [6,6] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs19Segment0 (refs19Segment1 ++ (refs19Segment2 ++ (refs19Segment3 ++ refs19Segment4))) (by decide),
    checkIndexedRow_append table [6,6] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs19Segment1 (refs19Segment2 ++ (refs19Segment3 ++ refs19Segment4)) (by decide),
    checkIndexedRow_append table [6,6] classSegment2 (classSegment3 ++ classSegment4) refs19Segment2 (refs19Segment3 ++ refs19Segment4) (by decide),
    checkIndexedRow_append table [6,6] classSegment3 classSegment4 refs19Segment3 refs19Segment4 (by decide)]
  decide

theorem residue19_checked : (2 * indexedCoverSum table 12 classes refs33 refs19) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs19Segment0 ++ (refs19Segment1 ++ (refs19Segment2 ++ (refs19Segment3 ++ refs19Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs19Segment0 (refs19Segment1 ++ (refs19Segment2 ++ (refs19Segment3 ++ refs19Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs19Segment1 (refs19Segment2 ++ (refs19Segment3 ++ refs19Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs19Segment2 (refs19Segment3 ++ refs19Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs19Segment3 refs19Segment4 (by decide) (by decide)]
  decide

theorem row20_checked : checkIndexedRow table [6,5,1] classes refs20 = true := by
  change checkIndexedRow table [6,5,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs20Segment0 ++ (refs20Segment1 ++ (refs20Segment2 ++ (refs20Segment3 ++ refs20Segment4)))) = true
  rw [checkIndexedRow_append table [6,5,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs20Segment0 (refs20Segment1 ++ (refs20Segment2 ++ (refs20Segment3 ++ refs20Segment4))) (by decide),
    checkIndexedRow_append table [6,5,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs20Segment1 (refs20Segment2 ++ (refs20Segment3 ++ refs20Segment4)) (by decide),
    checkIndexedRow_append table [6,5,1] classSegment2 (classSegment3 ++ classSegment4) refs20Segment2 (refs20Segment3 ++ refs20Segment4) (by decide),
    checkIndexedRow_append table [6,5,1] classSegment3 classSegment4 refs20Segment3 refs20Segment4 (by decide)]
  decide

theorem residue20_checked : (2 * indexedCoverSum table 12 classes refs33 refs20) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs20Segment0 ++ (refs20Segment1 ++ (refs20Segment2 ++ (refs20Segment3 ++ refs20Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs20Segment0 (refs20Segment1 ++ (refs20Segment2 ++ (refs20Segment3 ++ refs20Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs20Segment1 (refs20Segment2 ++ (refs20Segment3 ++ refs20Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs20Segment2 (refs20Segment3 ++ refs20Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs20Segment3 refs20Segment4 (by decide) (by decide)]
  decide

theorem row21_checked : checkIndexedRow table [6,4,2] classes refs21 = true := by
  change checkIndexedRow table [6,4,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs21Segment0 ++ (refs21Segment1 ++ (refs21Segment2 ++ (refs21Segment3 ++ refs21Segment4)))) = true
  rw [checkIndexedRow_append table [6,4,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs21Segment0 (refs21Segment1 ++ (refs21Segment2 ++ (refs21Segment3 ++ refs21Segment4))) (by decide),
    checkIndexedRow_append table [6,4,2] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs21Segment1 (refs21Segment2 ++ (refs21Segment3 ++ refs21Segment4)) (by decide),
    checkIndexedRow_append table [6,4,2] classSegment2 (classSegment3 ++ classSegment4) refs21Segment2 (refs21Segment3 ++ refs21Segment4) (by decide),
    checkIndexedRow_append table [6,4,2] classSegment3 classSegment4 refs21Segment3 refs21Segment4 (by decide)]
  decide

theorem residue21_checked : (2 * indexedCoverSum table 12 classes refs33 refs21) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs21Segment0 ++ (refs21Segment1 ++ (refs21Segment2 ++ (refs21Segment3 ++ refs21Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs21Segment0 (refs21Segment1 ++ (refs21Segment2 ++ (refs21Segment3 ++ refs21Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs21Segment1 (refs21Segment2 ++ (refs21Segment3 ++ refs21Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs21Segment2 (refs21Segment3 ++ refs21Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs21Segment3 refs21Segment4 (by decide) (by decide)]
  decide

theorem row22_checked : checkIndexedRow table [6,4,1,1] classes refs22 = true := by
  change checkIndexedRow table [6,4,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs22Segment0 ++ (refs22Segment1 ++ (refs22Segment2 ++ (refs22Segment3 ++ refs22Segment4)))) = true
  rw [checkIndexedRow_append table [6,4,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs22Segment0 (refs22Segment1 ++ (refs22Segment2 ++ (refs22Segment3 ++ refs22Segment4))) (by decide),
    checkIndexedRow_append table [6,4,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs22Segment1 (refs22Segment2 ++ (refs22Segment3 ++ refs22Segment4)) (by decide),
    checkIndexedRow_append table [6,4,1,1] classSegment2 (classSegment3 ++ classSegment4) refs22Segment2 (refs22Segment3 ++ refs22Segment4) (by decide),
    checkIndexedRow_append table [6,4,1,1] classSegment3 classSegment4 refs22Segment3 refs22Segment4 (by decide)]
  decide

theorem residue22_checked : (2 * indexedCoverSum table 12 classes refs33 refs22) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs22Segment0 ++ (refs22Segment1 ++ (refs22Segment2 ++ (refs22Segment3 ++ refs22Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs22Segment0 (refs22Segment1 ++ (refs22Segment2 ++ (refs22Segment3 ++ refs22Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs22Segment1 (refs22Segment2 ++ (refs22Segment3 ++ refs22Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs22Segment2 (refs22Segment3 ++ refs22Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs22Segment3 refs22Segment4 (by decide) (by decide)]
  decide

theorem row23_checked : checkIndexedRow table [6,3,3] classes refs23 = true := by
  change checkIndexedRow table [6,3,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ (refs23Segment3 ++ refs23Segment4)))) = true
  rw [checkIndexedRow_append table [6,3,3] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ (refs23Segment3 ++ refs23Segment4))) (by decide),
    checkIndexedRow_append table [6,3,3] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs23Segment1 (refs23Segment2 ++ (refs23Segment3 ++ refs23Segment4)) (by decide),
    checkIndexedRow_append table [6,3,3] classSegment2 (classSegment3 ++ classSegment4) refs23Segment2 (refs23Segment3 ++ refs23Segment4) (by decide),
    checkIndexedRow_append table [6,3,3] classSegment3 classSegment4 refs23Segment3 refs23Segment4 (by decide)]
  decide

theorem residue23_checked : (2 * indexedCoverSum table 12 classes refs33 refs23) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ (refs23Segment3 ++ refs23Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ (refs23Segment3 ++ refs23Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs23Segment1 (refs23Segment2 ++ (refs23Segment3 ++ refs23Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs23Segment2 (refs23Segment3 ++ refs23Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs23Segment3 refs23Segment4 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D12
