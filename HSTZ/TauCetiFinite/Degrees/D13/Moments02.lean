import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row16_checked : checkIndexedRow table [8,2,2,1] classes refs16 = true := by
  change checkIndexedRow table [8,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs16Segment0 ++ (refs16Segment1 ++ (refs16Segment2 ++ (refs16Segment3 ++ (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6)))))) = true
  rw [checkIndexedRow_append table [8,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs16Segment0 (refs16Segment1 ++ (refs16Segment2 ++ (refs16Segment3 ++ (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6))))) (by decide),
    checkIndexedRow_append table [8,2,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs16Segment1 (refs16Segment2 ++ (refs16Segment3 ++ (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6)))) (by decide),
    checkIndexedRow_append table [8,2,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs16Segment2 (refs16Segment3 ++ (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6))) (by decide),
    checkIndexedRow_append table [8,2,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs16Segment3 (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6)) (by decide),
    checkIndexedRow_append table [8,2,2,1] classSegment4 (classSegment5 ++ classSegment6) refs16Segment4 (refs16Segment5 ++ refs16Segment6) (by decide),
    checkIndexedRow_append table [8,2,2,1] classSegment5 classSegment6 refs16Segment5 refs16Segment6 (by decide)]
  decide

theorem residue16_checked : (2 * indexedCoverSum table 13 classes refs34 refs16) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs16Segment0 ++ (refs16Segment1 ++ (refs16Segment2 ++ (refs16Segment3 ++ (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs16Segment0 (refs16Segment1 ++ (refs16Segment2 ++ (refs16Segment3 ++ (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs16Segment1 (refs16Segment2 ++ (refs16Segment3 ++ (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs16Segment2 (refs16Segment3 ++ (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs16Segment3 (refs16Segment4 ++ (refs16Segment5 ++ refs16Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs16Segment4 (refs16Segment5 ++ refs16Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs16Segment5 refs16Segment6 (by decide) (by decide)]
  decide

theorem row17_checked : checkIndexedRow table [8,2,1,1,1] classes refs17 = true := by
  change checkIndexedRow table [8,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs17Segment0 ++ (refs17Segment1 ++ (refs17Segment2 ++ (refs17Segment3 ++ (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6)))))) = true
  rw [checkIndexedRow_append table [8,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs17Segment0 (refs17Segment1 ++ (refs17Segment2 ++ (refs17Segment3 ++ (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6))))) (by decide),
    checkIndexedRow_append table [8,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs17Segment1 (refs17Segment2 ++ (refs17Segment3 ++ (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6)))) (by decide),
    checkIndexedRow_append table [8,2,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs17Segment2 (refs17Segment3 ++ (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6))) (by decide),
    checkIndexedRow_append table [8,2,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs17Segment3 (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6)) (by decide),
    checkIndexedRow_append table [8,2,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs17Segment4 (refs17Segment5 ++ refs17Segment6) (by decide),
    checkIndexedRow_append table [8,2,1,1,1] classSegment5 classSegment6 refs17Segment5 refs17Segment6 (by decide)]
  decide

theorem residue17_checked : (2 * indexedCoverSum table 13 classes refs34 refs17) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs17Segment0 ++ (refs17Segment1 ++ (refs17Segment2 ++ (refs17Segment3 ++ (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs17Segment0 (refs17Segment1 ++ (refs17Segment2 ++ (refs17Segment3 ++ (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs17Segment1 (refs17Segment2 ++ (refs17Segment3 ++ (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs17Segment2 (refs17Segment3 ++ (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs17Segment3 (refs17Segment4 ++ (refs17Segment5 ++ refs17Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs17Segment4 (refs17Segment5 ++ refs17Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs17Segment5 refs17Segment6 (by decide) (by decide)]
  decide

theorem row18_checked : checkIndexedRow table [8,1,1,1,1,1] classes refs18 = true := by
  change checkIndexedRow table [8,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs18Segment0 ++ (refs18Segment1 ++ (refs18Segment2 ++ (refs18Segment3 ++ (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6)))))) = true
  rw [checkIndexedRow_append table [8,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs18Segment0 (refs18Segment1 ++ (refs18Segment2 ++ (refs18Segment3 ++ (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6))))) (by decide),
    checkIndexedRow_append table [8,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs18Segment1 (refs18Segment2 ++ (refs18Segment3 ++ (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6)))) (by decide),
    checkIndexedRow_append table [8,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs18Segment2 (refs18Segment3 ++ (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6))) (by decide),
    checkIndexedRow_append table [8,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs18Segment3 (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6)) (by decide),
    checkIndexedRow_append table [8,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs18Segment4 (refs18Segment5 ++ refs18Segment6) (by decide),
    checkIndexedRow_append table [8,1,1,1,1,1] classSegment5 classSegment6 refs18Segment5 refs18Segment6 (by decide)]
  decide

theorem residue18_checked : (2 * indexedCoverSum table 13 classes refs34 refs18) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs18Segment0 ++ (refs18Segment1 ++ (refs18Segment2 ++ (refs18Segment3 ++ (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs18Segment0 (refs18Segment1 ++ (refs18Segment2 ++ (refs18Segment3 ++ (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs18Segment1 (refs18Segment2 ++ (refs18Segment3 ++ (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs18Segment2 (refs18Segment3 ++ (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs18Segment3 (refs18Segment4 ++ (refs18Segment5 ++ refs18Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs18Segment4 (refs18Segment5 ++ refs18Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs18Segment5 refs18Segment6 (by decide) (by decide)]
  decide

theorem row19_checked : checkIndexedRow table [7,6] classes refs19 = true := by
  change checkIndexedRow table [7,6] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs19Segment0 ++ (refs19Segment1 ++ (refs19Segment2 ++ (refs19Segment3 ++ (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6)))))) = true
  rw [checkIndexedRow_append table [7,6] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs19Segment0 (refs19Segment1 ++ (refs19Segment2 ++ (refs19Segment3 ++ (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6))))) (by decide),
    checkIndexedRow_append table [7,6] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs19Segment1 (refs19Segment2 ++ (refs19Segment3 ++ (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6)))) (by decide),
    checkIndexedRow_append table [7,6] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs19Segment2 (refs19Segment3 ++ (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6))) (by decide),
    checkIndexedRow_append table [7,6] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs19Segment3 (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6)) (by decide),
    checkIndexedRow_append table [7,6] classSegment4 (classSegment5 ++ classSegment6) refs19Segment4 (refs19Segment5 ++ refs19Segment6) (by decide),
    checkIndexedRow_append table [7,6] classSegment5 classSegment6 refs19Segment5 refs19Segment6 (by decide)]
  decide

theorem residue19_checked : (2 * indexedCoverSum table 13 classes refs34 refs19) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs19Segment0 ++ (refs19Segment1 ++ (refs19Segment2 ++ (refs19Segment3 ++ (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs19Segment0 (refs19Segment1 ++ (refs19Segment2 ++ (refs19Segment3 ++ (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs19Segment1 (refs19Segment2 ++ (refs19Segment3 ++ (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs19Segment2 (refs19Segment3 ++ (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs19Segment3 (refs19Segment4 ++ (refs19Segment5 ++ refs19Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs19Segment4 (refs19Segment5 ++ refs19Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs19Segment5 refs19Segment6 (by decide) (by decide)]
  decide

theorem row20_checked : checkIndexedRow table [7,5,1] classes refs20 = true := by
  change checkIndexedRow table [7,5,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs20Segment0 ++ (refs20Segment1 ++ (refs20Segment2 ++ (refs20Segment3 ++ (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6)))))) = true
  rw [checkIndexedRow_append table [7,5,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs20Segment0 (refs20Segment1 ++ (refs20Segment2 ++ (refs20Segment3 ++ (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6))))) (by decide),
    checkIndexedRow_append table [7,5,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs20Segment1 (refs20Segment2 ++ (refs20Segment3 ++ (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6)))) (by decide),
    checkIndexedRow_append table [7,5,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs20Segment2 (refs20Segment3 ++ (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6))) (by decide),
    checkIndexedRow_append table [7,5,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs20Segment3 (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6)) (by decide),
    checkIndexedRow_append table [7,5,1] classSegment4 (classSegment5 ++ classSegment6) refs20Segment4 (refs20Segment5 ++ refs20Segment6) (by decide),
    checkIndexedRow_append table [7,5,1] classSegment5 classSegment6 refs20Segment5 refs20Segment6 (by decide)]
  decide

theorem residue20_checked : (2 * indexedCoverSum table 13 classes refs34 refs20) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs20Segment0 ++ (refs20Segment1 ++ (refs20Segment2 ++ (refs20Segment3 ++ (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs20Segment0 (refs20Segment1 ++ (refs20Segment2 ++ (refs20Segment3 ++ (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs20Segment1 (refs20Segment2 ++ (refs20Segment3 ++ (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs20Segment2 (refs20Segment3 ++ (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs20Segment3 (refs20Segment4 ++ (refs20Segment5 ++ refs20Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs20Segment4 (refs20Segment5 ++ refs20Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs20Segment5 refs20Segment6 (by decide) (by decide)]
  decide

theorem row21_checked : checkIndexedRow table [7,4,2] classes refs21 = true := by
  change checkIndexedRow table [7,4,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs21Segment0 ++ (refs21Segment1 ++ (refs21Segment2 ++ (refs21Segment3 ++ (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6)))))) = true
  rw [checkIndexedRow_append table [7,4,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs21Segment0 (refs21Segment1 ++ (refs21Segment2 ++ (refs21Segment3 ++ (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6))))) (by decide),
    checkIndexedRow_append table [7,4,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs21Segment1 (refs21Segment2 ++ (refs21Segment3 ++ (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6)))) (by decide),
    checkIndexedRow_append table [7,4,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs21Segment2 (refs21Segment3 ++ (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6))) (by decide),
    checkIndexedRow_append table [7,4,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs21Segment3 (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6)) (by decide),
    checkIndexedRow_append table [7,4,2] classSegment4 (classSegment5 ++ classSegment6) refs21Segment4 (refs21Segment5 ++ refs21Segment6) (by decide),
    checkIndexedRow_append table [7,4,2] classSegment5 classSegment6 refs21Segment5 refs21Segment6 (by decide)]
  decide

theorem residue21_checked : (2 * indexedCoverSum table 13 classes refs34 refs21) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs21Segment0 ++ (refs21Segment1 ++ (refs21Segment2 ++ (refs21Segment3 ++ (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs21Segment0 (refs21Segment1 ++ (refs21Segment2 ++ (refs21Segment3 ++ (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs21Segment1 (refs21Segment2 ++ (refs21Segment3 ++ (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs21Segment2 (refs21Segment3 ++ (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs21Segment3 (refs21Segment4 ++ (refs21Segment5 ++ refs21Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs21Segment4 (refs21Segment5 ++ refs21Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs21Segment5 refs21Segment6 (by decide) (by decide)]
  decide

theorem row22_checked : checkIndexedRow table [7,4,1,1] classes refs22 = true := by
  change checkIndexedRow table [7,4,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs22Segment0 ++ (refs22Segment1 ++ (refs22Segment2 ++ (refs22Segment3 ++ (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6)))))) = true
  rw [checkIndexedRow_append table [7,4,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs22Segment0 (refs22Segment1 ++ (refs22Segment2 ++ (refs22Segment3 ++ (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6))))) (by decide),
    checkIndexedRow_append table [7,4,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs22Segment1 (refs22Segment2 ++ (refs22Segment3 ++ (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6)))) (by decide),
    checkIndexedRow_append table [7,4,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs22Segment2 (refs22Segment3 ++ (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6))) (by decide),
    checkIndexedRow_append table [7,4,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs22Segment3 (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6)) (by decide),
    checkIndexedRow_append table [7,4,1,1] classSegment4 (classSegment5 ++ classSegment6) refs22Segment4 (refs22Segment5 ++ refs22Segment6) (by decide),
    checkIndexedRow_append table [7,4,1,1] classSegment5 classSegment6 refs22Segment5 refs22Segment6 (by decide)]
  decide

theorem residue22_checked : (2 * indexedCoverSum table 13 classes refs34 refs22) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs22Segment0 ++ (refs22Segment1 ++ (refs22Segment2 ++ (refs22Segment3 ++ (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs22Segment0 (refs22Segment1 ++ (refs22Segment2 ++ (refs22Segment3 ++ (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs22Segment1 (refs22Segment2 ++ (refs22Segment3 ++ (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs22Segment2 (refs22Segment3 ++ (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs22Segment3 (refs22Segment4 ++ (refs22Segment5 ++ refs22Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs22Segment4 (refs22Segment5 ++ refs22Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs22Segment5 refs22Segment6 (by decide) (by decide)]
  decide

theorem row23_checked : checkIndexedRow table [7,3,3] classes refs23 = true := by
  change checkIndexedRow table [7,3,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ (refs23Segment3 ++ (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6)))))) = true
  rw [checkIndexedRow_append table [7,3,3] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ (refs23Segment3 ++ (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6))))) (by decide),
    checkIndexedRow_append table [7,3,3] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs23Segment1 (refs23Segment2 ++ (refs23Segment3 ++ (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6)))) (by decide),
    checkIndexedRow_append table [7,3,3] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs23Segment2 (refs23Segment3 ++ (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6))) (by decide),
    checkIndexedRow_append table [7,3,3] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs23Segment3 (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6)) (by decide),
    checkIndexedRow_append table [7,3,3] classSegment4 (classSegment5 ++ classSegment6) refs23Segment4 (refs23Segment5 ++ refs23Segment6) (by decide),
    checkIndexedRow_append table [7,3,3] classSegment5 classSegment6 refs23Segment5 refs23Segment6 (by decide)]
  decide

theorem residue23_checked : (2 * indexedCoverSum table 13 classes refs34 refs23) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ (refs23Segment3 ++ (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ (refs23Segment3 ++ (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs23Segment1 (refs23Segment2 ++ (refs23Segment3 ++ (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs23Segment2 (refs23Segment3 ++ (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs23Segment3 (refs23Segment4 ++ (refs23Segment5 ++ refs23Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs23Segment4 (refs23Segment5 ++ refs23Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs23Segment5 refs23Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
