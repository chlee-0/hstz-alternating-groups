import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row0_checked : checkIndexedRow table [13] classes refs0 = true := by
  change checkIndexedRow table [13] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs0Segment0 ++ (refs0Segment1 ++ (refs0Segment2 ++ (refs0Segment3 ++ (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6)))))) = true
  rw [checkIndexedRow_append table [13] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs0Segment0 (refs0Segment1 ++ (refs0Segment2 ++ (refs0Segment3 ++ (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6))))) (by decide),
    checkIndexedRow_append table [13] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs0Segment1 (refs0Segment2 ++ (refs0Segment3 ++ (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6)))) (by decide),
    checkIndexedRow_append table [13] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs0Segment2 (refs0Segment3 ++ (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6))) (by decide),
    checkIndexedRow_append table [13] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs0Segment3 (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6)) (by decide),
    checkIndexedRow_append table [13] classSegment4 (classSegment5 ++ classSegment6) refs0Segment4 (refs0Segment5 ++ refs0Segment6) (by decide),
    checkIndexedRow_append table [13] classSegment5 classSegment6 refs0Segment5 refs0Segment6 (by decide)]
  decide

theorem residue0_checked : (2 * indexedCoverSum table 13 classes refs34 refs0) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs0Segment0 ++ (refs0Segment1 ++ (refs0Segment2 ++ (refs0Segment3 ++ (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs0Segment0 (refs0Segment1 ++ (refs0Segment2 ++ (refs0Segment3 ++ (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs0Segment1 (refs0Segment2 ++ (refs0Segment3 ++ (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs0Segment2 (refs0Segment3 ++ (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs0Segment3 (refs0Segment4 ++ (refs0Segment5 ++ refs0Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs0Segment4 (refs0Segment5 ++ refs0Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs0Segment5 refs0Segment6 (by decide) (by decide)]
  decide

theorem row1_checked : checkIndexedRow table [12,1] classes refs1 = true := by
  change checkIndexedRow table [12,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs1Segment0 ++ (refs1Segment1 ++ (refs1Segment2 ++ (refs1Segment3 ++ (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6)))))) = true
  rw [checkIndexedRow_append table [12,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs1Segment0 (refs1Segment1 ++ (refs1Segment2 ++ (refs1Segment3 ++ (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6))))) (by decide),
    checkIndexedRow_append table [12,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs1Segment1 (refs1Segment2 ++ (refs1Segment3 ++ (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6)))) (by decide),
    checkIndexedRow_append table [12,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs1Segment2 (refs1Segment3 ++ (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6))) (by decide),
    checkIndexedRow_append table [12,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs1Segment3 (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6)) (by decide),
    checkIndexedRow_append table [12,1] classSegment4 (classSegment5 ++ classSegment6) refs1Segment4 (refs1Segment5 ++ refs1Segment6) (by decide),
    checkIndexedRow_append table [12,1] classSegment5 classSegment6 refs1Segment5 refs1Segment6 (by decide)]
  decide

theorem residue1_checked : (2 * indexedCoverSum table 13 classes refs34 refs1) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs1Segment0 ++ (refs1Segment1 ++ (refs1Segment2 ++ (refs1Segment3 ++ (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs1Segment0 (refs1Segment1 ++ (refs1Segment2 ++ (refs1Segment3 ++ (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs1Segment1 (refs1Segment2 ++ (refs1Segment3 ++ (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs1Segment2 (refs1Segment3 ++ (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs1Segment3 (refs1Segment4 ++ (refs1Segment5 ++ refs1Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs1Segment4 (refs1Segment5 ++ refs1Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs1Segment5 refs1Segment6 (by decide) (by decide)]
  decide

theorem row2_checked : checkIndexedRow table [11,2] classes refs2 = true := by
  change checkIndexedRow table [11,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs2Segment0 ++ (refs2Segment1 ++ (refs2Segment2 ++ (refs2Segment3 ++ (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6)))))) = true
  rw [checkIndexedRow_append table [11,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs2Segment0 (refs2Segment1 ++ (refs2Segment2 ++ (refs2Segment3 ++ (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6))))) (by decide),
    checkIndexedRow_append table [11,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs2Segment1 (refs2Segment2 ++ (refs2Segment3 ++ (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6)))) (by decide),
    checkIndexedRow_append table [11,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs2Segment2 (refs2Segment3 ++ (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6))) (by decide),
    checkIndexedRow_append table [11,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs2Segment3 (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6)) (by decide),
    checkIndexedRow_append table [11,2] classSegment4 (classSegment5 ++ classSegment6) refs2Segment4 (refs2Segment5 ++ refs2Segment6) (by decide),
    checkIndexedRow_append table [11,2] classSegment5 classSegment6 refs2Segment5 refs2Segment6 (by decide)]
  decide

theorem residue2_checked : (2 * indexedCoverSum table 13 classes refs34 refs2) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs2Segment0 ++ (refs2Segment1 ++ (refs2Segment2 ++ (refs2Segment3 ++ (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs2Segment0 (refs2Segment1 ++ (refs2Segment2 ++ (refs2Segment3 ++ (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs2Segment1 (refs2Segment2 ++ (refs2Segment3 ++ (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs2Segment2 (refs2Segment3 ++ (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs2Segment3 (refs2Segment4 ++ (refs2Segment5 ++ refs2Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs2Segment4 (refs2Segment5 ++ refs2Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs2Segment5 refs2Segment6 (by decide) (by decide)]
  decide

theorem row3_checked : checkIndexedRow table [11,1,1] classes refs3 = true := by
  change checkIndexedRow table [11,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs3Segment0 ++ (refs3Segment1 ++ (refs3Segment2 ++ (refs3Segment3 ++ (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6)))))) = true
  rw [checkIndexedRow_append table [11,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs3Segment0 (refs3Segment1 ++ (refs3Segment2 ++ (refs3Segment3 ++ (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6))))) (by decide),
    checkIndexedRow_append table [11,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs3Segment1 (refs3Segment2 ++ (refs3Segment3 ++ (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6)))) (by decide),
    checkIndexedRow_append table [11,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs3Segment2 (refs3Segment3 ++ (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6))) (by decide),
    checkIndexedRow_append table [11,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs3Segment3 (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6)) (by decide),
    checkIndexedRow_append table [11,1,1] classSegment4 (classSegment5 ++ classSegment6) refs3Segment4 (refs3Segment5 ++ refs3Segment6) (by decide),
    checkIndexedRow_append table [11,1,1] classSegment5 classSegment6 refs3Segment5 refs3Segment6 (by decide)]
  decide

theorem residue3_checked : (2 * indexedCoverSum table 13 classes refs34 refs3) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs3Segment0 ++ (refs3Segment1 ++ (refs3Segment2 ++ (refs3Segment3 ++ (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs3Segment0 (refs3Segment1 ++ (refs3Segment2 ++ (refs3Segment3 ++ (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs3Segment1 (refs3Segment2 ++ (refs3Segment3 ++ (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs3Segment2 (refs3Segment3 ++ (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs3Segment3 (refs3Segment4 ++ (refs3Segment5 ++ refs3Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs3Segment4 (refs3Segment5 ++ refs3Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs3Segment5 refs3Segment6 (by decide) (by decide)]
  decide

theorem row4_checked : checkIndexedRow table [10,3] classes refs4 = true := by
  change checkIndexedRow table [10,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs4Segment0 ++ (refs4Segment1 ++ (refs4Segment2 ++ (refs4Segment3 ++ (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6)))))) = true
  rw [checkIndexedRow_append table [10,3] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs4Segment0 (refs4Segment1 ++ (refs4Segment2 ++ (refs4Segment3 ++ (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6))))) (by decide),
    checkIndexedRow_append table [10,3] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs4Segment1 (refs4Segment2 ++ (refs4Segment3 ++ (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6)))) (by decide),
    checkIndexedRow_append table [10,3] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs4Segment2 (refs4Segment3 ++ (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6))) (by decide),
    checkIndexedRow_append table [10,3] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs4Segment3 (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6)) (by decide),
    checkIndexedRow_append table [10,3] classSegment4 (classSegment5 ++ classSegment6) refs4Segment4 (refs4Segment5 ++ refs4Segment6) (by decide),
    checkIndexedRow_append table [10,3] classSegment5 classSegment6 refs4Segment5 refs4Segment6 (by decide)]
  decide

theorem residue4_checked : (2 * indexedCoverSum table 13 classes refs34 refs4) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs4Segment0 ++ (refs4Segment1 ++ (refs4Segment2 ++ (refs4Segment3 ++ (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs4Segment0 (refs4Segment1 ++ (refs4Segment2 ++ (refs4Segment3 ++ (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs4Segment1 (refs4Segment2 ++ (refs4Segment3 ++ (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs4Segment2 (refs4Segment3 ++ (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs4Segment3 (refs4Segment4 ++ (refs4Segment5 ++ refs4Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs4Segment4 (refs4Segment5 ++ refs4Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs4Segment5 refs4Segment6 (by decide) (by decide)]
  decide

theorem row5_checked : checkIndexedRow table [10,2,1] classes refs5 = true := by
  change checkIndexedRow table [10,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs5Segment0 ++ (refs5Segment1 ++ (refs5Segment2 ++ (refs5Segment3 ++ (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6)))))) = true
  rw [checkIndexedRow_append table [10,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs5Segment0 (refs5Segment1 ++ (refs5Segment2 ++ (refs5Segment3 ++ (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6))))) (by decide),
    checkIndexedRow_append table [10,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs5Segment1 (refs5Segment2 ++ (refs5Segment3 ++ (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6)))) (by decide),
    checkIndexedRow_append table [10,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs5Segment2 (refs5Segment3 ++ (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6))) (by decide),
    checkIndexedRow_append table [10,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs5Segment3 (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6)) (by decide),
    checkIndexedRow_append table [10,2,1] classSegment4 (classSegment5 ++ classSegment6) refs5Segment4 (refs5Segment5 ++ refs5Segment6) (by decide),
    checkIndexedRow_append table [10,2,1] classSegment5 classSegment6 refs5Segment5 refs5Segment6 (by decide)]
  decide

theorem residue5_checked : (2 * indexedCoverSum table 13 classes refs34 refs5) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs5Segment0 ++ (refs5Segment1 ++ (refs5Segment2 ++ (refs5Segment3 ++ (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs5Segment0 (refs5Segment1 ++ (refs5Segment2 ++ (refs5Segment3 ++ (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs5Segment1 (refs5Segment2 ++ (refs5Segment3 ++ (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs5Segment2 (refs5Segment3 ++ (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs5Segment3 (refs5Segment4 ++ (refs5Segment5 ++ refs5Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs5Segment4 (refs5Segment5 ++ refs5Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs5Segment5 refs5Segment6 (by decide) (by decide)]
  decide

theorem row6_checked : checkIndexedRow table [10,1,1,1] classes refs6 = true := by
  change checkIndexedRow table [10,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs6Segment0 ++ (refs6Segment1 ++ (refs6Segment2 ++ (refs6Segment3 ++ (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6)))))) = true
  rw [checkIndexedRow_append table [10,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs6Segment0 (refs6Segment1 ++ (refs6Segment2 ++ (refs6Segment3 ++ (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6))))) (by decide),
    checkIndexedRow_append table [10,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs6Segment1 (refs6Segment2 ++ (refs6Segment3 ++ (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6)))) (by decide),
    checkIndexedRow_append table [10,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs6Segment2 (refs6Segment3 ++ (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6))) (by decide),
    checkIndexedRow_append table [10,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs6Segment3 (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6)) (by decide),
    checkIndexedRow_append table [10,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs6Segment4 (refs6Segment5 ++ refs6Segment6) (by decide),
    checkIndexedRow_append table [10,1,1,1] classSegment5 classSegment6 refs6Segment5 refs6Segment6 (by decide)]
  decide

theorem residue6_checked : (2 * indexedCoverSum table 13 classes refs34 refs6) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs6Segment0 ++ (refs6Segment1 ++ (refs6Segment2 ++ (refs6Segment3 ++ (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs6Segment0 (refs6Segment1 ++ (refs6Segment2 ++ (refs6Segment3 ++ (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs6Segment1 (refs6Segment2 ++ (refs6Segment3 ++ (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs6Segment2 (refs6Segment3 ++ (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs6Segment3 (refs6Segment4 ++ (refs6Segment5 ++ refs6Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs6Segment4 (refs6Segment5 ++ refs6Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs6Segment5 refs6Segment6 (by decide) (by decide)]
  decide

theorem row7_checked : checkIndexedRow table [9,4] classes refs7 = true := by
  change checkIndexedRow table [9,4] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs7Segment0 ++ (refs7Segment1 ++ (refs7Segment2 ++ (refs7Segment3 ++ (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6)))))) = true
  rw [checkIndexedRow_append table [9,4] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs7Segment0 (refs7Segment1 ++ (refs7Segment2 ++ (refs7Segment3 ++ (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6))))) (by decide),
    checkIndexedRow_append table [9,4] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs7Segment1 (refs7Segment2 ++ (refs7Segment3 ++ (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6)))) (by decide),
    checkIndexedRow_append table [9,4] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs7Segment2 (refs7Segment3 ++ (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6))) (by decide),
    checkIndexedRow_append table [9,4] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs7Segment3 (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6)) (by decide),
    checkIndexedRow_append table [9,4] classSegment4 (classSegment5 ++ classSegment6) refs7Segment4 (refs7Segment5 ++ refs7Segment6) (by decide),
    checkIndexedRow_append table [9,4] classSegment5 classSegment6 refs7Segment5 refs7Segment6 (by decide)]
  decide

theorem residue7_checked : (2 * indexedCoverSum table 13 classes refs34 refs7) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs7Segment0 ++ (refs7Segment1 ++ (refs7Segment2 ++ (refs7Segment3 ++ (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs7Segment0 (refs7Segment1 ++ (refs7Segment2 ++ (refs7Segment3 ++ (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs7Segment1 (refs7Segment2 ++ (refs7Segment3 ++ (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs7Segment2 (refs7Segment3 ++ (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs7Segment3 (refs7Segment4 ++ (refs7Segment5 ++ refs7Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs7Segment4 (refs7Segment5 ++ refs7Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs7Segment5 refs7Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
