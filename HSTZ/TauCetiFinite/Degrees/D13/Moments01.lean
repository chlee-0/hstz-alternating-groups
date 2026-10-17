import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row8_checked : checkIndexedRow table [9,3,1] classes refs8 = true := by
  change checkIndexedRow table [9,3,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs8Segment0 ++ (refs8Segment1 ++ (refs8Segment2 ++ (refs8Segment3 ++ (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6)))))) = true
  rw [checkIndexedRow_append table [9,3,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs8Segment0 (refs8Segment1 ++ (refs8Segment2 ++ (refs8Segment3 ++ (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6))))) (by decide),
    checkIndexedRow_append table [9,3,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs8Segment1 (refs8Segment2 ++ (refs8Segment3 ++ (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6)))) (by decide),
    checkIndexedRow_append table [9,3,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs8Segment2 (refs8Segment3 ++ (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6))) (by decide),
    checkIndexedRow_append table [9,3,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs8Segment3 (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6)) (by decide),
    checkIndexedRow_append table [9,3,1] classSegment4 (classSegment5 ++ classSegment6) refs8Segment4 (refs8Segment5 ++ refs8Segment6) (by decide),
    checkIndexedRow_append table [9,3,1] classSegment5 classSegment6 refs8Segment5 refs8Segment6 (by decide)]
  decide

theorem residue8_checked : (2 * indexedCoverSum table 13 classes refs34 refs8) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs8Segment0 ++ (refs8Segment1 ++ (refs8Segment2 ++ (refs8Segment3 ++ (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs8Segment0 (refs8Segment1 ++ (refs8Segment2 ++ (refs8Segment3 ++ (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs8Segment1 (refs8Segment2 ++ (refs8Segment3 ++ (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs8Segment2 (refs8Segment3 ++ (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs8Segment3 (refs8Segment4 ++ (refs8Segment5 ++ refs8Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs8Segment4 (refs8Segment5 ++ refs8Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs8Segment5 refs8Segment6 (by decide) (by decide)]
  decide

theorem row9_checked : checkIndexedRow table [9,2,2] classes refs9 = true := by
  change checkIndexedRow table [9,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs9Segment0 ++ (refs9Segment1 ++ (refs9Segment2 ++ (refs9Segment3 ++ (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6)))))) = true
  rw [checkIndexedRow_append table [9,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs9Segment0 (refs9Segment1 ++ (refs9Segment2 ++ (refs9Segment3 ++ (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6))))) (by decide),
    checkIndexedRow_append table [9,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs9Segment1 (refs9Segment2 ++ (refs9Segment3 ++ (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6)))) (by decide),
    checkIndexedRow_append table [9,2,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs9Segment2 (refs9Segment3 ++ (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6))) (by decide),
    checkIndexedRow_append table [9,2,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs9Segment3 (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6)) (by decide),
    checkIndexedRow_append table [9,2,2] classSegment4 (classSegment5 ++ classSegment6) refs9Segment4 (refs9Segment5 ++ refs9Segment6) (by decide),
    checkIndexedRow_append table [9,2,2] classSegment5 classSegment6 refs9Segment5 refs9Segment6 (by decide)]
  decide

theorem residue9_checked : (2 * indexedCoverSum table 13 classes refs34 refs9) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs9Segment0 ++ (refs9Segment1 ++ (refs9Segment2 ++ (refs9Segment3 ++ (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs9Segment0 (refs9Segment1 ++ (refs9Segment2 ++ (refs9Segment3 ++ (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs9Segment1 (refs9Segment2 ++ (refs9Segment3 ++ (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs9Segment2 (refs9Segment3 ++ (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs9Segment3 (refs9Segment4 ++ (refs9Segment5 ++ refs9Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs9Segment4 (refs9Segment5 ++ refs9Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs9Segment5 refs9Segment6 (by decide) (by decide)]
  decide

theorem row10_checked : checkIndexedRow table [9,2,1,1] classes refs10 = true := by
  change checkIndexedRow table [9,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs10Segment0 ++ (refs10Segment1 ++ (refs10Segment2 ++ (refs10Segment3 ++ (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6)))))) = true
  rw [checkIndexedRow_append table [9,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs10Segment0 (refs10Segment1 ++ (refs10Segment2 ++ (refs10Segment3 ++ (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6))))) (by decide),
    checkIndexedRow_append table [9,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs10Segment1 (refs10Segment2 ++ (refs10Segment3 ++ (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6)))) (by decide),
    checkIndexedRow_append table [9,2,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs10Segment2 (refs10Segment3 ++ (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6))) (by decide),
    checkIndexedRow_append table [9,2,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs10Segment3 (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6)) (by decide),
    checkIndexedRow_append table [9,2,1,1] classSegment4 (classSegment5 ++ classSegment6) refs10Segment4 (refs10Segment5 ++ refs10Segment6) (by decide),
    checkIndexedRow_append table [9,2,1,1] classSegment5 classSegment6 refs10Segment5 refs10Segment6 (by decide)]
  decide

theorem residue10_checked : (2 * indexedCoverSum table 13 classes refs34 refs10) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs10Segment0 ++ (refs10Segment1 ++ (refs10Segment2 ++ (refs10Segment3 ++ (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs10Segment0 (refs10Segment1 ++ (refs10Segment2 ++ (refs10Segment3 ++ (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs10Segment1 (refs10Segment2 ++ (refs10Segment3 ++ (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs10Segment2 (refs10Segment3 ++ (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs10Segment3 (refs10Segment4 ++ (refs10Segment5 ++ refs10Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs10Segment4 (refs10Segment5 ++ refs10Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs10Segment5 refs10Segment6 (by decide) (by decide)]
  decide

theorem row11_checked : checkIndexedRow table [9,1,1,1,1] classes refs11 = true := by
  change checkIndexedRow table [9,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs11Segment0 ++ (refs11Segment1 ++ (refs11Segment2 ++ (refs11Segment3 ++ (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6)))))) = true
  rw [checkIndexedRow_append table [9,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs11Segment0 (refs11Segment1 ++ (refs11Segment2 ++ (refs11Segment3 ++ (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6))))) (by decide),
    checkIndexedRow_append table [9,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs11Segment1 (refs11Segment2 ++ (refs11Segment3 ++ (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6)))) (by decide),
    checkIndexedRow_append table [9,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs11Segment2 (refs11Segment3 ++ (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6))) (by decide),
    checkIndexedRow_append table [9,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs11Segment3 (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6)) (by decide),
    checkIndexedRow_append table [9,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs11Segment4 (refs11Segment5 ++ refs11Segment6) (by decide),
    checkIndexedRow_append table [9,1,1,1,1] classSegment5 classSegment6 refs11Segment5 refs11Segment6 (by decide)]
  decide

theorem residue11_checked : (2 * indexedCoverSum table 13 classes refs34 refs11) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs11Segment0 ++ (refs11Segment1 ++ (refs11Segment2 ++ (refs11Segment3 ++ (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs11Segment0 (refs11Segment1 ++ (refs11Segment2 ++ (refs11Segment3 ++ (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs11Segment1 (refs11Segment2 ++ (refs11Segment3 ++ (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs11Segment2 (refs11Segment3 ++ (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs11Segment3 (refs11Segment4 ++ (refs11Segment5 ++ refs11Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs11Segment4 (refs11Segment5 ++ refs11Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs11Segment5 refs11Segment6 (by decide) (by decide)]
  decide

theorem row12_checked : checkIndexedRow table [8,5] classes refs12 = true := by
  change checkIndexedRow table [8,5] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs12Segment0 ++ (refs12Segment1 ++ (refs12Segment2 ++ (refs12Segment3 ++ (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6)))))) = true
  rw [checkIndexedRow_append table [8,5] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs12Segment0 (refs12Segment1 ++ (refs12Segment2 ++ (refs12Segment3 ++ (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6))))) (by decide),
    checkIndexedRow_append table [8,5] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs12Segment1 (refs12Segment2 ++ (refs12Segment3 ++ (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6)))) (by decide),
    checkIndexedRow_append table [8,5] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs12Segment2 (refs12Segment3 ++ (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6))) (by decide),
    checkIndexedRow_append table [8,5] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs12Segment3 (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6)) (by decide),
    checkIndexedRow_append table [8,5] classSegment4 (classSegment5 ++ classSegment6) refs12Segment4 (refs12Segment5 ++ refs12Segment6) (by decide),
    checkIndexedRow_append table [8,5] classSegment5 classSegment6 refs12Segment5 refs12Segment6 (by decide)]
  decide

theorem residue12_checked : (2 * indexedCoverSum table 13 classes refs34 refs12) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs12Segment0 ++ (refs12Segment1 ++ (refs12Segment2 ++ (refs12Segment3 ++ (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs12Segment0 (refs12Segment1 ++ (refs12Segment2 ++ (refs12Segment3 ++ (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs12Segment1 (refs12Segment2 ++ (refs12Segment3 ++ (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs12Segment2 (refs12Segment3 ++ (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs12Segment3 (refs12Segment4 ++ (refs12Segment5 ++ refs12Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs12Segment4 (refs12Segment5 ++ refs12Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs12Segment5 refs12Segment6 (by decide) (by decide)]
  decide

theorem row13_checked : checkIndexedRow table [8,4,1] classes refs13 = true := by
  change checkIndexedRow table [8,4,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs13Segment0 ++ (refs13Segment1 ++ (refs13Segment2 ++ (refs13Segment3 ++ (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6)))))) = true
  rw [checkIndexedRow_append table [8,4,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs13Segment0 (refs13Segment1 ++ (refs13Segment2 ++ (refs13Segment3 ++ (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6))))) (by decide),
    checkIndexedRow_append table [8,4,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs13Segment1 (refs13Segment2 ++ (refs13Segment3 ++ (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6)))) (by decide),
    checkIndexedRow_append table [8,4,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs13Segment2 (refs13Segment3 ++ (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6))) (by decide),
    checkIndexedRow_append table [8,4,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs13Segment3 (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6)) (by decide),
    checkIndexedRow_append table [8,4,1] classSegment4 (classSegment5 ++ classSegment6) refs13Segment4 (refs13Segment5 ++ refs13Segment6) (by decide),
    checkIndexedRow_append table [8,4,1] classSegment5 classSegment6 refs13Segment5 refs13Segment6 (by decide)]
  decide

theorem residue13_checked : (2 * indexedCoverSum table 13 classes refs34 refs13) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs13Segment0 ++ (refs13Segment1 ++ (refs13Segment2 ++ (refs13Segment3 ++ (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs13Segment0 (refs13Segment1 ++ (refs13Segment2 ++ (refs13Segment3 ++ (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs13Segment1 (refs13Segment2 ++ (refs13Segment3 ++ (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs13Segment2 (refs13Segment3 ++ (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs13Segment3 (refs13Segment4 ++ (refs13Segment5 ++ refs13Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs13Segment4 (refs13Segment5 ++ refs13Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs13Segment5 refs13Segment6 (by decide) (by decide)]
  decide

theorem row14_checked : checkIndexedRow table [8,3,2] classes refs14 = true := by
  change checkIndexedRow table [8,3,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs14Segment0 ++ (refs14Segment1 ++ (refs14Segment2 ++ (refs14Segment3 ++ (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6)))))) = true
  rw [checkIndexedRow_append table [8,3,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs14Segment0 (refs14Segment1 ++ (refs14Segment2 ++ (refs14Segment3 ++ (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6))))) (by decide),
    checkIndexedRow_append table [8,3,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs14Segment1 (refs14Segment2 ++ (refs14Segment3 ++ (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6)))) (by decide),
    checkIndexedRow_append table [8,3,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs14Segment2 (refs14Segment3 ++ (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6))) (by decide),
    checkIndexedRow_append table [8,3,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs14Segment3 (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6)) (by decide),
    checkIndexedRow_append table [8,3,2] classSegment4 (classSegment5 ++ classSegment6) refs14Segment4 (refs14Segment5 ++ refs14Segment6) (by decide),
    checkIndexedRow_append table [8,3,2] classSegment5 classSegment6 refs14Segment5 refs14Segment6 (by decide)]
  decide

theorem residue14_checked : (2 * indexedCoverSum table 13 classes refs34 refs14) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs14Segment0 ++ (refs14Segment1 ++ (refs14Segment2 ++ (refs14Segment3 ++ (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs14Segment0 (refs14Segment1 ++ (refs14Segment2 ++ (refs14Segment3 ++ (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs14Segment1 (refs14Segment2 ++ (refs14Segment3 ++ (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs14Segment2 (refs14Segment3 ++ (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs14Segment3 (refs14Segment4 ++ (refs14Segment5 ++ refs14Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs14Segment4 (refs14Segment5 ++ refs14Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs14Segment5 refs14Segment6 (by decide) (by decide)]
  decide

theorem row15_checked : checkIndexedRow table [8,3,1,1] classes refs15 = true := by
  change checkIndexedRow table [8,3,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs15Segment0 ++ (refs15Segment1 ++ (refs15Segment2 ++ (refs15Segment3 ++ (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6)))))) = true
  rw [checkIndexedRow_append table [8,3,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs15Segment0 (refs15Segment1 ++ (refs15Segment2 ++ (refs15Segment3 ++ (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6))))) (by decide),
    checkIndexedRow_append table [8,3,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs15Segment1 (refs15Segment2 ++ (refs15Segment3 ++ (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6)))) (by decide),
    checkIndexedRow_append table [8,3,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs15Segment2 (refs15Segment3 ++ (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6))) (by decide),
    checkIndexedRow_append table [8,3,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs15Segment3 (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6)) (by decide),
    checkIndexedRow_append table [8,3,1,1] classSegment4 (classSegment5 ++ classSegment6) refs15Segment4 (refs15Segment5 ++ refs15Segment6) (by decide),
    checkIndexedRow_append table [8,3,1,1] classSegment5 classSegment6 refs15Segment5 refs15Segment6 (by decide)]
  decide

theorem residue15_checked : (2 * indexedCoverSum table 13 classes refs34 refs15) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs15Segment0 ++ (refs15Segment1 ++ (refs15Segment2 ++ (refs15Segment3 ++ (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs15Segment0 (refs15Segment1 ++ (refs15Segment2 ++ (refs15Segment3 ++ (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs15Segment1 (refs15Segment2 ++ (refs15Segment3 ++ (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs15Segment2 (refs15Segment3 ++ (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs15Segment3 (refs15Segment4 ++ (refs15Segment5 ++ refs15Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs15Segment4 (refs15Segment5 ++ refs15Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs15Segment5 refs15Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
