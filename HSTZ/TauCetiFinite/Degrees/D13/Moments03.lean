import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row24_checked : checkIndexedRow table [7,3,2,1] classes refs24 = true := by
  change checkIndexedRow table [7,3,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs24Segment0 ++ (refs24Segment1 ++ (refs24Segment2 ++ (refs24Segment3 ++ (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6)))))) = true
  rw [checkIndexedRow_append table [7,3,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs24Segment0 (refs24Segment1 ++ (refs24Segment2 ++ (refs24Segment3 ++ (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6))))) (by decide),
    checkIndexedRow_append table [7,3,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs24Segment1 (refs24Segment2 ++ (refs24Segment3 ++ (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6)))) (by decide),
    checkIndexedRow_append table [7,3,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs24Segment2 (refs24Segment3 ++ (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6))) (by decide),
    checkIndexedRow_append table [7,3,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs24Segment3 (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6)) (by decide),
    checkIndexedRow_append table [7,3,2,1] classSegment4 (classSegment5 ++ classSegment6) refs24Segment4 (refs24Segment5 ++ refs24Segment6) (by decide),
    checkIndexedRow_append table [7,3,2,1] classSegment5 classSegment6 refs24Segment5 refs24Segment6 (by decide)]
  decide

theorem residue24_checked : (2 * indexedCoverSum table 13 classes refs34 refs24) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs24Segment0 ++ (refs24Segment1 ++ (refs24Segment2 ++ (refs24Segment3 ++ (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs24Segment0 (refs24Segment1 ++ (refs24Segment2 ++ (refs24Segment3 ++ (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs24Segment1 (refs24Segment2 ++ (refs24Segment3 ++ (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs24Segment2 (refs24Segment3 ++ (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs24Segment3 (refs24Segment4 ++ (refs24Segment5 ++ refs24Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs24Segment4 (refs24Segment5 ++ refs24Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs24Segment5 refs24Segment6 (by decide) (by decide)]
  decide

theorem row25_checked : checkIndexedRow table [7,3,1,1,1] classes refs25 = true := by
  change checkIndexedRow table [7,3,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs25Segment0 ++ (refs25Segment1 ++ (refs25Segment2 ++ (refs25Segment3 ++ (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6)))))) = true
  rw [checkIndexedRow_append table [7,3,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs25Segment0 (refs25Segment1 ++ (refs25Segment2 ++ (refs25Segment3 ++ (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6))))) (by decide),
    checkIndexedRow_append table [7,3,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs25Segment1 (refs25Segment2 ++ (refs25Segment3 ++ (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6)))) (by decide),
    checkIndexedRow_append table [7,3,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs25Segment2 (refs25Segment3 ++ (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6))) (by decide),
    checkIndexedRow_append table [7,3,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs25Segment3 (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6)) (by decide),
    checkIndexedRow_append table [7,3,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs25Segment4 (refs25Segment5 ++ refs25Segment6) (by decide),
    checkIndexedRow_append table [7,3,1,1,1] classSegment5 classSegment6 refs25Segment5 refs25Segment6 (by decide)]
  decide

theorem residue25_checked : (2 * indexedCoverSum table 13 classes refs34 refs25) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs25Segment0 ++ (refs25Segment1 ++ (refs25Segment2 ++ (refs25Segment3 ++ (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs25Segment0 (refs25Segment1 ++ (refs25Segment2 ++ (refs25Segment3 ++ (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs25Segment1 (refs25Segment2 ++ (refs25Segment3 ++ (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs25Segment2 (refs25Segment3 ++ (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs25Segment3 (refs25Segment4 ++ (refs25Segment5 ++ refs25Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs25Segment4 (refs25Segment5 ++ refs25Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs25Segment5 refs25Segment6 (by decide) (by decide)]
  decide

theorem row26_checked : checkIndexedRow table [7,2,2,2] classes refs26 = true := by
  change checkIndexedRow table [7,2,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs26Segment0 ++ (refs26Segment1 ++ (refs26Segment2 ++ (refs26Segment3 ++ (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6)))))) = true
  rw [checkIndexedRow_append table [7,2,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs26Segment0 (refs26Segment1 ++ (refs26Segment2 ++ (refs26Segment3 ++ (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6))))) (by decide),
    checkIndexedRow_append table [7,2,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs26Segment1 (refs26Segment2 ++ (refs26Segment3 ++ (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6)))) (by decide),
    checkIndexedRow_append table [7,2,2,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs26Segment2 (refs26Segment3 ++ (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6))) (by decide),
    checkIndexedRow_append table [7,2,2,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs26Segment3 (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6)) (by decide),
    checkIndexedRow_append table [7,2,2,2] classSegment4 (classSegment5 ++ classSegment6) refs26Segment4 (refs26Segment5 ++ refs26Segment6) (by decide),
    checkIndexedRow_append table [7,2,2,2] classSegment5 classSegment6 refs26Segment5 refs26Segment6 (by decide)]
  decide

theorem residue26_checked : (2 * indexedCoverSum table 13 classes refs34 refs26) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs26Segment0 ++ (refs26Segment1 ++ (refs26Segment2 ++ (refs26Segment3 ++ (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs26Segment0 (refs26Segment1 ++ (refs26Segment2 ++ (refs26Segment3 ++ (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs26Segment1 (refs26Segment2 ++ (refs26Segment3 ++ (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs26Segment2 (refs26Segment3 ++ (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs26Segment3 (refs26Segment4 ++ (refs26Segment5 ++ refs26Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs26Segment4 (refs26Segment5 ++ refs26Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs26Segment5 refs26Segment6 (by decide) (by decide)]
  decide

theorem row27_checked : checkIndexedRow table [7,2,2,1,1] classes refs27 = true := by
  change checkIndexedRow table [7,2,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs27Segment0 ++ (refs27Segment1 ++ (refs27Segment2 ++ (refs27Segment3 ++ (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6)))))) = true
  rw [checkIndexedRow_append table [7,2,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs27Segment0 (refs27Segment1 ++ (refs27Segment2 ++ (refs27Segment3 ++ (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6))))) (by decide),
    checkIndexedRow_append table [7,2,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs27Segment1 (refs27Segment2 ++ (refs27Segment3 ++ (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6)))) (by decide),
    checkIndexedRow_append table [7,2,2,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs27Segment2 (refs27Segment3 ++ (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6))) (by decide),
    checkIndexedRow_append table [7,2,2,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs27Segment3 (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6)) (by decide),
    checkIndexedRow_append table [7,2,2,1,1] classSegment4 (classSegment5 ++ classSegment6) refs27Segment4 (refs27Segment5 ++ refs27Segment6) (by decide),
    checkIndexedRow_append table [7,2,2,1,1] classSegment5 classSegment6 refs27Segment5 refs27Segment6 (by decide)]
  decide

theorem residue27_checked : (2 * indexedCoverSum table 13 classes refs34 refs27) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs27Segment0 ++ (refs27Segment1 ++ (refs27Segment2 ++ (refs27Segment3 ++ (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs27Segment0 (refs27Segment1 ++ (refs27Segment2 ++ (refs27Segment3 ++ (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs27Segment1 (refs27Segment2 ++ (refs27Segment3 ++ (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs27Segment2 (refs27Segment3 ++ (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs27Segment3 (refs27Segment4 ++ (refs27Segment5 ++ refs27Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs27Segment4 (refs27Segment5 ++ refs27Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs27Segment5 refs27Segment6 (by decide) (by decide)]
  decide

theorem row28_checked : checkIndexedRow table [7,2,1,1,1,1] classes refs28 = true := by
  change checkIndexedRow table [7,2,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs28Segment0 ++ (refs28Segment1 ++ (refs28Segment2 ++ (refs28Segment3 ++ (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6)))))) = true
  rw [checkIndexedRow_append table [7,2,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs28Segment0 (refs28Segment1 ++ (refs28Segment2 ++ (refs28Segment3 ++ (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6))))) (by decide),
    checkIndexedRow_append table [7,2,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs28Segment1 (refs28Segment2 ++ (refs28Segment3 ++ (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6)))) (by decide),
    checkIndexedRow_append table [7,2,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs28Segment2 (refs28Segment3 ++ (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6))) (by decide),
    checkIndexedRow_append table [7,2,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs28Segment3 (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6)) (by decide),
    checkIndexedRow_append table [7,2,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs28Segment4 (refs28Segment5 ++ refs28Segment6) (by decide),
    checkIndexedRow_append table [7,2,1,1,1,1] classSegment5 classSegment6 refs28Segment5 refs28Segment6 (by decide)]
  decide

theorem residue28_checked : (2 * indexedCoverSum table 13 classes refs34 refs28) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs28Segment0 ++ (refs28Segment1 ++ (refs28Segment2 ++ (refs28Segment3 ++ (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs28Segment0 (refs28Segment1 ++ (refs28Segment2 ++ (refs28Segment3 ++ (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs28Segment1 (refs28Segment2 ++ (refs28Segment3 ++ (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs28Segment2 (refs28Segment3 ++ (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs28Segment3 (refs28Segment4 ++ (refs28Segment5 ++ refs28Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs28Segment4 (refs28Segment5 ++ refs28Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs28Segment5 refs28Segment6 (by decide) (by decide)]
  decide

theorem row29_checked : checkIndexedRow table [7,1,1,1,1,1,1] classes refs29 = true := by
  change checkIndexedRow table [7,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs29Segment0 ++ (refs29Segment1 ++ (refs29Segment2 ++ (refs29Segment3 ++ (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6)))))) = true
  rw [checkIndexedRow_append table [7,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs29Segment0 (refs29Segment1 ++ (refs29Segment2 ++ (refs29Segment3 ++ (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6))))) (by decide),
    checkIndexedRow_append table [7,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs29Segment1 (refs29Segment2 ++ (refs29Segment3 ++ (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6)))) (by decide),
    checkIndexedRow_append table [7,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs29Segment2 (refs29Segment3 ++ (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6))) (by decide),
    checkIndexedRow_append table [7,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs29Segment3 (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6)) (by decide),
    checkIndexedRow_append table [7,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs29Segment4 (refs29Segment5 ++ refs29Segment6) (by decide),
    checkIndexedRow_append table [7,1,1,1,1,1,1] classSegment5 classSegment6 refs29Segment5 refs29Segment6 (by decide)]
  decide

theorem residue29_checked : (2 * indexedCoverSum table 13 classes refs34 refs29) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs29Segment0 ++ (refs29Segment1 ++ (refs29Segment2 ++ (refs29Segment3 ++ (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs29Segment0 (refs29Segment1 ++ (refs29Segment2 ++ (refs29Segment3 ++ (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs29Segment1 (refs29Segment2 ++ (refs29Segment3 ++ (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs29Segment2 (refs29Segment3 ++ (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs29Segment3 (refs29Segment4 ++ (refs29Segment5 ++ refs29Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs29Segment4 (refs29Segment5 ++ refs29Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs29Segment5 refs29Segment6 (by decide) (by decide)]
  decide

theorem row30_checked : checkIndexedRow table [6,6,1] classes refs30 = true := by
  change checkIndexedRow table [6,6,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs30Segment0 ++ (refs30Segment1 ++ (refs30Segment2 ++ (refs30Segment3 ++ (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6)))))) = true
  rw [checkIndexedRow_append table [6,6,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs30Segment0 (refs30Segment1 ++ (refs30Segment2 ++ (refs30Segment3 ++ (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6))))) (by decide),
    checkIndexedRow_append table [6,6,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs30Segment1 (refs30Segment2 ++ (refs30Segment3 ++ (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6)))) (by decide),
    checkIndexedRow_append table [6,6,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs30Segment2 (refs30Segment3 ++ (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6))) (by decide),
    checkIndexedRow_append table [6,6,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs30Segment3 (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6)) (by decide),
    checkIndexedRow_append table [6,6,1] classSegment4 (classSegment5 ++ classSegment6) refs30Segment4 (refs30Segment5 ++ refs30Segment6) (by decide),
    checkIndexedRow_append table [6,6,1] classSegment5 classSegment6 refs30Segment5 refs30Segment6 (by decide)]
  decide

theorem residue30_checked : (2 * indexedCoverSum table 13 classes refs34 refs30) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs30Segment0 ++ (refs30Segment1 ++ (refs30Segment2 ++ (refs30Segment3 ++ (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs30Segment0 (refs30Segment1 ++ (refs30Segment2 ++ (refs30Segment3 ++ (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs30Segment1 (refs30Segment2 ++ (refs30Segment3 ++ (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs30Segment2 (refs30Segment3 ++ (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs30Segment3 (refs30Segment4 ++ (refs30Segment5 ++ refs30Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs30Segment4 (refs30Segment5 ++ refs30Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs30Segment5 refs30Segment6 (by decide) (by decide)]
  decide

theorem row31_checked : checkIndexedRow table [6,5,2] classes refs31 = true := by
  change checkIndexedRow table [6,5,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs31Segment0 ++ (refs31Segment1 ++ (refs31Segment2 ++ (refs31Segment3 ++ (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6)))))) = true
  rw [checkIndexedRow_append table [6,5,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs31Segment0 (refs31Segment1 ++ (refs31Segment2 ++ (refs31Segment3 ++ (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6))))) (by decide),
    checkIndexedRow_append table [6,5,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs31Segment1 (refs31Segment2 ++ (refs31Segment3 ++ (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6)))) (by decide),
    checkIndexedRow_append table [6,5,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs31Segment2 (refs31Segment3 ++ (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6))) (by decide),
    checkIndexedRow_append table [6,5,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs31Segment3 (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6)) (by decide),
    checkIndexedRow_append table [6,5,2] classSegment4 (classSegment5 ++ classSegment6) refs31Segment4 (refs31Segment5 ++ refs31Segment6) (by decide),
    checkIndexedRow_append table [6,5,2] classSegment5 classSegment6 refs31Segment5 refs31Segment6 (by decide)]
  decide

theorem residue31_checked : (2 * indexedCoverSum table 13 classes refs34 refs31) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs31Segment0 ++ (refs31Segment1 ++ (refs31Segment2 ++ (refs31Segment3 ++ (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs31Segment0 (refs31Segment1 ++ (refs31Segment2 ++ (refs31Segment3 ++ (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs31Segment1 (refs31Segment2 ++ (refs31Segment3 ++ (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs31Segment2 (refs31Segment3 ++ (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs31Segment3 (refs31Segment4 ++ (refs31Segment5 ++ refs31Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs31Segment4 (refs31Segment5 ++ refs31Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs31Segment5 refs31Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
