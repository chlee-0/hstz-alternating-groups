import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row80_checked : checkIndexedRow table [3,3,3,3,1] classes refs80 = true := by
  change checkIndexedRow table [3,3,3,3,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs80Segment0 ++ (refs80Segment1 ++ (refs80Segment2 ++ (refs80Segment3 ++ (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6)))))) = true
  rw [checkIndexedRow_append table [3,3,3,3,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs80Segment0 (refs80Segment1 ++ (refs80Segment2 ++ (refs80Segment3 ++ (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6))))) (by decide),
    checkIndexedRow_append table [3,3,3,3,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs80Segment1 (refs80Segment2 ++ (refs80Segment3 ++ (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6)))) (by decide),
    checkIndexedRow_append table [3,3,3,3,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs80Segment2 (refs80Segment3 ++ (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6))) (by decide),
    checkIndexedRow_append table [3,3,3,3,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs80Segment3 (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6)) (by decide),
    checkIndexedRow_append table [3,3,3,3,1] classSegment4 (classSegment5 ++ classSegment6) refs80Segment4 (refs80Segment5 ++ refs80Segment6) (by decide),
    checkIndexedRow_append table [3,3,3,3,1] classSegment5 classSegment6 refs80Segment5 refs80Segment6 (by decide)]
  decide

theorem residue80_checked : (2 * indexedCoverSum table 13 classes refs34 refs80) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs80Segment0 ++ (refs80Segment1 ++ (refs80Segment2 ++ (refs80Segment3 ++ (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs80Segment0 (refs80Segment1 ++ (refs80Segment2 ++ (refs80Segment3 ++ (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs80Segment1 (refs80Segment2 ++ (refs80Segment3 ++ (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs80Segment2 (refs80Segment3 ++ (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs80Segment3 (refs80Segment4 ++ (refs80Segment5 ++ refs80Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs80Segment4 (refs80Segment5 ++ refs80Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs80Segment5 refs80Segment6 (by decide) (by decide)]
  decide

theorem row81_checked : checkIndexedRow table [3,3,3,2,2] classes refs81 = true := by
  change checkIndexedRow table [3,3,3,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs81Segment0 ++ (refs81Segment1 ++ (refs81Segment2 ++ (refs81Segment3 ++ (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6)))))) = true
  rw [checkIndexedRow_append table [3,3,3,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs81Segment0 (refs81Segment1 ++ (refs81Segment2 ++ (refs81Segment3 ++ (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6))))) (by decide),
    checkIndexedRow_append table [3,3,3,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs81Segment1 (refs81Segment2 ++ (refs81Segment3 ++ (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6)))) (by decide),
    checkIndexedRow_append table [3,3,3,2,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs81Segment2 (refs81Segment3 ++ (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6))) (by decide),
    checkIndexedRow_append table [3,3,3,2,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs81Segment3 (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6)) (by decide),
    checkIndexedRow_append table [3,3,3,2,2] classSegment4 (classSegment5 ++ classSegment6) refs81Segment4 (refs81Segment5 ++ refs81Segment6) (by decide),
    checkIndexedRow_append table [3,3,3,2,2] classSegment5 classSegment6 refs81Segment5 refs81Segment6 (by decide)]
  decide

theorem residue81_checked : (2 * indexedCoverSum table 13 classes refs34 refs81) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs81Segment0 ++ (refs81Segment1 ++ (refs81Segment2 ++ (refs81Segment3 ++ (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs81Segment0 (refs81Segment1 ++ (refs81Segment2 ++ (refs81Segment3 ++ (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs81Segment1 (refs81Segment2 ++ (refs81Segment3 ++ (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs81Segment2 (refs81Segment3 ++ (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs81Segment3 (refs81Segment4 ++ (refs81Segment5 ++ refs81Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs81Segment4 (refs81Segment5 ++ refs81Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs81Segment5 refs81Segment6 (by decide) (by decide)]
  decide

theorem row82_checked : checkIndexedRow table [3,3,3,2,1,1] classes refs82 = true := by
  change checkIndexedRow table [3,3,3,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs82Segment0 ++ (refs82Segment1 ++ (refs82Segment2 ++ (refs82Segment3 ++ (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6)))))) = true
  rw [checkIndexedRow_append table [3,3,3,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs82Segment0 (refs82Segment1 ++ (refs82Segment2 ++ (refs82Segment3 ++ (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6))))) (by decide),
    checkIndexedRow_append table [3,3,3,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs82Segment1 (refs82Segment2 ++ (refs82Segment3 ++ (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6)))) (by decide),
    checkIndexedRow_append table [3,3,3,2,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs82Segment2 (refs82Segment3 ++ (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6))) (by decide),
    checkIndexedRow_append table [3,3,3,2,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs82Segment3 (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6)) (by decide),
    checkIndexedRow_append table [3,3,3,2,1,1] classSegment4 (classSegment5 ++ classSegment6) refs82Segment4 (refs82Segment5 ++ refs82Segment6) (by decide),
    checkIndexedRow_append table [3,3,3,2,1,1] classSegment5 classSegment6 refs82Segment5 refs82Segment6 (by decide)]
  decide

theorem residue82_checked : (2 * indexedCoverSum table 13 classes refs34 refs82) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs82Segment0 ++ (refs82Segment1 ++ (refs82Segment2 ++ (refs82Segment3 ++ (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs82Segment0 (refs82Segment1 ++ (refs82Segment2 ++ (refs82Segment3 ++ (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs82Segment1 (refs82Segment2 ++ (refs82Segment3 ++ (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs82Segment2 (refs82Segment3 ++ (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs82Segment3 (refs82Segment4 ++ (refs82Segment5 ++ refs82Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs82Segment4 (refs82Segment5 ++ refs82Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs82Segment5 refs82Segment6 (by decide) (by decide)]
  decide

theorem row83_checked : checkIndexedRow table [3,3,3,1,1,1,1] classes refs83 = true := by
  change checkIndexedRow table [3,3,3,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs83Segment0 ++ (refs83Segment1 ++ (refs83Segment2 ++ (refs83Segment3 ++ (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6)))))) = true
  rw [checkIndexedRow_append table [3,3,3,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs83Segment0 (refs83Segment1 ++ (refs83Segment2 ++ (refs83Segment3 ++ (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6))))) (by decide),
    checkIndexedRow_append table [3,3,3,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs83Segment1 (refs83Segment2 ++ (refs83Segment3 ++ (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6)))) (by decide),
    checkIndexedRow_append table [3,3,3,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs83Segment2 (refs83Segment3 ++ (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6))) (by decide),
    checkIndexedRow_append table [3,3,3,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs83Segment3 (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6)) (by decide),
    checkIndexedRow_append table [3,3,3,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs83Segment4 (refs83Segment5 ++ refs83Segment6) (by decide),
    checkIndexedRow_append table [3,3,3,1,1,1,1] classSegment5 classSegment6 refs83Segment5 refs83Segment6 (by decide)]
  decide

theorem residue83_checked : (2 * indexedCoverSum table 13 classes refs34 refs83) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs83Segment0 ++ (refs83Segment1 ++ (refs83Segment2 ++ (refs83Segment3 ++ (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs83Segment0 (refs83Segment1 ++ (refs83Segment2 ++ (refs83Segment3 ++ (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs83Segment1 (refs83Segment2 ++ (refs83Segment3 ++ (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs83Segment2 (refs83Segment3 ++ (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs83Segment3 (refs83Segment4 ++ (refs83Segment5 ++ refs83Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs83Segment4 (refs83Segment5 ++ refs83Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs83Segment5 refs83Segment6 (by decide) (by decide)]
  decide

theorem row84_checked : checkIndexedRow table [3,3,2,2,2,1] classes refs84 = true := by
  change checkIndexedRow table [3,3,2,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs84Segment0 ++ (refs84Segment1 ++ (refs84Segment2 ++ (refs84Segment3 ++ (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6)))))) = true
  rw [checkIndexedRow_append table [3,3,2,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs84Segment0 (refs84Segment1 ++ (refs84Segment2 ++ (refs84Segment3 ++ (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6))))) (by decide),
    checkIndexedRow_append table [3,3,2,2,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs84Segment1 (refs84Segment2 ++ (refs84Segment3 ++ (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6)))) (by decide),
    checkIndexedRow_append table [3,3,2,2,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs84Segment2 (refs84Segment3 ++ (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6))) (by decide),
    checkIndexedRow_append table [3,3,2,2,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs84Segment3 (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6)) (by decide),
    checkIndexedRow_append table [3,3,2,2,2,1] classSegment4 (classSegment5 ++ classSegment6) refs84Segment4 (refs84Segment5 ++ refs84Segment6) (by decide),
    checkIndexedRow_append table [3,3,2,2,2,1] classSegment5 classSegment6 refs84Segment5 refs84Segment6 (by decide)]
  decide

theorem residue84_checked : (2 * indexedCoverSum table 13 classes refs34 refs84) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs84Segment0 ++ (refs84Segment1 ++ (refs84Segment2 ++ (refs84Segment3 ++ (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs84Segment0 (refs84Segment1 ++ (refs84Segment2 ++ (refs84Segment3 ++ (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs84Segment1 (refs84Segment2 ++ (refs84Segment3 ++ (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs84Segment2 (refs84Segment3 ++ (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs84Segment3 (refs84Segment4 ++ (refs84Segment5 ++ refs84Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs84Segment4 (refs84Segment5 ++ refs84Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs84Segment5 refs84Segment6 (by decide) (by decide)]
  decide

theorem row85_checked : checkIndexedRow table [3,3,2,2,1,1,1] classes refs85 = true := by
  change checkIndexedRow table [3,3,2,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs85Segment0 ++ (refs85Segment1 ++ (refs85Segment2 ++ (refs85Segment3 ++ (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6)))))) = true
  rw [checkIndexedRow_append table [3,3,2,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs85Segment0 (refs85Segment1 ++ (refs85Segment2 ++ (refs85Segment3 ++ (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6))))) (by decide),
    checkIndexedRow_append table [3,3,2,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs85Segment1 (refs85Segment2 ++ (refs85Segment3 ++ (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6)))) (by decide),
    checkIndexedRow_append table [3,3,2,2,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs85Segment2 (refs85Segment3 ++ (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6))) (by decide),
    checkIndexedRow_append table [3,3,2,2,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs85Segment3 (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6)) (by decide),
    checkIndexedRow_append table [3,3,2,2,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs85Segment4 (refs85Segment5 ++ refs85Segment6) (by decide),
    checkIndexedRow_append table [3,3,2,2,1,1,1] classSegment5 classSegment6 refs85Segment5 refs85Segment6 (by decide)]
  decide

theorem residue85_checked : (2 * indexedCoverSum table 13 classes refs34 refs85) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs85Segment0 ++ (refs85Segment1 ++ (refs85Segment2 ++ (refs85Segment3 ++ (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs85Segment0 (refs85Segment1 ++ (refs85Segment2 ++ (refs85Segment3 ++ (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs85Segment1 (refs85Segment2 ++ (refs85Segment3 ++ (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs85Segment2 (refs85Segment3 ++ (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs85Segment3 (refs85Segment4 ++ (refs85Segment5 ++ refs85Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs85Segment4 (refs85Segment5 ++ refs85Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs85Segment5 refs85Segment6 (by decide) (by decide)]
  decide

theorem row86_checked : checkIndexedRow table [3,3,2,1,1,1,1,1] classes refs86 = true := by
  change checkIndexedRow table [3,3,2,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs86Segment0 ++ (refs86Segment1 ++ (refs86Segment2 ++ (refs86Segment3 ++ (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6)))))) = true
  rw [checkIndexedRow_append table [3,3,2,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs86Segment0 (refs86Segment1 ++ (refs86Segment2 ++ (refs86Segment3 ++ (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6))))) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs86Segment1 (refs86Segment2 ++ (refs86Segment3 ++ (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6)))) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs86Segment2 (refs86Segment3 ++ (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6))) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs86Segment3 (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6)) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs86Segment4 (refs86Segment5 ++ refs86Segment6) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1,1,1] classSegment5 classSegment6 refs86Segment5 refs86Segment6 (by decide)]
  decide

theorem residue86_checked : (2 * indexedCoverSum table 13 classes refs34 refs86) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs86Segment0 ++ (refs86Segment1 ++ (refs86Segment2 ++ (refs86Segment3 ++ (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs86Segment0 (refs86Segment1 ++ (refs86Segment2 ++ (refs86Segment3 ++ (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs86Segment1 (refs86Segment2 ++ (refs86Segment3 ++ (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs86Segment2 (refs86Segment3 ++ (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs86Segment3 (refs86Segment4 ++ (refs86Segment5 ++ refs86Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs86Segment4 (refs86Segment5 ++ refs86Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs86Segment5 refs86Segment6 (by decide) (by decide)]
  decide

theorem row87_checked : checkIndexedRow table [3,3,1,1,1,1,1,1,1] classes refs87 = true := by
  change checkIndexedRow table [3,3,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs87Segment0 ++ (refs87Segment1 ++ (refs87Segment2 ++ (refs87Segment3 ++ (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6)))))) = true
  rw [checkIndexedRow_append table [3,3,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs87Segment0 (refs87Segment1 ++ (refs87Segment2 ++ (refs87Segment3 ++ (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6))))) (by decide),
    checkIndexedRow_append table [3,3,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs87Segment1 (refs87Segment2 ++ (refs87Segment3 ++ (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6)))) (by decide),
    checkIndexedRow_append table [3,3,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs87Segment2 (refs87Segment3 ++ (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6))) (by decide),
    checkIndexedRow_append table [3,3,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs87Segment3 (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6)) (by decide),
    checkIndexedRow_append table [3,3,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs87Segment4 (refs87Segment5 ++ refs87Segment6) (by decide),
    checkIndexedRow_append table [3,3,1,1,1,1,1,1,1] classSegment5 classSegment6 refs87Segment5 refs87Segment6 (by decide)]
  decide

theorem residue87_checked : (2 * indexedCoverSum table 13 classes refs34 refs87) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs87Segment0 ++ (refs87Segment1 ++ (refs87Segment2 ++ (refs87Segment3 ++ (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs87Segment0 (refs87Segment1 ++ (refs87Segment2 ++ (refs87Segment3 ++ (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs87Segment1 (refs87Segment2 ++ (refs87Segment3 ++ (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs87Segment2 (refs87Segment3 ++ (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs87Segment3 (refs87Segment4 ++ (refs87Segment5 ++ refs87Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs87Segment4 (refs87Segment5 ++ refs87Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs87Segment5 refs87Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
