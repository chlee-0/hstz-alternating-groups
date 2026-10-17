import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row72_checked : checkIndexedRow table [4,3,2,2,1,1] classes refs72 = true := by
  change checkIndexedRow table [4,3,2,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs72Segment0 ++ (refs72Segment1 ++ (refs72Segment2 ++ (refs72Segment3 ++ (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6)))))) = true
  rw [checkIndexedRow_append table [4,3,2,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs72Segment0 (refs72Segment1 ++ (refs72Segment2 ++ (refs72Segment3 ++ (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6))))) (by decide),
    checkIndexedRow_append table [4,3,2,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs72Segment1 (refs72Segment2 ++ (refs72Segment3 ++ (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6)))) (by decide),
    checkIndexedRow_append table [4,3,2,2,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs72Segment2 (refs72Segment3 ++ (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6))) (by decide),
    checkIndexedRow_append table [4,3,2,2,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs72Segment3 (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6)) (by decide),
    checkIndexedRow_append table [4,3,2,2,1,1] classSegment4 (classSegment5 ++ classSegment6) refs72Segment4 (refs72Segment5 ++ refs72Segment6) (by decide),
    checkIndexedRow_append table [4,3,2,2,1,1] classSegment5 classSegment6 refs72Segment5 refs72Segment6 (by decide)]
  decide

theorem residue72_checked : (2 * indexedCoverSum table 13 classes refs34 refs72) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs72Segment0 ++ (refs72Segment1 ++ (refs72Segment2 ++ (refs72Segment3 ++ (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs72Segment0 (refs72Segment1 ++ (refs72Segment2 ++ (refs72Segment3 ++ (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs72Segment1 (refs72Segment2 ++ (refs72Segment3 ++ (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs72Segment2 (refs72Segment3 ++ (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs72Segment3 (refs72Segment4 ++ (refs72Segment5 ++ refs72Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs72Segment4 (refs72Segment5 ++ refs72Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs72Segment5 refs72Segment6 (by decide) (by decide)]
  decide

theorem row73_checked : checkIndexedRow table [4,3,2,1,1,1,1] classes refs73 = true := by
  change checkIndexedRow table [4,3,2,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs73Segment0 ++ (refs73Segment1 ++ (refs73Segment2 ++ (refs73Segment3 ++ (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6)))))) = true
  rw [checkIndexedRow_append table [4,3,2,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs73Segment0 (refs73Segment1 ++ (refs73Segment2 ++ (refs73Segment3 ++ (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6))))) (by decide),
    checkIndexedRow_append table [4,3,2,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs73Segment1 (refs73Segment2 ++ (refs73Segment3 ++ (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6)))) (by decide),
    checkIndexedRow_append table [4,3,2,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs73Segment2 (refs73Segment3 ++ (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6))) (by decide),
    checkIndexedRow_append table [4,3,2,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs73Segment3 (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6)) (by decide),
    checkIndexedRow_append table [4,3,2,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs73Segment4 (refs73Segment5 ++ refs73Segment6) (by decide),
    checkIndexedRow_append table [4,3,2,1,1,1,1] classSegment5 classSegment6 refs73Segment5 refs73Segment6 (by decide)]
  decide

theorem residue73_checked : (2 * indexedCoverSum table 13 classes refs34 refs73) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs73Segment0 ++ (refs73Segment1 ++ (refs73Segment2 ++ (refs73Segment3 ++ (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs73Segment0 (refs73Segment1 ++ (refs73Segment2 ++ (refs73Segment3 ++ (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs73Segment1 (refs73Segment2 ++ (refs73Segment3 ++ (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs73Segment2 (refs73Segment3 ++ (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs73Segment3 (refs73Segment4 ++ (refs73Segment5 ++ refs73Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs73Segment4 (refs73Segment5 ++ refs73Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs73Segment5 refs73Segment6 (by decide) (by decide)]
  decide

theorem row74_checked : checkIndexedRow table [4,3,1,1,1,1,1,1] classes refs74 = true := by
  change checkIndexedRow table [4,3,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs74Segment0 ++ (refs74Segment1 ++ (refs74Segment2 ++ (refs74Segment3 ++ (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6)))))) = true
  rw [checkIndexedRow_append table [4,3,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs74Segment0 (refs74Segment1 ++ (refs74Segment2 ++ (refs74Segment3 ++ (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6))))) (by decide),
    checkIndexedRow_append table [4,3,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs74Segment1 (refs74Segment2 ++ (refs74Segment3 ++ (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6)))) (by decide),
    checkIndexedRow_append table [4,3,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs74Segment2 (refs74Segment3 ++ (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6))) (by decide),
    checkIndexedRow_append table [4,3,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs74Segment3 (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6)) (by decide),
    checkIndexedRow_append table [4,3,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs74Segment4 (refs74Segment5 ++ refs74Segment6) (by decide),
    checkIndexedRow_append table [4,3,1,1,1,1,1,1] classSegment5 classSegment6 refs74Segment5 refs74Segment6 (by decide)]
  decide

theorem residue74_checked : (2 * indexedCoverSum table 13 classes refs34 refs74) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs74Segment0 ++ (refs74Segment1 ++ (refs74Segment2 ++ (refs74Segment3 ++ (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs74Segment0 (refs74Segment1 ++ (refs74Segment2 ++ (refs74Segment3 ++ (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs74Segment1 (refs74Segment2 ++ (refs74Segment3 ++ (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs74Segment2 (refs74Segment3 ++ (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs74Segment3 (refs74Segment4 ++ (refs74Segment5 ++ refs74Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs74Segment4 (refs74Segment5 ++ refs74Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs74Segment5 refs74Segment6 (by decide) (by decide)]
  decide

theorem row75_checked : checkIndexedRow table [4,2,2,2,2,1] classes refs75 = true := by
  change checkIndexedRow table [4,2,2,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs75Segment0 ++ (refs75Segment1 ++ (refs75Segment2 ++ (refs75Segment3 ++ (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6)))))) = true
  rw [checkIndexedRow_append table [4,2,2,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs75Segment0 (refs75Segment1 ++ (refs75Segment2 ++ (refs75Segment3 ++ (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6))))) (by decide),
    checkIndexedRow_append table [4,2,2,2,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs75Segment1 (refs75Segment2 ++ (refs75Segment3 ++ (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6)))) (by decide),
    checkIndexedRow_append table [4,2,2,2,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs75Segment2 (refs75Segment3 ++ (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6))) (by decide),
    checkIndexedRow_append table [4,2,2,2,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs75Segment3 (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6)) (by decide),
    checkIndexedRow_append table [4,2,2,2,2,1] classSegment4 (classSegment5 ++ classSegment6) refs75Segment4 (refs75Segment5 ++ refs75Segment6) (by decide),
    checkIndexedRow_append table [4,2,2,2,2,1] classSegment5 classSegment6 refs75Segment5 refs75Segment6 (by decide)]
  decide

theorem residue75_checked : (2 * indexedCoverSum table 13 classes refs34 refs75) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs75Segment0 ++ (refs75Segment1 ++ (refs75Segment2 ++ (refs75Segment3 ++ (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs75Segment0 (refs75Segment1 ++ (refs75Segment2 ++ (refs75Segment3 ++ (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs75Segment1 (refs75Segment2 ++ (refs75Segment3 ++ (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs75Segment2 (refs75Segment3 ++ (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs75Segment3 (refs75Segment4 ++ (refs75Segment5 ++ refs75Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs75Segment4 (refs75Segment5 ++ refs75Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs75Segment5 refs75Segment6 (by decide) (by decide)]
  decide

theorem row76_checked : checkIndexedRow table [4,2,2,2,1,1,1] classes refs76 = true := by
  change checkIndexedRow table [4,2,2,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs76Segment0 ++ (refs76Segment1 ++ (refs76Segment2 ++ (refs76Segment3 ++ (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6)))))) = true
  rw [checkIndexedRow_append table [4,2,2,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs76Segment0 (refs76Segment1 ++ (refs76Segment2 ++ (refs76Segment3 ++ (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6))))) (by decide),
    checkIndexedRow_append table [4,2,2,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs76Segment1 (refs76Segment2 ++ (refs76Segment3 ++ (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6)))) (by decide),
    checkIndexedRow_append table [4,2,2,2,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs76Segment2 (refs76Segment3 ++ (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6))) (by decide),
    checkIndexedRow_append table [4,2,2,2,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs76Segment3 (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6)) (by decide),
    checkIndexedRow_append table [4,2,2,2,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs76Segment4 (refs76Segment5 ++ refs76Segment6) (by decide),
    checkIndexedRow_append table [4,2,2,2,1,1,1] classSegment5 classSegment6 refs76Segment5 refs76Segment6 (by decide)]
  decide

theorem residue76_checked : (2 * indexedCoverSum table 13 classes refs34 refs76) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs76Segment0 ++ (refs76Segment1 ++ (refs76Segment2 ++ (refs76Segment3 ++ (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs76Segment0 (refs76Segment1 ++ (refs76Segment2 ++ (refs76Segment3 ++ (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs76Segment1 (refs76Segment2 ++ (refs76Segment3 ++ (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs76Segment2 (refs76Segment3 ++ (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs76Segment3 (refs76Segment4 ++ (refs76Segment5 ++ refs76Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs76Segment4 (refs76Segment5 ++ refs76Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs76Segment5 refs76Segment6 (by decide) (by decide)]
  decide

theorem row77_checked : checkIndexedRow table [4,2,2,1,1,1,1,1] classes refs77 = true := by
  change checkIndexedRow table [4,2,2,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs77Segment0 ++ (refs77Segment1 ++ (refs77Segment2 ++ (refs77Segment3 ++ (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6)))))) = true
  rw [checkIndexedRow_append table [4,2,2,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs77Segment0 (refs77Segment1 ++ (refs77Segment2 ++ (refs77Segment3 ++ (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6))))) (by decide),
    checkIndexedRow_append table [4,2,2,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs77Segment1 (refs77Segment2 ++ (refs77Segment3 ++ (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6)))) (by decide),
    checkIndexedRow_append table [4,2,2,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs77Segment2 (refs77Segment3 ++ (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6))) (by decide),
    checkIndexedRow_append table [4,2,2,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs77Segment3 (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6)) (by decide),
    checkIndexedRow_append table [4,2,2,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs77Segment4 (refs77Segment5 ++ refs77Segment6) (by decide),
    checkIndexedRow_append table [4,2,2,1,1,1,1,1] classSegment5 classSegment6 refs77Segment5 refs77Segment6 (by decide)]
  decide

theorem residue77_checked : (2 * indexedCoverSum table 13 classes refs34 refs77) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs77Segment0 ++ (refs77Segment1 ++ (refs77Segment2 ++ (refs77Segment3 ++ (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs77Segment0 (refs77Segment1 ++ (refs77Segment2 ++ (refs77Segment3 ++ (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs77Segment1 (refs77Segment2 ++ (refs77Segment3 ++ (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs77Segment2 (refs77Segment3 ++ (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs77Segment3 (refs77Segment4 ++ (refs77Segment5 ++ refs77Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs77Segment4 (refs77Segment5 ++ refs77Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs77Segment5 refs77Segment6 (by decide) (by decide)]
  decide

theorem row78_checked : checkIndexedRow table [4,2,1,1,1,1,1,1,1] classes refs78 = true := by
  change checkIndexedRow table [4,2,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs78Segment0 ++ (refs78Segment1 ++ (refs78Segment2 ++ (refs78Segment3 ++ (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6)))))) = true
  rw [checkIndexedRow_append table [4,2,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs78Segment0 (refs78Segment1 ++ (refs78Segment2 ++ (refs78Segment3 ++ (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6))))) (by decide),
    checkIndexedRow_append table [4,2,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs78Segment1 (refs78Segment2 ++ (refs78Segment3 ++ (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6)))) (by decide),
    checkIndexedRow_append table [4,2,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs78Segment2 (refs78Segment3 ++ (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6))) (by decide),
    checkIndexedRow_append table [4,2,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs78Segment3 (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6)) (by decide),
    checkIndexedRow_append table [4,2,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs78Segment4 (refs78Segment5 ++ refs78Segment6) (by decide),
    checkIndexedRow_append table [4,2,1,1,1,1,1,1,1] classSegment5 classSegment6 refs78Segment5 refs78Segment6 (by decide)]
  decide

theorem residue78_checked : (2 * indexedCoverSum table 13 classes refs34 refs78) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs78Segment0 ++ (refs78Segment1 ++ (refs78Segment2 ++ (refs78Segment3 ++ (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs78Segment0 (refs78Segment1 ++ (refs78Segment2 ++ (refs78Segment3 ++ (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs78Segment1 (refs78Segment2 ++ (refs78Segment3 ++ (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs78Segment2 (refs78Segment3 ++ (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs78Segment3 (refs78Segment4 ++ (refs78Segment5 ++ refs78Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs78Segment4 (refs78Segment5 ++ refs78Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs78Segment5 refs78Segment6 (by decide) (by decide)]
  decide

theorem row79_checked : checkIndexedRow table [4,1,1,1,1,1,1,1,1,1] classes refs79 = true := by
  change checkIndexedRow table [4,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs79Segment0 ++ (refs79Segment1 ++ (refs79Segment2 ++ (refs79Segment3 ++ (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6)))))) = true
  rw [checkIndexedRow_append table [4,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs79Segment0 (refs79Segment1 ++ (refs79Segment2 ++ (refs79Segment3 ++ (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6))))) (by decide),
    checkIndexedRow_append table [4,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs79Segment1 (refs79Segment2 ++ (refs79Segment3 ++ (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6)))) (by decide),
    checkIndexedRow_append table [4,1,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs79Segment2 (refs79Segment3 ++ (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6))) (by decide),
    checkIndexedRow_append table [4,1,1,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs79Segment3 (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6)) (by decide),
    checkIndexedRow_append table [4,1,1,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs79Segment4 (refs79Segment5 ++ refs79Segment6) (by decide),
    checkIndexedRow_append table [4,1,1,1,1,1,1,1,1,1] classSegment5 classSegment6 refs79Segment5 refs79Segment6 (by decide)]
  decide

theorem residue79_checked : (2 * indexedCoverSum table 13 classes refs34 refs79) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs79Segment0 ++ (refs79Segment1 ++ (refs79Segment2 ++ (refs79Segment3 ++ (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs79Segment0 (refs79Segment1 ++ (refs79Segment2 ++ (refs79Segment3 ++ (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs79Segment1 (refs79Segment2 ++ (refs79Segment3 ++ (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs79Segment2 (refs79Segment3 ++ (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs79Segment3 (refs79Segment4 ++ (refs79Segment5 ++ refs79Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs79Segment4 (refs79Segment5 ++ refs79Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs79Segment5 refs79Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
