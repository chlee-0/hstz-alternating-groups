import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row48_checked : checkIndexedRow table [5,4,3,1] classes refs48 = true := by
  change checkIndexedRow table [5,4,3,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs48Segment0 ++ (refs48Segment1 ++ (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6)))))) = true
  rw [checkIndexedRow_append table [5,4,3,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs48Segment0 (refs48Segment1 ++ (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6))))) (by decide),
    checkIndexedRow_append table [5,4,3,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs48Segment1 (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6)))) (by decide),
    checkIndexedRow_append table [5,4,3,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs48Segment2 (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6))) (by decide),
    checkIndexedRow_append table [5,4,3,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs48Segment3 (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6)) (by decide),
    checkIndexedRow_append table [5,4,3,1] classSegment4 (classSegment5 ++ classSegment6) refs48Segment4 (refs48Segment5 ++ refs48Segment6) (by decide),
    checkIndexedRow_append table [5,4,3,1] classSegment5 classSegment6 refs48Segment5 refs48Segment6 (by decide)]
  decide

theorem residue48_checked : (2 * indexedCoverSum table 13 classes refs34 refs48) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs48Segment0 ++ (refs48Segment1 ++ (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs48Segment0 (refs48Segment1 ++ (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs48Segment1 (refs48Segment2 ++ (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs48Segment2 (refs48Segment3 ++ (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs48Segment3 (refs48Segment4 ++ (refs48Segment5 ++ refs48Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs48Segment4 (refs48Segment5 ++ refs48Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs48Segment5 refs48Segment6 (by decide) (by decide)]
  decide

theorem row49_checked : checkIndexedRow table [5,4,2,2] classes refs49 = true := by
  change checkIndexedRow table [5,4,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs49Segment0 ++ (refs49Segment1 ++ (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6)))))) = true
  rw [checkIndexedRow_append table [5,4,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs49Segment0 (refs49Segment1 ++ (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6))))) (by decide),
    checkIndexedRow_append table [5,4,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs49Segment1 (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6)))) (by decide),
    checkIndexedRow_append table [5,4,2,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs49Segment2 (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6))) (by decide),
    checkIndexedRow_append table [5,4,2,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs49Segment3 (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6)) (by decide),
    checkIndexedRow_append table [5,4,2,2] classSegment4 (classSegment5 ++ classSegment6) refs49Segment4 (refs49Segment5 ++ refs49Segment6) (by decide),
    checkIndexedRow_append table [5,4,2,2] classSegment5 classSegment6 refs49Segment5 refs49Segment6 (by decide)]
  decide

theorem residue49_checked : (2 * indexedCoverSum table 13 classes refs34 refs49) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs49Segment0 ++ (refs49Segment1 ++ (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs49Segment0 (refs49Segment1 ++ (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs49Segment1 (refs49Segment2 ++ (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs49Segment2 (refs49Segment3 ++ (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs49Segment3 (refs49Segment4 ++ (refs49Segment5 ++ refs49Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs49Segment4 (refs49Segment5 ++ refs49Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs49Segment5 refs49Segment6 (by decide) (by decide)]
  decide

theorem row50_checked : checkIndexedRow table [5,4,2,1,1] classes refs50 = true := by
  change checkIndexedRow table [5,4,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs50Segment0 ++ (refs50Segment1 ++ (refs50Segment2 ++ (refs50Segment3 ++ (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6)))))) = true
  rw [checkIndexedRow_append table [5,4,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs50Segment0 (refs50Segment1 ++ (refs50Segment2 ++ (refs50Segment3 ++ (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6))))) (by decide),
    checkIndexedRow_append table [5,4,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs50Segment1 (refs50Segment2 ++ (refs50Segment3 ++ (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6)))) (by decide),
    checkIndexedRow_append table [5,4,2,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs50Segment2 (refs50Segment3 ++ (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6))) (by decide),
    checkIndexedRow_append table [5,4,2,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs50Segment3 (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6)) (by decide),
    checkIndexedRow_append table [5,4,2,1,1] classSegment4 (classSegment5 ++ classSegment6) refs50Segment4 (refs50Segment5 ++ refs50Segment6) (by decide),
    checkIndexedRow_append table [5,4,2,1,1] classSegment5 classSegment6 refs50Segment5 refs50Segment6 (by decide)]
  decide

theorem residue50_checked : (2 * indexedCoverSum table 13 classes refs34 refs50) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs50Segment0 ++ (refs50Segment1 ++ (refs50Segment2 ++ (refs50Segment3 ++ (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs50Segment0 (refs50Segment1 ++ (refs50Segment2 ++ (refs50Segment3 ++ (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs50Segment1 (refs50Segment2 ++ (refs50Segment3 ++ (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs50Segment2 (refs50Segment3 ++ (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs50Segment3 (refs50Segment4 ++ (refs50Segment5 ++ refs50Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs50Segment4 (refs50Segment5 ++ refs50Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs50Segment5 refs50Segment6 (by decide) (by decide)]
  decide

theorem row51_checked : checkIndexedRow table [5,4,1,1,1,1] classes refs51 = true := by
  change checkIndexedRow table [5,4,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs51Segment0 ++ (refs51Segment1 ++ (refs51Segment2 ++ (refs51Segment3 ++ (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6)))))) = true
  rw [checkIndexedRow_append table [5,4,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs51Segment0 (refs51Segment1 ++ (refs51Segment2 ++ (refs51Segment3 ++ (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6))))) (by decide),
    checkIndexedRow_append table [5,4,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs51Segment1 (refs51Segment2 ++ (refs51Segment3 ++ (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6)))) (by decide),
    checkIndexedRow_append table [5,4,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs51Segment2 (refs51Segment3 ++ (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6))) (by decide),
    checkIndexedRow_append table [5,4,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs51Segment3 (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6)) (by decide),
    checkIndexedRow_append table [5,4,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs51Segment4 (refs51Segment5 ++ refs51Segment6) (by decide),
    checkIndexedRow_append table [5,4,1,1,1,1] classSegment5 classSegment6 refs51Segment5 refs51Segment6 (by decide)]
  decide

theorem residue51_checked : (2 * indexedCoverSum table 13 classes refs34 refs51) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs51Segment0 ++ (refs51Segment1 ++ (refs51Segment2 ++ (refs51Segment3 ++ (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs51Segment0 (refs51Segment1 ++ (refs51Segment2 ++ (refs51Segment3 ++ (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs51Segment1 (refs51Segment2 ++ (refs51Segment3 ++ (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs51Segment2 (refs51Segment3 ++ (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs51Segment3 (refs51Segment4 ++ (refs51Segment5 ++ refs51Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs51Segment4 (refs51Segment5 ++ refs51Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs51Segment5 refs51Segment6 (by decide) (by decide)]
  decide

theorem row52_checked : checkIndexedRow table [5,3,3,2] classes refs52 = true := by
  change checkIndexedRow table [5,3,3,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs52Segment0 ++ (refs52Segment1 ++ (refs52Segment2 ++ (refs52Segment3 ++ (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6)))))) = true
  rw [checkIndexedRow_append table [5,3,3,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs52Segment0 (refs52Segment1 ++ (refs52Segment2 ++ (refs52Segment3 ++ (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6))))) (by decide),
    checkIndexedRow_append table [5,3,3,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs52Segment1 (refs52Segment2 ++ (refs52Segment3 ++ (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6)))) (by decide),
    checkIndexedRow_append table [5,3,3,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs52Segment2 (refs52Segment3 ++ (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6))) (by decide),
    checkIndexedRow_append table [5,3,3,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs52Segment3 (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6)) (by decide),
    checkIndexedRow_append table [5,3,3,2] classSegment4 (classSegment5 ++ classSegment6) refs52Segment4 (refs52Segment5 ++ refs52Segment6) (by decide),
    checkIndexedRow_append table [5,3,3,2] classSegment5 classSegment6 refs52Segment5 refs52Segment6 (by decide)]
  decide

theorem residue52_checked : (2 * indexedCoverSum table 13 classes refs34 refs52) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs52Segment0 ++ (refs52Segment1 ++ (refs52Segment2 ++ (refs52Segment3 ++ (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs52Segment0 (refs52Segment1 ++ (refs52Segment2 ++ (refs52Segment3 ++ (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs52Segment1 (refs52Segment2 ++ (refs52Segment3 ++ (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs52Segment2 (refs52Segment3 ++ (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs52Segment3 (refs52Segment4 ++ (refs52Segment5 ++ refs52Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs52Segment4 (refs52Segment5 ++ refs52Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs52Segment5 refs52Segment6 (by decide) (by decide)]
  decide

theorem row53_checked : checkIndexedRow table [5,3,3,1,1] classes refs53 = true := by
  change checkIndexedRow table [5,3,3,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs53Segment0 ++ (refs53Segment1 ++ (refs53Segment2 ++ (refs53Segment3 ++ (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6)))))) = true
  rw [checkIndexedRow_append table [5,3,3,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs53Segment0 (refs53Segment1 ++ (refs53Segment2 ++ (refs53Segment3 ++ (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6))))) (by decide),
    checkIndexedRow_append table [5,3,3,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs53Segment1 (refs53Segment2 ++ (refs53Segment3 ++ (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6)))) (by decide),
    checkIndexedRow_append table [5,3,3,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs53Segment2 (refs53Segment3 ++ (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6))) (by decide),
    checkIndexedRow_append table [5,3,3,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs53Segment3 (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6)) (by decide),
    checkIndexedRow_append table [5,3,3,1,1] classSegment4 (classSegment5 ++ classSegment6) refs53Segment4 (refs53Segment5 ++ refs53Segment6) (by decide),
    checkIndexedRow_append table [5,3,3,1,1] classSegment5 classSegment6 refs53Segment5 refs53Segment6 (by decide)]
  decide

theorem residue53_checked : (2 * indexedCoverSum table 13 classes refs34 refs53) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs53Segment0 ++ (refs53Segment1 ++ (refs53Segment2 ++ (refs53Segment3 ++ (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs53Segment0 (refs53Segment1 ++ (refs53Segment2 ++ (refs53Segment3 ++ (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs53Segment1 (refs53Segment2 ++ (refs53Segment3 ++ (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs53Segment2 (refs53Segment3 ++ (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs53Segment3 (refs53Segment4 ++ (refs53Segment5 ++ refs53Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs53Segment4 (refs53Segment5 ++ refs53Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs53Segment5 refs53Segment6 (by decide) (by decide)]
  decide

theorem row54_checked : checkIndexedRow table [5,3,2,2,1] classes refs54 = true := by
  change checkIndexedRow table [5,3,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs54Segment0 ++ (refs54Segment1 ++ (refs54Segment2 ++ (refs54Segment3 ++ (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6)))))) = true
  rw [checkIndexedRow_append table [5,3,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs54Segment0 (refs54Segment1 ++ (refs54Segment2 ++ (refs54Segment3 ++ (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6))))) (by decide),
    checkIndexedRow_append table [5,3,2,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs54Segment1 (refs54Segment2 ++ (refs54Segment3 ++ (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6)))) (by decide),
    checkIndexedRow_append table [5,3,2,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs54Segment2 (refs54Segment3 ++ (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6))) (by decide),
    checkIndexedRow_append table [5,3,2,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs54Segment3 (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6)) (by decide),
    checkIndexedRow_append table [5,3,2,2,1] classSegment4 (classSegment5 ++ classSegment6) refs54Segment4 (refs54Segment5 ++ refs54Segment6) (by decide),
    checkIndexedRow_append table [5,3,2,2,1] classSegment5 classSegment6 refs54Segment5 refs54Segment6 (by decide)]
  decide

theorem residue54_checked : (2 * indexedCoverSum table 13 classes refs34 refs54) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs54Segment0 ++ (refs54Segment1 ++ (refs54Segment2 ++ (refs54Segment3 ++ (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs54Segment0 (refs54Segment1 ++ (refs54Segment2 ++ (refs54Segment3 ++ (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs54Segment1 (refs54Segment2 ++ (refs54Segment3 ++ (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs54Segment2 (refs54Segment3 ++ (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs54Segment3 (refs54Segment4 ++ (refs54Segment5 ++ refs54Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs54Segment4 (refs54Segment5 ++ refs54Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs54Segment5 refs54Segment6 (by decide) (by decide)]
  decide

theorem row55_checked : checkIndexedRow table [5,3,2,1,1,1] classes refs55 = true := by
  change checkIndexedRow table [5,3,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs55Segment0 ++ (refs55Segment1 ++ (refs55Segment2 ++ (refs55Segment3 ++ (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6)))))) = true
  rw [checkIndexedRow_append table [5,3,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs55Segment0 (refs55Segment1 ++ (refs55Segment2 ++ (refs55Segment3 ++ (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6))))) (by decide),
    checkIndexedRow_append table [5,3,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs55Segment1 (refs55Segment2 ++ (refs55Segment3 ++ (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6)))) (by decide),
    checkIndexedRow_append table [5,3,2,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs55Segment2 (refs55Segment3 ++ (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6))) (by decide),
    checkIndexedRow_append table [5,3,2,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs55Segment3 (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6)) (by decide),
    checkIndexedRow_append table [5,3,2,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs55Segment4 (refs55Segment5 ++ refs55Segment6) (by decide),
    checkIndexedRow_append table [5,3,2,1,1,1] classSegment5 classSegment6 refs55Segment5 refs55Segment6 (by decide)]
  decide

theorem residue55_checked : (2 * indexedCoverSum table 13 classes refs34 refs55) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs55Segment0 ++ (refs55Segment1 ++ (refs55Segment2 ++ (refs55Segment3 ++ (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs55Segment0 (refs55Segment1 ++ (refs55Segment2 ++ (refs55Segment3 ++ (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs55Segment1 (refs55Segment2 ++ (refs55Segment3 ++ (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs55Segment2 (refs55Segment3 ++ (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs55Segment3 (refs55Segment4 ++ (refs55Segment5 ++ refs55Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs55Segment4 (refs55Segment5 ++ refs55Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs55Segment5 refs55Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
