import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row88_checked : checkIndexedRow table [3,2,2,2,2,2] classes refs88 = true := by
  change checkIndexedRow table [3,2,2,2,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs88Segment0 ++ (refs88Segment1 ++ (refs88Segment2 ++ (refs88Segment3 ++ (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6)))))) = true
  rw [checkIndexedRow_append table [3,2,2,2,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs88Segment0 (refs88Segment1 ++ (refs88Segment2 ++ (refs88Segment3 ++ (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6))))) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs88Segment1 (refs88Segment2 ++ (refs88Segment3 ++ (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6)))) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs88Segment2 (refs88Segment3 ++ (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6))) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs88Segment3 (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6)) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,2] classSegment4 (classSegment5 ++ classSegment6) refs88Segment4 (refs88Segment5 ++ refs88Segment6) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,2] classSegment5 classSegment6 refs88Segment5 refs88Segment6 (by decide)]
  decide

theorem residue88_checked : (2 * indexedCoverSum table 13 classes refs34 refs88) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs88Segment0 ++ (refs88Segment1 ++ (refs88Segment2 ++ (refs88Segment3 ++ (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs88Segment0 (refs88Segment1 ++ (refs88Segment2 ++ (refs88Segment3 ++ (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs88Segment1 (refs88Segment2 ++ (refs88Segment3 ++ (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs88Segment2 (refs88Segment3 ++ (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs88Segment3 (refs88Segment4 ++ (refs88Segment5 ++ refs88Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs88Segment4 (refs88Segment5 ++ refs88Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs88Segment5 refs88Segment6 (by decide) (by decide)]
  decide

theorem row89_checked : checkIndexedRow table [3,2,2,2,2,1,1] classes refs89 = true := by
  change checkIndexedRow table [3,2,2,2,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs89Segment0 ++ (refs89Segment1 ++ (refs89Segment2 ++ (refs89Segment3 ++ (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6)))))) = true
  rw [checkIndexedRow_append table [3,2,2,2,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs89Segment0 (refs89Segment1 ++ (refs89Segment2 ++ (refs89Segment3 ++ (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6))))) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs89Segment1 (refs89Segment2 ++ (refs89Segment3 ++ (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6)))) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs89Segment2 (refs89Segment3 ++ (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6))) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs89Segment3 (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6)) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,1,1] classSegment4 (classSegment5 ++ classSegment6) refs89Segment4 (refs89Segment5 ++ refs89Segment6) (by decide),
    checkIndexedRow_append table [3,2,2,2,2,1,1] classSegment5 classSegment6 refs89Segment5 refs89Segment6 (by decide)]
  decide

theorem residue89_checked : (2 * indexedCoverSum table 13 classes refs34 refs89) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs89Segment0 ++ (refs89Segment1 ++ (refs89Segment2 ++ (refs89Segment3 ++ (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs89Segment0 (refs89Segment1 ++ (refs89Segment2 ++ (refs89Segment3 ++ (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs89Segment1 (refs89Segment2 ++ (refs89Segment3 ++ (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs89Segment2 (refs89Segment3 ++ (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs89Segment3 (refs89Segment4 ++ (refs89Segment5 ++ refs89Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs89Segment4 (refs89Segment5 ++ refs89Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs89Segment5 refs89Segment6 (by decide) (by decide)]
  decide

theorem row90_checked : checkIndexedRow table [3,2,2,2,1,1,1,1] classes refs90 = true := by
  change checkIndexedRow table [3,2,2,2,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs90Segment0 ++ (refs90Segment1 ++ (refs90Segment2 ++ (refs90Segment3 ++ (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6)))))) = true
  rw [checkIndexedRow_append table [3,2,2,2,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs90Segment0 (refs90Segment1 ++ (refs90Segment2 ++ (refs90Segment3 ++ (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6))))) (by decide),
    checkIndexedRow_append table [3,2,2,2,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs90Segment1 (refs90Segment2 ++ (refs90Segment3 ++ (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6)))) (by decide),
    checkIndexedRow_append table [3,2,2,2,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs90Segment2 (refs90Segment3 ++ (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6))) (by decide),
    checkIndexedRow_append table [3,2,2,2,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs90Segment3 (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6)) (by decide),
    checkIndexedRow_append table [3,2,2,2,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs90Segment4 (refs90Segment5 ++ refs90Segment6) (by decide),
    checkIndexedRow_append table [3,2,2,2,1,1,1,1] classSegment5 classSegment6 refs90Segment5 refs90Segment6 (by decide)]
  decide

theorem residue90_checked : (2 * indexedCoverSum table 13 classes refs34 refs90) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs90Segment0 ++ (refs90Segment1 ++ (refs90Segment2 ++ (refs90Segment3 ++ (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs90Segment0 (refs90Segment1 ++ (refs90Segment2 ++ (refs90Segment3 ++ (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs90Segment1 (refs90Segment2 ++ (refs90Segment3 ++ (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs90Segment2 (refs90Segment3 ++ (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs90Segment3 (refs90Segment4 ++ (refs90Segment5 ++ refs90Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs90Segment4 (refs90Segment5 ++ refs90Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs90Segment5 refs90Segment6 (by decide) (by decide)]
  decide

theorem row91_checked : checkIndexedRow table [3,2,2,1,1,1,1,1,1] classes refs91 = true := by
  change checkIndexedRow table [3,2,2,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs91Segment0 ++ (refs91Segment1 ++ (refs91Segment2 ++ (refs91Segment3 ++ (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6)))))) = true
  rw [checkIndexedRow_append table [3,2,2,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs91Segment0 (refs91Segment1 ++ (refs91Segment2 ++ (refs91Segment3 ++ (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6))))) (by decide),
    checkIndexedRow_append table [3,2,2,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs91Segment1 (refs91Segment2 ++ (refs91Segment3 ++ (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6)))) (by decide),
    checkIndexedRow_append table [3,2,2,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs91Segment2 (refs91Segment3 ++ (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6))) (by decide),
    checkIndexedRow_append table [3,2,2,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs91Segment3 (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6)) (by decide),
    checkIndexedRow_append table [3,2,2,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs91Segment4 (refs91Segment5 ++ refs91Segment6) (by decide),
    checkIndexedRow_append table [3,2,2,1,1,1,1,1,1] classSegment5 classSegment6 refs91Segment5 refs91Segment6 (by decide)]
  decide

theorem residue91_checked : (2 * indexedCoverSum table 13 classes refs34 refs91) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs91Segment0 ++ (refs91Segment1 ++ (refs91Segment2 ++ (refs91Segment3 ++ (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs91Segment0 (refs91Segment1 ++ (refs91Segment2 ++ (refs91Segment3 ++ (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs91Segment1 (refs91Segment2 ++ (refs91Segment3 ++ (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs91Segment2 (refs91Segment3 ++ (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs91Segment3 (refs91Segment4 ++ (refs91Segment5 ++ refs91Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs91Segment4 (refs91Segment5 ++ refs91Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs91Segment5 refs91Segment6 (by decide) (by decide)]
  decide

theorem row92_checked : checkIndexedRow table [3,2,1,1,1,1,1,1,1,1] classes refs92 = true := by
  change checkIndexedRow table [3,2,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs92Segment0 ++ (refs92Segment1 ++ (refs92Segment2 ++ (refs92Segment3 ++ (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6)))))) = true
  rw [checkIndexedRow_append table [3,2,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs92Segment0 (refs92Segment1 ++ (refs92Segment2 ++ (refs92Segment3 ++ (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6))))) (by decide),
    checkIndexedRow_append table [3,2,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs92Segment1 (refs92Segment2 ++ (refs92Segment3 ++ (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6)))) (by decide),
    checkIndexedRow_append table [3,2,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs92Segment2 (refs92Segment3 ++ (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6))) (by decide),
    checkIndexedRow_append table [3,2,1,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs92Segment3 (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6)) (by decide),
    checkIndexedRow_append table [3,2,1,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs92Segment4 (refs92Segment5 ++ refs92Segment6) (by decide),
    checkIndexedRow_append table [3,2,1,1,1,1,1,1,1,1] classSegment5 classSegment6 refs92Segment5 refs92Segment6 (by decide)]
  decide

theorem residue92_checked : (2 * indexedCoverSum table 13 classes refs34 refs92) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs92Segment0 ++ (refs92Segment1 ++ (refs92Segment2 ++ (refs92Segment3 ++ (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs92Segment0 (refs92Segment1 ++ (refs92Segment2 ++ (refs92Segment3 ++ (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs92Segment1 (refs92Segment2 ++ (refs92Segment3 ++ (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs92Segment2 (refs92Segment3 ++ (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs92Segment3 (refs92Segment4 ++ (refs92Segment5 ++ refs92Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs92Segment4 (refs92Segment5 ++ refs92Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs92Segment5 refs92Segment6 (by decide) (by decide)]
  decide

theorem row93_checked : checkIndexedRow table [3,1,1,1,1,1,1,1,1,1,1] classes refs93 = true := by
  change checkIndexedRow table [3,1,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs93Segment0 ++ (refs93Segment1 ++ (refs93Segment2 ++ (refs93Segment3 ++ (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6)))))) = true
  rw [checkIndexedRow_append table [3,1,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs93Segment0 (refs93Segment1 ++ (refs93Segment2 ++ (refs93Segment3 ++ (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6))))) (by decide),
    checkIndexedRow_append table [3,1,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs93Segment1 (refs93Segment2 ++ (refs93Segment3 ++ (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6)))) (by decide),
    checkIndexedRow_append table [3,1,1,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs93Segment2 (refs93Segment3 ++ (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6))) (by decide),
    checkIndexedRow_append table [3,1,1,1,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs93Segment3 (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6)) (by decide),
    checkIndexedRow_append table [3,1,1,1,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs93Segment4 (refs93Segment5 ++ refs93Segment6) (by decide),
    checkIndexedRow_append table [3,1,1,1,1,1,1,1,1,1,1] classSegment5 classSegment6 refs93Segment5 refs93Segment6 (by decide)]
  decide

theorem residue93_checked : (2 * indexedCoverSum table 13 classes refs34 refs93) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs93Segment0 ++ (refs93Segment1 ++ (refs93Segment2 ++ (refs93Segment3 ++ (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs93Segment0 (refs93Segment1 ++ (refs93Segment2 ++ (refs93Segment3 ++ (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs93Segment1 (refs93Segment2 ++ (refs93Segment3 ++ (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs93Segment2 (refs93Segment3 ++ (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs93Segment3 (refs93Segment4 ++ (refs93Segment5 ++ refs93Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs93Segment4 (refs93Segment5 ++ refs93Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs93Segment5 refs93Segment6 (by decide) (by decide)]
  decide

theorem row94_checked : checkIndexedRow table [2,2,2,2,2,2,1] classes refs94 = true := by
  change checkIndexedRow table [2,2,2,2,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs94Segment0 ++ (refs94Segment1 ++ (refs94Segment2 ++ (refs94Segment3 ++ (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6)))))) = true
  rw [checkIndexedRow_append table [2,2,2,2,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs94Segment0 (refs94Segment1 ++ (refs94Segment2 ++ (refs94Segment3 ++ (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6))))) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs94Segment1 (refs94Segment2 ++ (refs94Segment3 ++ (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6)))) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs94Segment2 (refs94Segment3 ++ (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6))) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs94Segment3 (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6)) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,2,1] classSegment4 (classSegment5 ++ classSegment6) refs94Segment4 (refs94Segment5 ++ refs94Segment6) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,2,1] classSegment5 classSegment6 refs94Segment5 refs94Segment6 (by decide)]
  decide

theorem residue94_checked : (2 * indexedCoverSum table 13 classes refs34 refs94) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs94Segment0 ++ (refs94Segment1 ++ (refs94Segment2 ++ (refs94Segment3 ++ (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs94Segment0 (refs94Segment1 ++ (refs94Segment2 ++ (refs94Segment3 ++ (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs94Segment1 (refs94Segment2 ++ (refs94Segment3 ++ (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs94Segment2 (refs94Segment3 ++ (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs94Segment3 (refs94Segment4 ++ (refs94Segment5 ++ refs94Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs94Segment4 (refs94Segment5 ++ refs94Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs94Segment5 refs94Segment6 (by decide) (by decide)]
  decide

theorem row95_checked : checkIndexedRow table [2,2,2,2,2,1,1,1] classes refs95 = true := by
  change checkIndexedRow table [2,2,2,2,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs95Segment0 ++ (refs95Segment1 ++ (refs95Segment2 ++ (refs95Segment3 ++ (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6)))))) = true
  rw [checkIndexedRow_append table [2,2,2,2,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs95Segment0 (refs95Segment1 ++ (refs95Segment2 ++ (refs95Segment3 ++ (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6))))) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs95Segment1 (refs95Segment2 ++ (refs95Segment3 ++ (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6)))) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs95Segment2 (refs95Segment3 ++ (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6))) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs95Segment3 (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6)) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs95Segment4 (refs95Segment5 ++ refs95Segment6) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,1,1,1] classSegment5 classSegment6 refs95Segment5 refs95Segment6 (by decide)]
  decide

theorem residue95_checked : (2 * indexedCoverSum table 13 classes refs34 refs95) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs95Segment0 ++ (refs95Segment1 ++ (refs95Segment2 ++ (refs95Segment3 ++ (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs95Segment0 (refs95Segment1 ++ (refs95Segment2 ++ (refs95Segment3 ++ (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs95Segment1 (refs95Segment2 ++ (refs95Segment3 ++ (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs95Segment2 (refs95Segment3 ++ (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs95Segment3 (refs95Segment4 ++ (refs95Segment5 ++ refs95Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs95Segment4 (refs95Segment5 ++ refs95Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs95Segment5 refs95Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
