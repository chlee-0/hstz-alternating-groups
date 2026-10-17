import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row32_checked : checkIndexedRow table [6,5,1,1] classes refs32 = true := by
  change checkIndexedRow table [6,5,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs32Segment0 ++ (refs32Segment1 ++ (refs32Segment2 ++ (refs32Segment3 ++ (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6)))))) = true
  rw [checkIndexedRow_append table [6,5,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs32Segment0 (refs32Segment1 ++ (refs32Segment2 ++ (refs32Segment3 ++ (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6))))) (by decide),
    checkIndexedRow_append table [6,5,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs32Segment1 (refs32Segment2 ++ (refs32Segment3 ++ (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6)))) (by decide),
    checkIndexedRow_append table [6,5,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs32Segment2 (refs32Segment3 ++ (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6))) (by decide),
    checkIndexedRow_append table [6,5,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs32Segment3 (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6)) (by decide),
    checkIndexedRow_append table [6,5,1,1] classSegment4 (classSegment5 ++ classSegment6) refs32Segment4 (refs32Segment5 ++ refs32Segment6) (by decide),
    checkIndexedRow_append table [6,5,1,1] classSegment5 classSegment6 refs32Segment5 refs32Segment6 (by decide)]
  decide

theorem residue32_checked : (2 * indexedCoverSum table 13 classes refs34 refs32) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs32Segment0 ++ (refs32Segment1 ++ (refs32Segment2 ++ (refs32Segment3 ++ (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs32Segment0 (refs32Segment1 ++ (refs32Segment2 ++ (refs32Segment3 ++ (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs32Segment1 (refs32Segment2 ++ (refs32Segment3 ++ (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs32Segment2 (refs32Segment3 ++ (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs32Segment3 (refs32Segment4 ++ (refs32Segment5 ++ refs32Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs32Segment4 (refs32Segment5 ++ refs32Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs32Segment5 refs32Segment6 (by decide) (by decide)]
  decide

theorem row33_checked : checkIndexedRow table [6,4,3] classes refs33 = true := by
  change checkIndexedRow table [6,4,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6)))))) = true
  rw [checkIndexedRow_append table [6,4,3] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6))))) (by decide),
    checkIndexedRow_append table [6,4,3] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6)))) (by decide),
    checkIndexedRow_append table [6,4,3] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs33Segment2 (refs33Segment3 ++ (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6))) (by decide),
    checkIndexedRow_append table [6,4,3] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs33Segment3 (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6)) (by decide),
    checkIndexedRow_append table [6,4,3] classSegment4 (classSegment5 ++ classSegment6) refs33Segment4 (refs33Segment5 ++ refs33Segment6) (by decide),
    checkIndexedRow_append table [6,4,3] classSegment5 classSegment6 refs33Segment5 refs33Segment6 (by decide)]
  decide

theorem residue33_checked : (2 * indexedCoverSum table 13 classes refs34 refs33) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs33Segment2 (refs33Segment3 ++ (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs33Segment3 (refs33Segment4 ++ (refs33Segment5 ++ refs33Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs33Segment4 (refs33Segment5 ++ refs33Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs33Segment5 refs33Segment6 (by decide) (by decide)]
  decide

theorem row34_checked : checkIndexedRow table [6,4,2,1] classes refs34 = true := by
  change checkIndexedRow table [6,4,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) = true
  rw [checkIndexedRow_append table [6,4,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) (by decide),
    checkIndexedRow_append table [6,4,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) (by decide),
    checkIndexedRow_append table [6,4,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) (by decide),
    checkIndexedRow_append table [6,4,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) (by decide),
    checkIndexedRow_append table [6,4,2,1] classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) (by decide),
    checkIndexedRow_append table [6,4,2,1] classSegment5 classSegment6 refs34Segment5 refs34Segment6 (by decide)]
  decide

theorem residue34_checked : (2 * indexedCoverSum table 13 classes refs34 refs34) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs34Segment5 refs34Segment6 (by decide) (by decide)]
  decide

theorem row35_checked : checkIndexedRow table [6,4,1,1,1] classes refs35 = true := by
  change checkIndexedRow table [6,4,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs35Segment0 ++ (refs35Segment1 ++ (refs35Segment2 ++ (refs35Segment3 ++ (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6)))))) = true
  rw [checkIndexedRow_append table [6,4,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs35Segment0 (refs35Segment1 ++ (refs35Segment2 ++ (refs35Segment3 ++ (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6))))) (by decide),
    checkIndexedRow_append table [6,4,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs35Segment1 (refs35Segment2 ++ (refs35Segment3 ++ (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6)))) (by decide),
    checkIndexedRow_append table [6,4,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs35Segment2 (refs35Segment3 ++ (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6))) (by decide),
    checkIndexedRow_append table [6,4,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs35Segment3 (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6)) (by decide),
    checkIndexedRow_append table [6,4,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs35Segment4 (refs35Segment5 ++ refs35Segment6) (by decide),
    checkIndexedRow_append table [6,4,1,1,1] classSegment5 classSegment6 refs35Segment5 refs35Segment6 (by decide)]
  decide

theorem residue35_checked : (2 * indexedCoverSum table 13 classes refs34 refs35) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs35Segment0 ++ (refs35Segment1 ++ (refs35Segment2 ++ (refs35Segment3 ++ (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs35Segment0 (refs35Segment1 ++ (refs35Segment2 ++ (refs35Segment3 ++ (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs35Segment1 (refs35Segment2 ++ (refs35Segment3 ++ (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs35Segment2 (refs35Segment3 ++ (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs35Segment3 (refs35Segment4 ++ (refs35Segment5 ++ refs35Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs35Segment4 (refs35Segment5 ++ refs35Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs35Segment5 refs35Segment6 (by decide) (by decide)]
  decide

theorem row36_checked : checkIndexedRow table [6,3,3,1] classes refs36 = true := by
  change checkIndexedRow table [6,3,3,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs36Segment0 ++ (refs36Segment1 ++ (refs36Segment2 ++ (refs36Segment3 ++ (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6)))))) = true
  rw [checkIndexedRow_append table [6,3,3,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs36Segment0 (refs36Segment1 ++ (refs36Segment2 ++ (refs36Segment3 ++ (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6))))) (by decide),
    checkIndexedRow_append table [6,3,3,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs36Segment1 (refs36Segment2 ++ (refs36Segment3 ++ (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6)))) (by decide),
    checkIndexedRow_append table [6,3,3,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs36Segment2 (refs36Segment3 ++ (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6))) (by decide),
    checkIndexedRow_append table [6,3,3,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs36Segment3 (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6)) (by decide),
    checkIndexedRow_append table [6,3,3,1] classSegment4 (classSegment5 ++ classSegment6) refs36Segment4 (refs36Segment5 ++ refs36Segment6) (by decide),
    checkIndexedRow_append table [6,3,3,1] classSegment5 classSegment6 refs36Segment5 refs36Segment6 (by decide)]
  decide

theorem residue36_checked : (2 * indexedCoverSum table 13 classes refs34 refs36) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs36Segment0 ++ (refs36Segment1 ++ (refs36Segment2 ++ (refs36Segment3 ++ (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs36Segment0 (refs36Segment1 ++ (refs36Segment2 ++ (refs36Segment3 ++ (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs36Segment1 (refs36Segment2 ++ (refs36Segment3 ++ (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs36Segment2 (refs36Segment3 ++ (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs36Segment3 (refs36Segment4 ++ (refs36Segment5 ++ refs36Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs36Segment4 (refs36Segment5 ++ refs36Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs36Segment5 refs36Segment6 (by decide) (by decide)]
  decide

theorem row37_checked : checkIndexedRow table [6,3,2,2] classes refs37 = true := by
  change checkIndexedRow table [6,3,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs37Segment0 ++ (refs37Segment1 ++ (refs37Segment2 ++ (refs37Segment3 ++ (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6)))))) = true
  rw [checkIndexedRow_append table [6,3,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs37Segment0 (refs37Segment1 ++ (refs37Segment2 ++ (refs37Segment3 ++ (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6))))) (by decide),
    checkIndexedRow_append table [6,3,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs37Segment1 (refs37Segment2 ++ (refs37Segment3 ++ (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6)))) (by decide),
    checkIndexedRow_append table [6,3,2,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs37Segment2 (refs37Segment3 ++ (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6))) (by decide),
    checkIndexedRow_append table [6,3,2,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs37Segment3 (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6)) (by decide),
    checkIndexedRow_append table [6,3,2,2] classSegment4 (classSegment5 ++ classSegment6) refs37Segment4 (refs37Segment5 ++ refs37Segment6) (by decide),
    checkIndexedRow_append table [6,3,2,2] classSegment5 classSegment6 refs37Segment5 refs37Segment6 (by decide)]
  decide

theorem residue37_checked : (2 * indexedCoverSum table 13 classes refs34 refs37) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs37Segment0 ++ (refs37Segment1 ++ (refs37Segment2 ++ (refs37Segment3 ++ (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs37Segment0 (refs37Segment1 ++ (refs37Segment2 ++ (refs37Segment3 ++ (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs37Segment1 (refs37Segment2 ++ (refs37Segment3 ++ (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs37Segment2 (refs37Segment3 ++ (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs37Segment3 (refs37Segment4 ++ (refs37Segment5 ++ refs37Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs37Segment4 (refs37Segment5 ++ refs37Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs37Segment5 refs37Segment6 (by decide) (by decide)]
  decide

theorem row38_checked : checkIndexedRow table [6,3,2,1,1] classes refs38 = true := by
  change checkIndexedRow table [6,3,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs38Segment0 ++ (refs38Segment1 ++ (refs38Segment2 ++ (refs38Segment3 ++ (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6)))))) = true
  rw [checkIndexedRow_append table [6,3,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs38Segment0 (refs38Segment1 ++ (refs38Segment2 ++ (refs38Segment3 ++ (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6))))) (by decide),
    checkIndexedRow_append table [6,3,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs38Segment1 (refs38Segment2 ++ (refs38Segment3 ++ (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6)))) (by decide),
    checkIndexedRow_append table [6,3,2,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs38Segment2 (refs38Segment3 ++ (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6))) (by decide),
    checkIndexedRow_append table [6,3,2,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs38Segment3 (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6)) (by decide),
    checkIndexedRow_append table [6,3,2,1,1] classSegment4 (classSegment5 ++ classSegment6) refs38Segment4 (refs38Segment5 ++ refs38Segment6) (by decide),
    checkIndexedRow_append table [6,3,2,1,1] classSegment5 classSegment6 refs38Segment5 refs38Segment6 (by decide)]
  decide

theorem residue38_checked : (2 * indexedCoverSum table 13 classes refs34 refs38) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs38Segment0 ++ (refs38Segment1 ++ (refs38Segment2 ++ (refs38Segment3 ++ (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs38Segment0 (refs38Segment1 ++ (refs38Segment2 ++ (refs38Segment3 ++ (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs38Segment1 (refs38Segment2 ++ (refs38Segment3 ++ (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs38Segment2 (refs38Segment3 ++ (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs38Segment3 (refs38Segment4 ++ (refs38Segment5 ++ refs38Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs38Segment4 (refs38Segment5 ++ refs38Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs38Segment5 refs38Segment6 (by decide) (by decide)]
  decide

theorem row39_checked : checkIndexedRow table [6,3,1,1,1,1] classes refs39 = true := by
  change checkIndexedRow table [6,3,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs39Segment0 ++ (refs39Segment1 ++ (refs39Segment2 ++ (refs39Segment3 ++ (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6)))))) = true
  rw [checkIndexedRow_append table [6,3,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs39Segment0 (refs39Segment1 ++ (refs39Segment2 ++ (refs39Segment3 ++ (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6))))) (by decide),
    checkIndexedRow_append table [6,3,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs39Segment1 (refs39Segment2 ++ (refs39Segment3 ++ (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6)))) (by decide),
    checkIndexedRow_append table [6,3,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs39Segment2 (refs39Segment3 ++ (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6))) (by decide),
    checkIndexedRow_append table [6,3,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs39Segment3 (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6)) (by decide),
    checkIndexedRow_append table [6,3,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs39Segment4 (refs39Segment5 ++ refs39Segment6) (by decide),
    checkIndexedRow_append table [6,3,1,1,1,1] classSegment5 classSegment6 refs39Segment5 refs39Segment6 (by decide)]
  decide

theorem residue39_checked : (2 * indexedCoverSum table 13 classes refs34 refs39) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs39Segment0 ++ (refs39Segment1 ++ (refs39Segment2 ++ (refs39Segment3 ++ (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs39Segment0 (refs39Segment1 ++ (refs39Segment2 ++ (refs39Segment3 ++ (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs39Segment1 (refs39Segment2 ++ (refs39Segment3 ++ (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs39Segment2 (refs39Segment3 ++ (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs39Segment3 (refs39Segment4 ++ (refs39Segment5 ++ refs39Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs39Segment4 (refs39Segment5 ++ refs39Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs39Segment5 refs39Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
