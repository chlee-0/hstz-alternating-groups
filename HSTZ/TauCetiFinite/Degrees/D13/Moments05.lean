import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row40_checked : checkIndexedRow table [6,2,2,2,1] classes refs40 = true := by
  change checkIndexedRow table [6,2,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs40Segment0 ++ (refs40Segment1 ++ (refs40Segment2 ++ (refs40Segment3 ++ (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6)))))) = true
  rw [checkIndexedRow_append table [6,2,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs40Segment0 (refs40Segment1 ++ (refs40Segment2 ++ (refs40Segment3 ++ (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6))))) (by decide),
    checkIndexedRow_append table [6,2,2,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs40Segment1 (refs40Segment2 ++ (refs40Segment3 ++ (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6)))) (by decide),
    checkIndexedRow_append table [6,2,2,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs40Segment2 (refs40Segment3 ++ (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6))) (by decide),
    checkIndexedRow_append table [6,2,2,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs40Segment3 (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6)) (by decide),
    checkIndexedRow_append table [6,2,2,2,1] classSegment4 (classSegment5 ++ classSegment6) refs40Segment4 (refs40Segment5 ++ refs40Segment6) (by decide),
    checkIndexedRow_append table [6,2,2,2,1] classSegment5 classSegment6 refs40Segment5 refs40Segment6 (by decide)]
  decide

theorem residue40_checked : (2 * indexedCoverSum table 13 classes refs34 refs40) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs40Segment0 ++ (refs40Segment1 ++ (refs40Segment2 ++ (refs40Segment3 ++ (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs40Segment0 (refs40Segment1 ++ (refs40Segment2 ++ (refs40Segment3 ++ (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs40Segment1 (refs40Segment2 ++ (refs40Segment3 ++ (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs40Segment2 (refs40Segment3 ++ (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs40Segment3 (refs40Segment4 ++ (refs40Segment5 ++ refs40Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs40Segment4 (refs40Segment5 ++ refs40Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs40Segment5 refs40Segment6 (by decide) (by decide)]
  decide

theorem row41_checked : checkIndexedRow table [6,2,2,1,1,1] classes refs41 = true := by
  change checkIndexedRow table [6,2,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs41Segment0 ++ (refs41Segment1 ++ (refs41Segment2 ++ (refs41Segment3 ++ (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6)))))) = true
  rw [checkIndexedRow_append table [6,2,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs41Segment0 (refs41Segment1 ++ (refs41Segment2 ++ (refs41Segment3 ++ (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6))))) (by decide),
    checkIndexedRow_append table [6,2,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs41Segment1 (refs41Segment2 ++ (refs41Segment3 ++ (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6)))) (by decide),
    checkIndexedRow_append table [6,2,2,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs41Segment2 (refs41Segment3 ++ (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6))) (by decide),
    checkIndexedRow_append table [6,2,2,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs41Segment3 (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6)) (by decide),
    checkIndexedRow_append table [6,2,2,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs41Segment4 (refs41Segment5 ++ refs41Segment6) (by decide),
    checkIndexedRow_append table [6,2,2,1,1,1] classSegment5 classSegment6 refs41Segment5 refs41Segment6 (by decide)]
  decide

theorem residue41_checked : (2 * indexedCoverSum table 13 classes refs34 refs41) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs41Segment0 ++ (refs41Segment1 ++ (refs41Segment2 ++ (refs41Segment3 ++ (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs41Segment0 (refs41Segment1 ++ (refs41Segment2 ++ (refs41Segment3 ++ (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs41Segment1 (refs41Segment2 ++ (refs41Segment3 ++ (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs41Segment2 (refs41Segment3 ++ (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs41Segment3 (refs41Segment4 ++ (refs41Segment5 ++ refs41Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs41Segment4 (refs41Segment5 ++ refs41Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs41Segment5 refs41Segment6 (by decide) (by decide)]
  decide

theorem row42_checked : checkIndexedRow table [6,2,1,1,1,1,1] classes refs42 = true := by
  change checkIndexedRow table [6,2,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs42Segment0 ++ (refs42Segment1 ++ (refs42Segment2 ++ (refs42Segment3 ++ (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6)))))) = true
  rw [checkIndexedRow_append table [6,2,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs42Segment0 (refs42Segment1 ++ (refs42Segment2 ++ (refs42Segment3 ++ (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6))))) (by decide),
    checkIndexedRow_append table [6,2,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs42Segment1 (refs42Segment2 ++ (refs42Segment3 ++ (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6)))) (by decide),
    checkIndexedRow_append table [6,2,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs42Segment2 (refs42Segment3 ++ (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6))) (by decide),
    checkIndexedRow_append table [6,2,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs42Segment3 (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6)) (by decide),
    checkIndexedRow_append table [6,2,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs42Segment4 (refs42Segment5 ++ refs42Segment6) (by decide),
    checkIndexedRow_append table [6,2,1,1,1,1,1] classSegment5 classSegment6 refs42Segment5 refs42Segment6 (by decide)]
  decide

theorem residue42_checked : (2 * indexedCoverSum table 13 classes refs34 refs42) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs42Segment0 ++ (refs42Segment1 ++ (refs42Segment2 ++ (refs42Segment3 ++ (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs42Segment0 (refs42Segment1 ++ (refs42Segment2 ++ (refs42Segment3 ++ (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs42Segment1 (refs42Segment2 ++ (refs42Segment3 ++ (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs42Segment2 (refs42Segment3 ++ (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs42Segment3 (refs42Segment4 ++ (refs42Segment5 ++ refs42Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs42Segment4 (refs42Segment5 ++ refs42Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs42Segment5 refs42Segment6 (by decide) (by decide)]
  decide

theorem row43_checked : checkIndexedRow table [6,1,1,1,1,1,1,1] classes refs43 = true := by
  change checkIndexedRow table [6,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs43Segment0 ++ (refs43Segment1 ++ (refs43Segment2 ++ (refs43Segment3 ++ (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6)))))) = true
  rw [checkIndexedRow_append table [6,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs43Segment0 (refs43Segment1 ++ (refs43Segment2 ++ (refs43Segment3 ++ (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6))))) (by decide),
    checkIndexedRow_append table [6,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs43Segment1 (refs43Segment2 ++ (refs43Segment3 ++ (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6)))) (by decide),
    checkIndexedRow_append table [6,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs43Segment2 (refs43Segment3 ++ (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6))) (by decide),
    checkIndexedRow_append table [6,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs43Segment3 (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6)) (by decide),
    checkIndexedRow_append table [6,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs43Segment4 (refs43Segment5 ++ refs43Segment6) (by decide),
    checkIndexedRow_append table [6,1,1,1,1,1,1,1] classSegment5 classSegment6 refs43Segment5 refs43Segment6 (by decide)]
  decide

theorem residue43_checked : (2 * indexedCoverSum table 13 classes refs34 refs43) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs43Segment0 ++ (refs43Segment1 ++ (refs43Segment2 ++ (refs43Segment3 ++ (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs43Segment0 (refs43Segment1 ++ (refs43Segment2 ++ (refs43Segment3 ++ (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs43Segment1 (refs43Segment2 ++ (refs43Segment3 ++ (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs43Segment2 (refs43Segment3 ++ (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs43Segment3 (refs43Segment4 ++ (refs43Segment5 ++ refs43Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs43Segment4 (refs43Segment5 ++ refs43Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs43Segment5 refs43Segment6 (by decide) (by decide)]
  decide

theorem row44_checked : checkIndexedRow table [5,5,3] classes refs44 = true := by
  change checkIndexedRow table [5,5,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs44Segment0 ++ (refs44Segment1 ++ (refs44Segment2 ++ (refs44Segment3 ++ (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6)))))) = true
  rw [checkIndexedRow_append table [5,5,3] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs44Segment0 (refs44Segment1 ++ (refs44Segment2 ++ (refs44Segment3 ++ (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6))))) (by decide),
    checkIndexedRow_append table [5,5,3] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs44Segment1 (refs44Segment2 ++ (refs44Segment3 ++ (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6)))) (by decide),
    checkIndexedRow_append table [5,5,3] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs44Segment2 (refs44Segment3 ++ (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6))) (by decide),
    checkIndexedRow_append table [5,5,3] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs44Segment3 (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6)) (by decide),
    checkIndexedRow_append table [5,5,3] classSegment4 (classSegment5 ++ classSegment6) refs44Segment4 (refs44Segment5 ++ refs44Segment6) (by decide),
    checkIndexedRow_append table [5,5,3] classSegment5 classSegment6 refs44Segment5 refs44Segment6 (by decide)]
  decide

theorem residue44_checked : (2 * indexedCoverSum table 13 classes refs34 refs44) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs44Segment0 ++ (refs44Segment1 ++ (refs44Segment2 ++ (refs44Segment3 ++ (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs44Segment0 (refs44Segment1 ++ (refs44Segment2 ++ (refs44Segment3 ++ (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs44Segment1 (refs44Segment2 ++ (refs44Segment3 ++ (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs44Segment2 (refs44Segment3 ++ (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs44Segment3 (refs44Segment4 ++ (refs44Segment5 ++ refs44Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs44Segment4 (refs44Segment5 ++ refs44Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs44Segment5 refs44Segment6 (by decide) (by decide)]
  decide

theorem row45_checked : checkIndexedRow table [5,5,2,1] classes refs45 = true := by
  change checkIndexedRow table [5,5,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs45Segment0 ++ (refs45Segment1 ++ (refs45Segment2 ++ (refs45Segment3 ++ (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6)))))) = true
  rw [checkIndexedRow_append table [5,5,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs45Segment0 (refs45Segment1 ++ (refs45Segment2 ++ (refs45Segment3 ++ (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6))))) (by decide),
    checkIndexedRow_append table [5,5,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs45Segment1 (refs45Segment2 ++ (refs45Segment3 ++ (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6)))) (by decide),
    checkIndexedRow_append table [5,5,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs45Segment2 (refs45Segment3 ++ (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6))) (by decide),
    checkIndexedRow_append table [5,5,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs45Segment3 (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6)) (by decide),
    checkIndexedRow_append table [5,5,2,1] classSegment4 (classSegment5 ++ classSegment6) refs45Segment4 (refs45Segment5 ++ refs45Segment6) (by decide),
    checkIndexedRow_append table [5,5,2,1] classSegment5 classSegment6 refs45Segment5 refs45Segment6 (by decide)]
  decide

theorem residue45_checked : (2 * indexedCoverSum table 13 classes refs34 refs45) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs45Segment0 ++ (refs45Segment1 ++ (refs45Segment2 ++ (refs45Segment3 ++ (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs45Segment0 (refs45Segment1 ++ (refs45Segment2 ++ (refs45Segment3 ++ (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs45Segment1 (refs45Segment2 ++ (refs45Segment3 ++ (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs45Segment2 (refs45Segment3 ++ (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs45Segment3 (refs45Segment4 ++ (refs45Segment5 ++ refs45Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs45Segment4 (refs45Segment5 ++ refs45Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs45Segment5 refs45Segment6 (by decide) (by decide)]
  decide

theorem row46_checked : checkIndexedRow table [5,5,1,1,1] classes refs46 = true := by
  change checkIndexedRow table [5,5,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs46Segment0 ++ (refs46Segment1 ++ (refs46Segment2 ++ (refs46Segment3 ++ (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6)))))) = true
  rw [checkIndexedRow_append table [5,5,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs46Segment0 (refs46Segment1 ++ (refs46Segment2 ++ (refs46Segment3 ++ (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6))))) (by decide),
    checkIndexedRow_append table [5,5,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs46Segment1 (refs46Segment2 ++ (refs46Segment3 ++ (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6)))) (by decide),
    checkIndexedRow_append table [5,5,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs46Segment2 (refs46Segment3 ++ (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6))) (by decide),
    checkIndexedRow_append table [5,5,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs46Segment3 (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6)) (by decide),
    checkIndexedRow_append table [5,5,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs46Segment4 (refs46Segment5 ++ refs46Segment6) (by decide),
    checkIndexedRow_append table [5,5,1,1,1] classSegment5 classSegment6 refs46Segment5 refs46Segment6 (by decide)]
  decide

theorem residue46_checked : (2 * indexedCoverSum table 13 classes refs34 refs46) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs46Segment0 ++ (refs46Segment1 ++ (refs46Segment2 ++ (refs46Segment3 ++ (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs46Segment0 (refs46Segment1 ++ (refs46Segment2 ++ (refs46Segment3 ++ (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs46Segment1 (refs46Segment2 ++ (refs46Segment3 ++ (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs46Segment2 (refs46Segment3 ++ (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs46Segment3 (refs46Segment4 ++ (refs46Segment5 ++ refs46Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs46Segment4 (refs46Segment5 ++ refs46Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs46Segment5 refs46Segment6 (by decide) (by decide)]
  decide

theorem row47_checked : checkIndexedRow table [5,4,4] classes refs47 = true := by
  change checkIndexedRow table [5,4,4] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs47Segment0 ++ (refs47Segment1 ++ (refs47Segment2 ++ (refs47Segment3 ++ (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6)))))) = true
  rw [checkIndexedRow_append table [5,4,4] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs47Segment0 (refs47Segment1 ++ (refs47Segment2 ++ (refs47Segment3 ++ (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6))))) (by decide),
    checkIndexedRow_append table [5,4,4] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs47Segment1 (refs47Segment2 ++ (refs47Segment3 ++ (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6)))) (by decide),
    checkIndexedRow_append table [5,4,4] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs47Segment2 (refs47Segment3 ++ (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6))) (by decide),
    checkIndexedRow_append table [5,4,4] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs47Segment3 (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6)) (by decide),
    checkIndexedRow_append table [5,4,4] classSegment4 (classSegment5 ++ classSegment6) refs47Segment4 (refs47Segment5 ++ refs47Segment6) (by decide),
    checkIndexedRow_append table [5,4,4] classSegment5 classSegment6 refs47Segment5 refs47Segment6 (by decide)]
  decide

theorem residue47_checked : (2 * indexedCoverSum table 13 classes refs34 refs47) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs47Segment0 ++ (refs47Segment1 ++ (refs47Segment2 ++ (refs47Segment3 ++ (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs47Segment0 (refs47Segment1 ++ (refs47Segment2 ++ (refs47Segment3 ++ (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs47Segment1 (refs47Segment2 ++ (refs47Segment3 ++ (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs47Segment2 (refs47Segment3 ++ (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs47Segment3 (refs47Segment4 ++ (refs47Segment5 ++ refs47Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs47Segment4 (refs47Segment5 ++ refs47Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs47Segment5 refs47Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
