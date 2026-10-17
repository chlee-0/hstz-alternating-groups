import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row96_checked : checkIndexedRow table [2,2,2,2,1,1,1,1,1] classes refs96 = true := by
  change checkIndexedRow table [2,2,2,2,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs96Segment0 ++ (refs96Segment1 ++ (refs96Segment2 ++ (refs96Segment3 ++ (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6)))))) = true
  rw [checkIndexedRow_append table [2,2,2,2,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs96Segment0 (refs96Segment1 ++ (refs96Segment2 ++ (refs96Segment3 ++ (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6))))) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs96Segment1 (refs96Segment2 ++ (refs96Segment3 ++ (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6)))) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs96Segment2 (refs96Segment3 ++ (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6))) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs96Segment3 (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6)) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs96Segment4 (refs96Segment5 ++ refs96Segment6) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1,1,1] classSegment5 classSegment6 refs96Segment5 refs96Segment6 (by decide)]
  decide

theorem residue96_checked : (2 * indexedCoverSum table 13 classes refs34 refs96) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs96Segment0 ++ (refs96Segment1 ++ (refs96Segment2 ++ (refs96Segment3 ++ (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs96Segment0 (refs96Segment1 ++ (refs96Segment2 ++ (refs96Segment3 ++ (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs96Segment1 (refs96Segment2 ++ (refs96Segment3 ++ (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs96Segment2 (refs96Segment3 ++ (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs96Segment3 (refs96Segment4 ++ (refs96Segment5 ++ refs96Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs96Segment4 (refs96Segment5 ++ refs96Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs96Segment5 refs96Segment6 (by decide) (by decide)]
  decide

theorem row97_checked : checkIndexedRow table [2,2,2,1,1,1,1,1,1,1] classes refs97 = true := by
  change checkIndexedRow table [2,2,2,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs97Segment0 ++ (refs97Segment1 ++ (refs97Segment2 ++ (refs97Segment3 ++ (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6)))))) = true
  rw [checkIndexedRow_append table [2,2,2,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs97Segment0 (refs97Segment1 ++ (refs97Segment2 ++ (refs97Segment3 ++ (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6))))) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs97Segment1 (refs97Segment2 ++ (refs97Segment3 ++ (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6)))) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs97Segment2 (refs97Segment3 ++ (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6))) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs97Segment3 (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6)) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs97Segment4 (refs97Segment5 ++ refs97Segment6) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1,1,1] classSegment5 classSegment6 refs97Segment5 refs97Segment6 (by decide)]
  decide

theorem residue97_checked : (2 * indexedCoverSum table 13 classes refs34 refs97) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs97Segment0 ++ (refs97Segment1 ++ (refs97Segment2 ++ (refs97Segment3 ++ (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs97Segment0 (refs97Segment1 ++ (refs97Segment2 ++ (refs97Segment3 ++ (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs97Segment1 (refs97Segment2 ++ (refs97Segment3 ++ (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs97Segment2 (refs97Segment3 ++ (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs97Segment3 (refs97Segment4 ++ (refs97Segment5 ++ refs97Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs97Segment4 (refs97Segment5 ++ refs97Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs97Segment5 refs97Segment6 (by decide) (by decide)]
  decide

theorem row98_checked : checkIndexedRow table [2,2,1,1,1,1,1,1,1,1,1] classes refs98 = true := by
  change checkIndexedRow table [2,2,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs98Segment0 ++ (refs98Segment1 ++ (refs98Segment2 ++ (refs98Segment3 ++ (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6)))))) = true
  rw [checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs98Segment0 (refs98Segment1 ++ (refs98Segment2 ++ (refs98Segment3 ++ (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6))))) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs98Segment1 (refs98Segment2 ++ (refs98Segment3 ++ (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6)))) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs98Segment2 (refs98Segment3 ++ (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6))) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs98Segment3 (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6)) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs98Segment4 (refs98Segment5 ++ refs98Segment6) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1,1] classSegment5 classSegment6 refs98Segment5 refs98Segment6 (by decide)]
  decide

theorem residue98_checked : (2 * indexedCoverSum table 13 classes refs34 refs98) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs98Segment0 ++ (refs98Segment1 ++ (refs98Segment2 ++ (refs98Segment3 ++ (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs98Segment0 (refs98Segment1 ++ (refs98Segment2 ++ (refs98Segment3 ++ (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs98Segment1 (refs98Segment2 ++ (refs98Segment3 ++ (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs98Segment2 (refs98Segment3 ++ (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs98Segment3 (refs98Segment4 ++ (refs98Segment5 ++ refs98Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs98Segment4 (refs98Segment5 ++ refs98Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs98Segment5 refs98Segment6 (by decide) (by decide)]
  decide

theorem row99_checked : checkIndexedRow table [2,1,1,1,1,1,1,1,1,1,1,1] classes refs99 = true := by
  change checkIndexedRow table [2,1,1,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs99Segment0 ++ (refs99Segment1 ++ (refs99Segment2 ++ (refs99Segment3 ++ (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6)))))) = true
  rw [checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs99Segment0 (refs99Segment1 ++ (refs99Segment2 ++ (refs99Segment3 ++ (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6))))) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs99Segment1 (refs99Segment2 ++ (refs99Segment3 ++ (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6)))) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs99Segment2 (refs99Segment3 ++ (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6))) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs99Segment3 (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6)) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs99Segment4 (refs99Segment5 ++ refs99Segment6) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1,1] classSegment5 classSegment6 refs99Segment5 refs99Segment6 (by decide)]
  decide

theorem residue99_checked : (2 * indexedCoverSum table 13 classes refs34 refs99) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs99Segment0 ++ (refs99Segment1 ++ (refs99Segment2 ++ (refs99Segment3 ++ (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs99Segment0 (refs99Segment1 ++ (refs99Segment2 ++ (refs99Segment3 ++ (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs99Segment1 (refs99Segment2 ++ (refs99Segment3 ++ (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs99Segment2 (refs99Segment3 ++ (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs99Segment3 (refs99Segment4 ++ (refs99Segment5 ++ refs99Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs99Segment4 (refs99Segment5 ++ refs99Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs99Segment5 refs99Segment6 (by decide) (by decide)]
  decide

theorem row100_checked : checkIndexedRow table [1,1,1,1,1,1,1,1,1,1,1,1,1] classes refs100 = true := by
  change checkIndexedRow table [1,1,1,1,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs100Segment0 ++ (refs100Segment1 ++ (refs100Segment2 ++ (refs100Segment3 ++ (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6)))))) = true
  rw [checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs100Segment0 (refs100Segment1 ++ (refs100Segment2 ++ (refs100Segment3 ++ (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6))))) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs100Segment1 (refs100Segment2 ++ (refs100Segment3 ++ (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6)))) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs100Segment2 (refs100Segment3 ++ (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6))) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs100Segment3 (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6)) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs100Segment4 (refs100Segment5 ++ refs100Segment6) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1,1] classSegment5 classSegment6 refs100Segment5 refs100Segment6 (by decide)]
  decide

theorem residue100_checked : (2 * indexedCoverSum table 13 classes refs34 refs100) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs100Segment0 ++ (refs100Segment1 ++ (refs100Segment2 ++ (refs100Segment3 ++ (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs100Segment0 (refs100Segment1 ++ (refs100Segment2 ++ (refs100Segment3 ++ (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs100Segment1 (refs100Segment2 ++ (refs100Segment3 ++ (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs100Segment2 (refs100Segment3 ++ (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs100Segment3 (refs100Segment4 ++ (refs100Segment5 ++ refs100Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs100Segment4 (refs100Segment5 ++ refs100Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs100Segment5 refs100Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
