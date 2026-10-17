import HSTZ.TauCetiFinite.Degrees.D13.Segments

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem row64_checked : checkIndexedRow table [4,4,3,1,1] classes refs64 = true := by
  change checkIndexedRow table [4,4,3,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs64Segment0 ++ (refs64Segment1 ++ (refs64Segment2 ++ (refs64Segment3 ++ (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6)))))) = true
  rw [checkIndexedRow_append table [4,4,3,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs64Segment0 (refs64Segment1 ++ (refs64Segment2 ++ (refs64Segment3 ++ (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6))))) (by decide),
    checkIndexedRow_append table [4,4,3,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs64Segment1 (refs64Segment2 ++ (refs64Segment3 ++ (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6)))) (by decide),
    checkIndexedRow_append table [4,4,3,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs64Segment2 (refs64Segment3 ++ (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6))) (by decide),
    checkIndexedRow_append table [4,4,3,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs64Segment3 (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6)) (by decide),
    checkIndexedRow_append table [4,4,3,1,1] classSegment4 (classSegment5 ++ classSegment6) refs64Segment4 (refs64Segment5 ++ refs64Segment6) (by decide),
    checkIndexedRow_append table [4,4,3,1,1] classSegment5 classSegment6 refs64Segment5 refs64Segment6 (by decide)]
  decide

theorem residue64_checked : (2 * indexedCoverSum table 13 classes refs34 refs64) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs64Segment0 ++ (refs64Segment1 ++ (refs64Segment2 ++ (refs64Segment3 ++ (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs64Segment0 (refs64Segment1 ++ (refs64Segment2 ++ (refs64Segment3 ++ (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs64Segment1 (refs64Segment2 ++ (refs64Segment3 ++ (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs64Segment2 (refs64Segment3 ++ (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs64Segment3 (refs64Segment4 ++ (refs64Segment5 ++ refs64Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs64Segment4 (refs64Segment5 ++ refs64Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs64Segment5 refs64Segment6 (by decide) (by decide)]
  decide

theorem row65_checked : checkIndexedRow table [4,4,2,2,1] classes refs65 = true := by
  change checkIndexedRow table [4,4,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs65Segment0 ++ (refs65Segment1 ++ (refs65Segment2 ++ (refs65Segment3 ++ (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6)))))) = true
  rw [checkIndexedRow_append table [4,4,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs65Segment0 (refs65Segment1 ++ (refs65Segment2 ++ (refs65Segment3 ++ (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6))))) (by decide),
    checkIndexedRow_append table [4,4,2,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs65Segment1 (refs65Segment2 ++ (refs65Segment3 ++ (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6)))) (by decide),
    checkIndexedRow_append table [4,4,2,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs65Segment2 (refs65Segment3 ++ (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6))) (by decide),
    checkIndexedRow_append table [4,4,2,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs65Segment3 (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6)) (by decide),
    checkIndexedRow_append table [4,4,2,2,1] classSegment4 (classSegment5 ++ classSegment6) refs65Segment4 (refs65Segment5 ++ refs65Segment6) (by decide),
    checkIndexedRow_append table [4,4,2,2,1] classSegment5 classSegment6 refs65Segment5 refs65Segment6 (by decide)]
  decide

theorem residue65_checked : (2 * indexedCoverSum table 13 classes refs34 refs65) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs65Segment0 ++ (refs65Segment1 ++ (refs65Segment2 ++ (refs65Segment3 ++ (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs65Segment0 (refs65Segment1 ++ (refs65Segment2 ++ (refs65Segment3 ++ (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs65Segment1 (refs65Segment2 ++ (refs65Segment3 ++ (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs65Segment2 (refs65Segment3 ++ (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs65Segment3 (refs65Segment4 ++ (refs65Segment5 ++ refs65Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs65Segment4 (refs65Segment5 ++ refs65Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs65Segment5 refs65Segment6 (by decide) (by decide)]
  decide

theorem row66_checked : checkIndexedRow table [4,4,2,1,1,1] classes refs66 = true := by
  change checkIndexedRow table [4,4,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs66Segment0 ++ (refs66Segment1 ++ (refs66Segment2 ++ (refs66Segment3 ++ (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6)))))) = true
  rw [checkIndexedRow_append table [4,4,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs66Segment0 (refs66Segment1 ++ (refs66Segment2 ++ (refs66Segment3 ++ (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6))))) (by decide),
    checkIndexedRow_append table [4,4,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs66Segment1 (refs66Segment2 ++ (refs66Segment3 ++ (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6)))) (by decide),
    checkIndexedRow_append table [4,4,2,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs66Segment2 (refs66Segment3 ++ (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6))) (by decide),
    checkIndexedRow_append table [4,4,2,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs66Segment3 (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6)) (by decide),
    checkIndexedRow_append table [4,4,2,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs66Segment4 (refs66Segment5 ++ refs66Segment6) (by decide),
    checkIndexedRow_append table [4,4,2,1,1,1] classSegment5 classSegment6 refs66Segment5 refs66Segment6 (by decide)]
  decide

theorem residue66_checked : (2 * indexedCoverSum table 13 classes refs34 refs66) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs66Segment0 ++ (refs66Segment1 ++ (refs66Segment2 ++ (refs66Segment3 ++ (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs66Segment0 (refs66Segment1 ++ (refs66Segment2 ++ (refs66Segment3 ++ (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs66Segment1 (refs66Segment2 ++ (refs66Segment3 ++ (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs66Segment2 (refs66Segment3 ++ (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs66Segment3 (refs66Segment4 ++ (refs66Segment5 ++ refs66Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs66Segment4 (refs66Segment5 ++ refs66Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs66Segment5 refs66Segment6 (by decide) (by decide)]
  decide

theorem row67_checked : checkIndexedRow table [4,4,1,1,1,1,1] classes refs67 = true := by
  change checkIndexedRow table [4,4,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs67Segment0 ++ (refs67Segment1 ++ (refs67Segment2 ++ (refs67Segment3 ++ (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6)))))) = true
  rw [checkIndexedRow_append table [4,4,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs67Segment0 (refs67Segment1 ++ (refs67Segment2 ++ (refs67Segment3 ++ (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6))))) (by decide),
    checkIndexedRow_append table [4,4,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs67Segment1 (refs67Segment2 ++ (refs67Segment3 ++ (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6)))) (by decide),
    checkIndexedRow_append table [4,4,1,1,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs67Segment2 (refs67Segment3 ++ (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6))) (by decide),
    checkIndexedRow_append table [4,4,1,1,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs67Segment3 (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6)) (by decide),
    checkIndexedRow_append table [4,4,1,1,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs67Segment4 (refs67Segment5 ++ refs67Segment6) (by decide),
    checkIndexedRow_append table [4,4,1,1,1,1,1] classSegment5 classSegment6 refs67Segment5 refs67Segment6 (by decide)]
  decide

theorem residue67_checked : (2 * indexedCoverSum table 13 classes refs34 refs67) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs67Segment0 ++ (refs67Segment1 ++ (refs67Segment2 ++ (refs67Segment3 ++ (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs67Segment0 (refs67Segment1 ++ (refs67Segment2 ++ (refs67Segment3 ++ (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs67Segment1 (refs67Segment2 ++ (refs67Segment3 ++ (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs67Segment2 (refs67Segment3 ++ (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs67Segment3 (refs67Segment4 ++ (refs67Segment5 ++ refs67Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs67Segment4 (refs67Segment5 ++ refs67Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs67Segment5 refs67Segment6 (by decide) (by decide)]
  decide

theorem row68_checked : checkIndexedRow table [4,3,3,3] classes refs68 = true := by
  change checkIndexedRow table [4,3,3,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs68Segment0 ++ (refs68Segment1 ++ (refs68Segment2 ++ (refs68Segment3 ++ (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6)))))) = true
  rw [checkIndexedRow_append table [4,3,3,3] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs68Segment0 (refs68Segment1 ++ (refs68Segment2 ++ (refs68Segment3 ++ (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6))))) (by decide),
    checkIndexedRow_append table [4,3,3,3] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs68Segment1 (refs68Segment2 ++ (refs68Segment3 ++ (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6)))) (by decide),
    checkIndexedRow_append table [4,3,3,3] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs68Segment2 (refs68Segment3 ++ (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6))) (by decide),
    checkIndexedRow_append table [4,3,3,3] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs68Segment3 (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6)) (by decide),
    checkIndexedRow_append table [4,3,3,3] classSegment4 (classSegment5 ++ classSegment6) refs68Segment4 (refs68Segment5 ++ refs68Segment6) (by decide),
    checkIndexedRow_append table [4,3,3,3] classSegment5 classSegment6 refs68Segment5 refs68Segment6 (by decide)]
  decide

theorem residue68_checked : (2 * indexedCoverSum table 13 classes refs34 refs68) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs68Segment0 ++ (refs68Segment1 ++ (refs68Segment2 ++ (refs68Segment3 ++ (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs68Segment0 (refs68Segment1 ++ (refs68Segment2 ++ (refs68Segment3 ++ (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs68Segment1 (refs68Segment2 ++ (refs68Segment3 ++ (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs68Segment2 (refs68Segment3 ++ (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs68Segment3 (refs68Segment4 ++ (refs68Segment5 ++ refs68Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs68Segment4 (refs68Segment5 ++ refs68Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs68Segment5 refs68Segment6 (by decide) (by decide)]
  decide

theorem row69_checked : checkIndexedRow table [4,3,3,2,1] classes refs69 = true := by
  change checkIndexedRow table [4,3,3,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs69Segment0 ++ (refs69Segment1 ++ (refs69Segment2 ++ (refs69Segment3 ++ (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6)))))) = true
  rw [checkIndexedRow_append table [4,3,3,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs69Segment0 (refs69Segment1 ++ (refs69Segment2 ++ (refs69Segment3 ++ (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6))))) (by decide),
    checkIndexedRow_append table [4,3,3,2,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs69Segment1 (refs69Segment2 ++ (refs69Segment3 ++ (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6)))) (by decide),
    checkIndexedRow_append table [4,3,3,2,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs69Segment2 (refs69Segment3 ++ (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6))) (by decide),
    checkIndexedRow_append table [4,3,3,2,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs69Segment3 (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6)) (by decide),
    checkIndexedRow_append table [4,3,3,2,1] classSegment4 (classSegment5 ++ classSegment6) refs69Segment4 (refs69Segment5 ++ refs69Segment6) (by decide),
    checkIndexedRow_append table [4,3,3,2,1] classSegment5 classSegment6 refs69Segment5 refs69Segment6 (by decide)]
  decide

theorem residue69_checked : (2 * indexedCoverSum table 13 classes refs34 refs69) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs69Segment0 ++ (refs69Segment1 ++ (refs69Segment2 ++ (refs69Segment3 ++ (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs69Segment0 (refs69Segment1 ++ (refs69Segment2 ++ (refs69Segment3 ++ (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs69Segment1 (refs69Segment2 ++ (refs69Segment3 ++ (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs69Segment2 (refs69Segment3 ++ (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs69Segment3 (refs69Segment4 ++ (refs69Segment5 ++ refs69Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs69Segment4 (refs69Segment5 ++ refs69Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs69Segment5 refs69Segment6 (by decide) (by decide)]
  decide

theorem row70_checked : checkIndexedRow table [4,3,3,1,1,1] classes refs70 = true := by
  change checkIndexedRow table [4,3,3,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs70Segment0 ++ (refs70Segment1 ++ (refs70Segment2 ++ (refs70Segment3 ++ (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6)))))) = true
  rw [checkIndexedRow_append table [4,3,3,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs70Segment0 (refs70Segment1 ++ (refs70Segment2 ++ (refs70Segment3 ++ (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6))))) (by decide),
    checkIndexedRow_append table [4,3,3,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs70Segment1 (refs70Segment2 ++ (refs70Segment3 ++ (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6)))) (by decide),
    checkIndexedRow_append table [4,3,3,1,1,1] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs70Segment2 (refs70Segment3 ++ (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6))) (by decide),
    checkIndexedRow_append table [4,3,3,1,1,1] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs70Segment3 (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6)) (by decide),
    checkIndexedRow_append table [4,3,3,1,1,1] classSegment4 (classSegment5 ++ classSegment6) refs70Segment4 (refs70Segment5 ++ refs70Segment6) (by decide),
    checkIndexedRow_append table [4,3,3,1,1,1] classSegment5 classSegment6 refs70Segment5 refs70Segment6 (by decide)]
  decide

theorem residue70_checked : (2 * indexedCoverSum table 13 classes refs34 refs70) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs70Segment0 ++ (refs70Segment1 ++ (refs70Segment2 ++ (refs70Segment3 ++ (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs70Segment0 (refs70Segment1 ++ (refs70Segment2 ++ (refs70Segment3 ++ (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs70Segment1 (refs70Segment2 ++ (refs70Segment3 ++ (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs70Segment2 (refs70Segment3 ++ (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs70Segment3 (refs70Segment4 ++ (refs70Segment5 ++ refs70Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs70Segment4 (refs70Segment5 ++ refs70Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs70Segment5 refs70Segment6 (by decide) (by decide)]
  decide

theorem row71_checked : checkIndexedRow table [4,3,2,2,2] classes refs71 = true := by
  change checkIndexedRow table [4,3,2,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs71Segment0 ++ (refs71Segment1 ++ (refs71Segment2 ++ (refs71Segment3 ++ (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6)))))) = true
  rw [checkIndexedRow_append table [4,3,2,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs71Segment0 (refs71Segment1 ++ (refs71Segment2 ++ (refs71Segment3 ++ (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6))))) (by decide),
    checkIndexedRow_append table [4,3,2,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs71Segment1 (refs71Segment2 ++ (refs71Segment3 ++ (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6)))) (by decide),
    checkIndexedRow_append table [4,3,2,2,2] classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs71Segment2 (refs71Segment3 ++ (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6))) (by decide),
    checkIndexedRow_append table [4,3,2,2,2] classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs71Segment3 (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6)) (by decide),
    checkIndexedRow_append table [4,3,2,2,2] classSegment4 (classSegment5 ++ classSegment6) refs71Segment4 (refs71Segment5 ++ refs71Segment6) (by decide),
    checkIndexedRow_append table [4,3,2,2,2] classSegment5 classSegment6 refs71Segment5 refs71Segment6 (by decide)]
  decide

theorem residue71_checked : (2 * indexedCoverSum table 13 classes refs34 refs71) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 13 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))))) (refs34Segment0 ++ (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))))) (refs71Segment0 ++ (refs71Segment1 ++ (refs71Segment2 ++ (refs71Segment3 ++ (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6))))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 13 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))))) refs34Segment0 (refs34Segment1 ++ (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))))) refs71Segment0 (refs71Segment1 ++ (refs71Segment2 ++ (refs71Segment3 ++ (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6))))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment1 (classSegment2 ++ (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6)))) refs34Segment1 (refs34Segment2 ++ (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)))) refs71Segment1 (refs71Segment2 ++ (refs71Segment3 ++ (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6)))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment2 (classSegment3 ++ (classSegment4 ++ (classSegment5 ++ classSegment6))) refs34Segment2 (refs34Segment3 ++ (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6))) refs71Segment2 (refs71Segment3 ++ (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6))) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment3 (classSegment4 ++ (classSegment5 ++ classSegment6)) refs34Segment3 (refs34Segment4 ++ (refs34Segment5 ++ refs34Segment6)) refs71Segment3 (refs71Segment4 ++ (refs71Segment5 ++ refs71Segment6)) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment4 (classSegment5 ++ classSegment6) refs34Segment4 (refs34Segment5 ++ refs34Segment6) refs71Segment4 (refs71Segment5 ++ refs71Segment6) (by decide) (by decide),
    indexedCoverSum_append table 13 classSegment5 classSegment6 refs34Segment5 refs34Segment6 refs71Segment5 refs71Segment6 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D13
