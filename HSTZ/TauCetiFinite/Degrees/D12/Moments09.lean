import HSTZ.TauCetiFinite.Degrees.D12.Segments

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem row72_checked : checkIndexedRow table [2,2,2,2,1,1,1,1] classes refs72 = true := by
  change checkIndexedRow table [2,2,2,2,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs72Segment0 ++ (refs72Segment1 ++ (refs72Segment2 ++ (refs72Segment3 ++ refs72Segment4)))) = true
  rw [checkIndexedRow_append table [2,2,2,2,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs72Segment0 (refs72Segment1 ++ (refs72Segment2 ++ (refs72Segment3 ++ refs72Segment4))) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs72Segment1 (refs72Segment2 ++ (refs72Segment3 ++ refs72Segment4)) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs72Segment2 (refs72Segment3 ++ refs72Segment4) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1,1] classSegment3 classSegment4 refs72Segment3 refs72Segment4 (by decide)]
  decide

theorem residue72_checked : (2 * indexedCoverSum table 12 classes refs33 refs72) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs72Segment0 ++ (refs72Segment1 ++ (refs72Segment2 ++ (refs72Segment3 ++ refs72Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs72Segment0 (refs72Segment1 ++ (refs72Segment2 ++ (refs72Segment3 ++ refs72Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs72Segment1 (refs72Segment2 ++ (refs72Segment3 ++ refs72Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs72Segment2 (refs72Segment3 ++ refs72Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs72Segment3 refs72Segment4 (by decide) (by decide)]
  decide

theorem row73_checked : checkIndexedRow table [2,2,2,1,1,1,1,1,1] classes refs73 = true := by
  change checkIndexedRow table [2,2,2,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs73Segment0 ++ (refs73Segment1 ++ (refs73Segment2 ++ (refs73Segment3 ++ refs73Segment4)))) = true
  rw [checkIndexedRow_append table [2,2,2,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs73Segment0 (refs73Segment1 ++ (refs73Segment2 ++ (refs73Segment3 ++ refs73Segment4))) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs73Segment1 (refs73Segment2 ++ (refs73Segment3 ++ refs73Segment4)) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs73Segment2 (refs73Segment3 ++ refs73Segment4) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1,1] classSegment3 classSegment4 refs73Segment3 refs73Segment4 (by decide)]
  decide

theorem residue73_checked : (2 * indexedCoverSum table 12 classes refs33 refs73) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs73Segment0 ++ (refs73Segment1 ++ (refs73Segment2 ++ (refs73Segment3 ++ refs73Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs73Segment0 (refs73Segment1 ++ (refs73Segment2 ++ (refs73Segment3 ++ refs73Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs73Segment1 (refs73Segment2 ++ (refs73Segment3 ++ refs73Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs73Segment2 (refs73Segment3 ++ refs73Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs73Segment3 refs73Segment4 (by decide) (by decide)]
  decide

theorem row74_checked : checkIndexedRow table [2,2,1,1,1,1,1,1,1,1] classes refs74 = true := by
  change checkIndexedRow table [2,2,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs74Segment0 ++ (refs74Segment1 ++ (refs74Segment2 ++ (refs74Segment3 ++ refs74Segment4)))) = true
  rw [checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs74Segment0 (refs74Segment1 ++ (refs74Segment2 ++ (refs74Segment3 ++ refs74Segment4))) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs74Segment1 (refs74Segment2 ++ (refs74Segment3 ++ refs74Segment4)) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs74Segment2 (refs74Segment3 ++ refs74Segment4) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1,1] classSegment3 classSegment4 refs74Segment3 refs74Segment4 (by decide)]
  decide

theorem residue74_checked : (2 * indexedCoverSum table 12 classes refs33 refs74) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs74Segment0 ++ (refs74Segment1 ++ (refs74Segment2 ++ (refs74Segment3 ++ refs74Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs74Segment0 (refs74Segment1 ++ (refs74Segment2 ++ (refs74Segment3 ++ refs74Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs74Segment1 (refs74Segment2 ++ (refs74Segment3 ++ refs74Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs74Segment2 (refs74Segment3 ++ refs74Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs74Segment3 refs74Segment4 (by decide) (by decide)]
  decide

theorem row75_checked : checkIndexedRow table [2,1,1,1,1,1,1,1,1,1,1] classes refs75 = true := by
  change checkIndexedRow table [2,1,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs75Segment0 ++ (refs75Segment1 ++ (refs75Segment2 ++ (refs75Segment3 ++ refs75Segment4)))) = true
  rw [checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs75Segment0 (refs75Segment1 ++ (refs75Segment2 ++ (refs75Segment3 ++ refs75Segment4))) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs75Segment1 (refs75Segment2 ++ (refs75Segment3 ++ refs75Segment4)) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs75Segment2 (refs75Segment3 ++ refs75Segment4) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1,1] classSegment3 classSegment4 refs75Segment3 refs75Segment4 (by decide)]
  decide

theorem residue75_checked : (2 * indexedCoverSum table 12 classes refs33 refs75) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs75Segment0 ++ (refs75Segment1 ++ (refs75Segment2 ++ (refs75Segment3 ++ refs75Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs75Segment0 (refs75Segment1 ++ (refs75Segment2 ++ (refs75Segment3 ++ refs75Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs75Segment1 (refs75Segment2 ++ (refs75Segment3 ++ refs75Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs75Segment2 (refs75Segment3 ++ refs75Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs75Segment3 refs75Segment4 (by decide) (by decide)]
  decide

theorem row76_checked : checkIndexedRow table [1,1,1,1,1,1,1,1,1,1,1,1] classes refs76 = true := by
  change checkIndexedRow table [1,1,1,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs76Segment0 ++ (refs76Segment1 ++ (refs76Segment2 ++ (refs76Segment3 ++ refs76Segment4)))) = true
  rw [checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs76Segment0 (refs76Segment1 ++ (refs76Segment2 ++ (refs76Segment3 ++ refs76Segment4))) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs76Segment1 (refs76Segment2 ++ (refs76Segment3 ++ refs76Segment4)) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs76Segment2 (refs76Segment3 ++ refs76Segment4) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1,1] classSegment3 classSegment4 refs76Segment3 refs76Segment4 (by decide)]
  decide

theorem residue76_checked : (2 * indexedCoverSum table 12 classes refs33 refs76) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs76Segment0 ++ (refs76Segment1 ++ (refs76Segment2 ++ (refs76Segment3 ++ refs76Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs76Segment0 (refs76Segment1 ++ (refs76Segment2 ++ (refs76Segment3 ++ refs76Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs76Segment1 (refs76Segment2 ++ (refs76Segment3 ++ refs76Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs76Segment2 (refs76Segment3 ++ refs76Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs76Segment3 refs76Segment4 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D12
