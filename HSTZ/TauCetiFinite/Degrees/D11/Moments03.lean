import HSTZ.TauCetiFinite.Degrees.D11.Segments

/-! Part of the degree-11 finite character certificate (`HSTZ.TauCetiFinite.D11`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D11
open HSTZ.MurnaghanNakayama

theorem row24_checked : checkIndexedRow table [5,3,1,1,1] classes refs24 = true := by
  change checkIndexedRow table [5,3,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs24Segment0 ++ (refs24Segment1 ++ (refs24Segment2 ++ refs24Segment3))) = true
  rw [checkIndexedRow_append table [5,3,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs24Segment0 (refs24Segment1 ++ (refs24Segment2 ++ refs24Segment3)) (by decide),
    checkIndexedRow_append table [5,3,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs24Segment1 (refs24Segment2 ++ refs24Segment3) (by decide),
    checkIndexedRow_append table [5,3,1,1,1] classSegment2 classSegment3 refs24Segment2 refs24Segment3 (by decide)]
  decide

theorem residue24_checked : (2 * indexedCoverSum table 11 classes refs23 refs24) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs24Segment0 ++ (refs24Segment1 ++ (refs24Segment2 ++ refs24Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs24Segment0 (refs24Segment1 ++ (refs24Segment2 ++ refs24Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs24Segment1 (refs24Segment2 ++ refs24Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs24Segment2 refs24Segment3 (by decide) (by decide)]
  decide

theorem row25_checked : checkIndexedRow table [5,2,2,2] classes refs25 = true := by
  change checkIndexedRow table [5,2,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs25Segment0 ++ (refs25Segment1 ++ (refs25Segment2 ++ refs25Segment3))) = true
  rw [checkIndexedRow_append table [5,2,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs25Segment0 (refs25Segment1 ++ (refs25Segment2 ++ refs25Segment3)) (by decide),
    checkIndexedRow_append table [5,2,2,2] classSegment1 (classSegment2 ++ classSegment3) refs25Segment1 (refs25Segment2 ++ refs25Segment3) (by decide),
    checkIndexedRow_append table [5,2,2,2] classSegment2 classSegment3 refs25Segment2 refs25Segment3 (by decide)]
  decide

theorem residue25_checked : (2 * indexedCoverSum table 11 classes refs23 refs25) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs25Segment0 ++ (refs25Segment1 ++ (refs25Segment2 ++ refs25Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs25Segment0 (refs25Segment1 ++ (refs25Segment2 ++ refs25Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs25Segment1 (refs25Segment2 ++ refs25Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs25Segment2 refs25Segment3 (by decide) (by decide)]
  decide

theorem row26_checked : checkIndexedRow table [5,2,2,1,1] classes refs26 = true := by
  change checkIndexedRow table [5,2,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs26Segment0 ++ (refs26Segment1 ++ (refs26Segment2 ++ refs26Segment3))) = true
  rw [checkIndexedRow_append table [5,2,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs26Segment0 (refs26Segment1 ++ (refs26Segment2 ++ refs26Segment3)) (by decide),
    checkIndexedRow_append table [5,2,2,1,1] classSegment1 (classSegment2 ++ classSegment3) refs26Segment1 (refs26Segment2 ++ refs26Segment3) (by decide),
    checkIndexedRow_append table [5,2,2,1,1] classSegment2 classSegment3 refs26Segment2 refs26Segment3 (by decide)]
  decide

theorem residue26_checked : (2 * indexedCoverSum table 11 classes refs23 refs26) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs26Segment0 ++ (refs26Segment1 ++ (refs26Segment2 ++ refs26Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs26Segment0 (refs26Segment1 ++ (refs26Segment2 ++ refs26Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs26Segment1 (refs26Segment2 ++ refs26Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs26Segment2 refs26Segment3 (by decide) (by decide)]
  decide

theorem row27_checked : checkIndexedRow table [5,2,1,1,1,1] classes refs27 = true := by
  change checkIndexedRow table [5,2,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs27Segment0 ++ (refs27Segment1 ++ (refs27Segment2 ++ refs27Segment3))) = true
  rw [checkIndexedRow_append table [5,2,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs27Segment0 (refs27Segment1 ++ (refs27Segment2 ++ refs27Segment3)) (by decide),
    checkIndexedRow_append table [5,2,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs27Segment1 (refs27Segment2 ++ refs27Segment3) (by decide),
    checkIndexedRow_append table [5,2,1,1,1,1] classSegment2 classSegment3 refs27Segment2 refs27Segment3 (by decide)]
  decide

theorem residue27_checked : (2 * indexedCoverSum table 11 classes refs23 refs27) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs27Segment0 ++ (refs27Segment1 ++ (refs27Segment2 ++ refs27Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs27Segment0 (refs27Segment1 ++ (refs27Segment2 ++ refs27Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs27Segment1 (refs27Segment2 ++ refs27Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs27Segment2 refs27Segment3 (by decide) (by decide)]
  decide

theorem row28_checked : checkIndexedRow table [5,1,1,1,1,1,1] classes refs28 = true := by
  change checkIndexedRow table [5,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs28Segment0 ++ (refs28Segment1 ++ (refs28Segment2 ++ refs28Segment3))) = true
  rw [checkIndexedRow_append table [5,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs28Segment0 (refs28Segment1 ++ (refs28Segment2 ++ refs28Segment3)) (by decide),
    checkIndexedRow_append table [5,1,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs28Segment1 (refs28Segment2 ++ refs28Segment3) (by decide),
    checkIndexedRow_append table [5,1,1,1,1,1,1] classSegment2 classSegment3 refs28Segment2 refs28Segment3 (by decide)]
  decide

theorem residue28_checked : (2 * indexedCoverSum table 11 classes refs23 refs28) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs28Segment0 ++ (refs28Segment1 ++ (refs28Segment2 ++ refs28Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs28Segment0 (refs28Segment1 ++ (refs28Segment2 ++ refs28Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs28Segment1 (refs28Segment2 ++ refs28Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs28Segment2 refs28Segment3 (by decide) (by decide)]
  decide

theorem row29_checked : checkIndexedRow table [4,4,3] classes refs29 = true := by
  change checkIndexedRow table [4,4,3] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs29Segment0 ++ (refs29Segment1 ++ (refs29Segment2 ++ refs29Segment3))) = true
  rw [checkIndexedRow_append table [4,4,3] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs29Segment0 (refs29Segment1 ++ (refs29Segment2 ++ refs29Segment3)) (by decide),
    checkIndexedRow_append table [4,4,3] classSegment1 (classSegment2 ++ classSegment3) refs29Segment1 (refs29Segment2 ++ refs29Segment3) (by decide),
    checkIndexedRow_append table [4,4,3] classSegment2 classSegment3 refs29Segment2 refs29Segment3 (by decide)]
  decide

theorem residue29_checked : (2 * indexedCoverSum table 11 classes refs23 refs29) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs29Segment0 ++ (refs29Segment1 ++ (refs29Segment2 ++ refs29Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs29Segment0 (refs29Segment1 ++ (refs29Segment2 ++ refs29Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs29Segment1 (refs29Segment2 ++ refs29Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs29Segment2 refs29Segment3 (by decide) (by decide)]
  decide

theorem row30_checked : checkIndexedRow table [4,4,2,1] classes refs30 = true := by
  change checkIndexedRow table [4,4,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs30Segment0 ++ (refs30Segment1 ++ (refs30Segment2 ++ refs30Segment3))) = true
  rw [checkIndexedRow_append table [4,4,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs30Segment0 (refs30Segment1 ++ (refs30Segment2 ++ refs30Segment3)) (by decide),
    checkIndexedRow_append table [4,4,2,1] classSegment1 (classSegment2 ++ classSegment3) refs30Segment1 (refs30Segment2 ++ refs30Segment3) (by decide),
    checkIndexedRow_append table [4,4,2,1] classSegment2 classSegment3 refs30Segment2 refs30Segment3 (by decide)]
  decide

theorem residue30_checked : (2 * indexedCoverSum table 11 classes refs23 refs30) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs30Segment0 ++ (refs30Segment1 ++ (refs30Segment2 ++ refs30Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs30Segment0 (refs30Segment1 ++ (refs30Segment2 ++ refs30Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs30Segment1 (refs30Segment2 ++ refs30Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs30Segment2 refs30Segment3 (by decide) (by decide)]
  decide

theorem row31_checked : checkIndexedRow table [4,4,1,1,1] classes refs31 = true := by
  change checkIndexedRow table [4,4,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs31Segment0 ++ (refs31Segment1 ++ (refs31Segment2 ++ refs31Segment3))) = true
  rw [checkIndexedRow_append table [4,4,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs31Segment0 (refs31Segment1 ++ (refs31Segment2 ++ refs31Segment3)) (by decide),
    checkIndexedRow_append table [4,4,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs31Segment1 (refs31Segment2 ++ refs31Segment3) (by decide),
    checkIndexedRow_append table [4,4,1,1,1] classSegment2 classSegment3 refs31Segment2 refs31Segment3 (by decide)]
  decide

theorem residue31_checked : (2 * indexedCoverSum table 11 classes refs23 refs31) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs31Segment0 ++ (refs31Segment1 ++ (refs31Segment2 ++ refs31Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs31Segment0 (refs31Segment1 ++ (refs31Segment2 ++ refs31Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs31Segment1 (refs31Segment2 ++ refs31Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs31Segment2 refs31Segment3 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D11
