import HSTZ.TauCetiFinite.Degrees.D12.Segments

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem row40_checked : checkIndexedRow table [5,2,2,1,1,1] classes refs40 = true := by
  change checkIndexedRow table [5,2,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs40Segment0 ++ (refs40Segment1 ++ (refs40Segment2 ++ (refs40Segment3 ++ refs40Segment4)))) = true
  rw [checkIndexedRow_append table [5,2,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs40Segment0 (refs40Segment1 ++ (refs40Segment2 ++ (refs40Segment3 ++ refs40Segment4))) (by decide),
    checkIndexedRow_append table [5,2,2,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs40Segment1 (refs40Segment2 ++ (refs40Segment3 ++ refs40Segment4)) (by decide),
    checkIndexedRow_append table [5,2,2,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs40Segment2 (refs40Segment3 ++ refs40Segment4) (by decide),
    checkIndexedRow_append table [5,2,2,1,1,1] classSegment3 classSegment4 refs40Segment3 refs40Segment4 (by decide)]
  decide

theorem residue40_checked : (2 * indexedCoverSum table 12 classes refs33 refs40) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs40Segment0 ++ (refs40Segment1 ++ (refs40Segment2 ++ (refs40Segment3 ++ refs40Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs40Segment0 (refs40Segment1 ++ (refs40Segment2 ++ (refs40Segment3 ++ refs40Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs40Segment1 (refs40Segment2 ++ (refs40Segment3 ++ refs40Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs40Segment2 (refs40Segment3 ++ refs40Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs40Segment3 refs40Segment4 (by decide) (by decide)]
  decide

theorem row41_checked : checkIndexedRow table [5,2,1,1,1,1,1] classes refs41 = true := by
  change checkIndexedRow table [5,2,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs41Segment0 ++ (refs41Segment1 ++ (refs41Segment2 ++ (refs41Segment3 ++ refs41Segment4)))) = true
  rw [checkIndexedRow_append table [5,2,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs41Segment0 (refs41Segment1 ++ (refs41Segment2 ++ (refs41Segment3 ++ refs41Segment4))) (by decide),
    checkIndexedRow_append table [5,2,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs41Segment1 (refs41Segment2 ++ (refs41Segment3 ++ refs41Segment4)) (by decide),
    checkIndexedRow_append table [5,2,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs41Segment2 (refs41Segment3 ++ refs41Segment4) (by decide),
    checkIndexedRow_append table [5,2,1,1,1,1,1] classSegment3 classSegment4 refs41Segment3 refs41Segment4 (by decide)]
  decide

theorem residue41_checked : (2 * indexedCoverSum table 12 classes refs33 refs41) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs41Segment0 ++ (refs41Segment1 ++ (refs41Segment2 ++ (refs41Segment3 ++ refs41Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs41Segment0 (refs41Segment1 ++ (refs41Segment2 ++ (refs41Segment3 ++ refs41Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs41Segment1 (refs41Segment2 ++ (refs41Segment3 ++ refs41Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs41Segment2 (refs41Segment3 ++ refs41Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs41Segment3 refs41Segment4 (by decide) (by decide)]
  decide

theorem row42_checked : checkIndexedRow table [5,1,1,1,1,1,1,1] classes refs42 = true := by
  change checkIndexedRow table [5,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs42Segment0 ++ (refs42Segment1 ++ (refs42Segment2 ++ (refs42Segment3 ++ refs42Segment4)))) = true
  rw [checkIndexedRow_append table [5,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs42Segment0 (refs42Segment1 ++ (refs42Segment2 ++ (refs42Segment3 ++ refs42Segment4))) (by decide),
    checkIndexedRow_append table [5,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs42Segment1 (refs42Segment2 ++ (refs42Segment3 ++ refs42Segment4)) (by decide),
    checkIndexedRow_append table [5,1,1,1,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs42Segment2 (refs42Segment3 ++ refs42Segment4) (by decide),
    checkIndexedRow_append table [5,1,1,1,1,1,1,1] classSegment3 classSegment4 refs42Segment3 refs42Segment4 (by decide)]
  decide

theorem residue42_checked : (2 * indexedCoverSum table 12 classes refs33 refs42) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs42Segment0 ++ (refs42Segment1 ++ (refs42Segment2 ++ (refs42Segment3 ++ refs42Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs42Segment0 (refs42Segment1 ++ (refs42Segment2 ++ (refs42Segment3 ++ refs42Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs42Segment1 (refs42Segment2 ++ (refs42Segment3 ++ refs42Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs42Segment2 (refs42Segment3 ++ refs42Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs42Segment3 refs42Segment4 (by decide) (by decide)]
  decide

theorem row43_checked : checkIndexedRow table [4,4,4] classes refs43 = true := by
  change checkIndexedRow table [4,4,4] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs43Segment0 ++ (refs43Segment1 ++ (refs43Segment2 ++ (refs43Segment3 ++ refs43Segment4)))) = true
  rw [checkIndexedRow_append table [4,4,4] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs43Segment0 (refs43Segment1 ++ (refs43Segment2 ++ (refs43Segment3 ++ refs43Segment4))) (by decide),
    checkIndexedRow_append table [4,4,4] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs43Segment1 (refs43Segment2 ++ (refs43Segment3 ++ refs43Segment4)) (by decide),
    checkIndexedRow_append table [4,4,4] classSegment2 (classSegment3 ++ classSegment4) refs43Segment2 (refs43Segment3 ++ refs43Segment4) (by decide),
    checkIndexedRow_append table [4,4,4] classSegment3 classSegment4 refs43Segment3 refs43Segment4 (by decide)]
  decide

theorem residue43_checked : (2 * indexedCoverSum table 12 classes refs33 refs43) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs43Segment0 ++ (refs43Segment1 ++ (refs43Segment2 ++ (refs43Segment3 ++ refs43Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs43Segment0 (refs43Segment1 ++ (refs43Segment2 ++ (refs43Segment3 ++ refs43Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs43Segment1 (refs43Segment2 ++ (refs43Segment3 ++ refs43Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs43Segment2 (refs43Segment3 ++ refs43Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs43Segment3 refs43Segment4 (by decide) (by decide)]
  decide

theorem row44_checked : checkIndexedRow table [4,4,3,1] classes refs44 = true := by
  change checkIndexedRow table [4,4,3,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs44Segment0 ++ (refs44Segment1 ++ (refs44Segment2 ++ (refs44Segment3 ++ refs44Segment4)))) = true
  rw [checkIndexedRow_append table [4,4,3,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs44Segment0 (refs44Segment1 ++ (refs44Segment2 ++ (refs44Segment3 ++ refs44Segment4))) (by decide),
    checkIndexedRow_append table [4,4,3,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs44Segment1 (refs44Segment2 ++ (refs44Segment3 ++ refs44Segment4)) (by decide),
    checkIndexedRow_append table [4,4,3,1] classSegment2 (classSegment3 ++ classSegment4) refs44Segment2 (refs44Segment3 ++ refs44Segment4) (by decide),
    checkIndexedRow_append table [4,4,3,1] classSegment3 classSegment4 refs44Segment3 refs44Segment4 (by decide)]
  decide

theorem residue44_checked : (2 * indexedCoverSum table 12 classes refs33 refs44) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs44Segment0 ++ (refs44Segment1 ++ (refs44Segment2 ++ (refs44Segment3 ++ refs44Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs44Segment0 (refs44Segment1 ++ (refs44Segment2 ++ (refs44Segment3 ++ refs44Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs44Segment1 (refs44Segment2 ++ (refs44Segment3 ++ refs44Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs44Segment2 (refs44Segment3 ++ refs44Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs44Segment3 refs44Segment4 (by decide) (by decide)]
  decide

theorem row45_checked : checkIndexedRow table [4,4,2,2] classes refs45 = true := by
  change checkIndexedRow table [4,4,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs45Segment0 ++ (refs45Segment1 ++ (refs45Segment2 ++ (refs45Segment3 ++ refs45Segment4)))) = true
  rw [checkIndexedRow_append table [4,4,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs45Segment0 (refs45Segment1 ++ (refs45Segment2 ++ (refs45Segment3 ++ refs45Segment4))) (by decide),
    checkIndexedRow_append table [4,4,2,2] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs45Segment1 (refs45Segment2 ++ (refs45Segment3 ++ refs45Segment4)) (by decide),
    checkIndexedRow_append table [4,4,2,2] classSegment2 (classSegment3 ++ classSegment4) refs45Segment2 (refs45Segment3 ++ refs45Segment4) (by decide),
    checkIndexedRow_append table [4,4,2,2] classSegment3 classSegment4 refs45Segment3 refs45Segment4 (by decide)]
  decide

theorem residue45_checked : (2 * indexedCoverSum table 12 classes refs33 refs45) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs45Segment0 ++ (refs45Segment1 ++ (refs45Segment2 ++ (refs45Segment3 ++ refs45Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs45Segment0 (refs45Segment1 ++ (refs45Segment2 ++ (refs45Segment3 ++ refs45Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs45Segment1 (refs45Segment2 ++ (refs45Segment3 ++ refs45Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs45Segment2 (refs45Segment3 ++ refs45Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs45Segment3 refs45Segment4 (by decide) (by decide)]
  decide

theorem row46_checked : checkIndexedRow table [4,4,2,1,1] classes refs46 = true := by
  change checkIndexedRow table [4,4,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs46Segment0 ++ (refs46Segment1 ++ (refs46Segment2 ++ (refs46Segment3 ++ refs46Segment4)))) = true
  rw [checkIndexedRow_append table [4,4,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs46Segment0 (refs46Segment1 ++ (refs46Segment2 ++ (refs46Segment3 ++ refs46Segment4))) (by decide),
    checkIndexedRow_append table [4,4,2,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs46Segment1 (refs46Segment2 ++ (refs46Segment3 ++ refs46Segment4)) (by decide),
    checkIndexedRow_append table [4,4,2,1,1] classSegment2 (classSegment3 ++ classSegment4) refs46Segment2 (refs46Segment3 ++ refs46Segment4) (by decide),
    checkIndexedRow_append table [4,4,2,1,1] classSegment3 classSegment4 refs46Segment3 refs46Segment4 (by decide)]
  decide

theorem residue46_checked : (2 * indexedCoverSum table 12 classes refs33 refs46) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs46Segment0 ++ (refs46Segment1 ++ (refs46Segment2 ++ (refs46Segment3 ++ refs46Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs46Segment0 (refs46Segment1 ++ (refs46Segment2 ++ (refs46Segment3 ++ refs46Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs46Segment1 (refs46Segment2 ++ (refs46Segment3 ++ refs46Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs46Segment2 (refs46Segment3 ++ refs46Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs46Segment3 refs46Segment4 (by decide) (by decide)]
  decide

theorem row47_checked : checkIndexedRow table [4,4,1,1,1,1] classes refs47 = true := by
  change checkIndexedRow table [4,4,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs47Segment0 ++ (refs47Segment1 ++ (refs47Segment2 ++ (refs47Segment3 ++ refs47Segment4)))) = true
  rw [checkIndexedRow_append table [4,4,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs47Segment0 (refs47Segment1 ++ (refs47Segment2 ++ (refs47Segment3 ++ refs47Segment4))) (by decide),
    checkIndexedRow_append table [4,4,1,1,1,1] classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs47Segment1 (refs47Segment2 ++ (refs47Segment3 ++ refs47Segment4)) (by decide),
    checkIndexedRow_append table [4,4,1,1,1,1] classSegment2 (classSegment3 ++ classSegment4) refs47Segment2 (refs47Segment3 ++ refs47Segment4) (by decide),
    checkIndexedRow_append table [4,4,1,1,1,1] classSegment3 classSegment4 refs47Segment3 refs47Segment4 (by decide)]
  decide

theorem residue47_checked : (2 * indexedCoverSum table 12 classes refs33 refs47) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 12 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4)))) (refs33Segment0 ++ (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)))) (refs47Segment0 ++ (refs47Segment1 ++ (refs47Segment2 ++ (refs47Segment3 ++ refs47Segment4))))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 12 classSegment0 (classSegment1 ++ (classSegment2 ++ (classSegment3 ++ classSegment4))) refs33Segment0 (refs33Segment1 ++ (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4))) refs47Segment0 (refs47Segment1 ++ (refs47Segment2 ++ (refs47Segment3 ++ refs47Segment4))) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment1 (classSegment2 ++ (classSegment3 ++ classSegment4)) refs33Segment1 (refs33Segment2 ++ (refs33Segment3 ++ refs33Segment4)) refs47Segment1 (refs47Segment2 ++ (refs47Segment3 ++ refs47Segment4)) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment2 (classSegment3 ++ classSegment4) refs33Segment2 (refs33Segment3 ++ refs33Segment4) refs47Segment2 (refs47Segment3 ++ refs47Segment4) (by decide) (by decide),
    indexedCoverSum_append table 12 classSegment3 classSegment4 refs33Segment3 refs33Segment4 refs47Segment3 refs47Segment4 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D12
