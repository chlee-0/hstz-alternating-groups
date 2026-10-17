import HSTZ.TauCetiFinite.Degrees.D11.Segments

/-! Part of the degree-11 finite character certificate (`HSTZ.TauCetiFinite.D11`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D11
open HSTZ.MurnaghanNakayama

theorem row40_checked : checkIndexedRow table [3,3,3,2] classes refs40 = true := by
  change checkIndexedRow table [3,3,3,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs40Segment0 ++ (refs40Segment1 ++ (refs40Segment2 ++ refs40Segment3))) = true
  rw [checkIndexedRow_append table [3,3,3,2] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs40Segment0 (refs40Segment1 ++ (refs40Segment2 ++ refs40Segment3)) (by decide),
    checkIndexedRow_append table [3,3,3,2] classSegment1 (classSegment2 ++ classSegment3) refs40Segment1 (refs40Segment2 ++ refs40Segment3) (by decide),
    checkIndexedRow_append table [3,3,3,2] classSegment2 classSegment3 refs40Segment2 refs40Segment3 (by decide)]
  decide

theorem residue40_checked : (2 * indexedCoverSum table 11 classes refs23 refs40) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs40Segment0 ++ (refs40Segment1 ++ (refs40Segment2 ++ refs40Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs40Segment0 (refs40Segment1 ++ (refs40Segment2 ++ refs40Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs40Segment1 (refs40Segment2 ++ refs40Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs40Segment2 refs40Segment3 (by decide) (by decide)]
  decide

theorem row41_checked : checkIndexedRow table [3,3,3,1,1] classes refs41 = true := by
  change checkIndexedRow table [3,3,3,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs41Segment0 ++ (refs41Segment1 ++ (refs41Segment2 ++ refs41Segment3))) = true
  rw [checkIndexedRow_append table [3,3,3,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs41Segment0 (refs41Segment1 ++ (refs41Segment2 ++ refs41Segment3)) (by decide),
    checkIndexedRow_append table [3,3,3,1,1] classSegment1 (classSegment2 ++ classSegment3) refs41Segment1 (refs41Segment2 ++ refs41Segment3) (by decide),
    checkIndexedRow_append table [3,3,3,1,1] classSegment2 classSegment3 refs41Segment2 refs41Segment3 (by decide)]
  decide

theorem residue41_checked : (2 * indexedCoverSum table 11 classes refs23 refs41) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs41Segment0 ++ (refs41Segment1 ++ (refs41Segment2 ++ refs41Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs41Segment0 (refs41Segment1 ++ (refs41Segment2 ++ refs41Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs41Segment1 (refs41Segment2 ++ refs41Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs41Segment2 refs41Segment3 (by decide) (by decide)]
  decide

theorem row42_checked : checkIndexedRow table [3,3,2,2,1] classes refs42 = true := by
  change checkIndexedRow table [3,3,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs42Segment0 ++ (refs42Segment1 ++ (refs42Segment2 ++ refs42Segment3))) = true
  rw [checkIndexedRow_append table [3,3,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs42Segment0 (refs42Segment1 ++ (refs42Segment2 ++ refs42Segment3)) (by decide),
    checkIndexedRow_append table [3,3,2,2,1] classSegment1 (classSegment2 ++ classSegment3) refs42Segment1 (refs42Segment2 ++ refs42Segment3) (by decide),
    checkIndexedRow_append table [3,3,2,2,1] classSegment2 classSegment3 refs42Segment2 refs42Segment3 (by decide)]
  decide

theorem residue42_checked : (2 * indexedCoverSum table 11 classes refs23 refs42) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs42Segment0 ++ (refs42Segment1 ++ (refs42Segment2 ++ refs42Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs42Segment0 (refs42Segment1 ++ (refs42Segment2 ++ refs42Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs42Segment1 (refs42Segment2 ++ refs42Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs42Segment2 refs42Segment3 (by decide) (by decide)]
  decide

theorem row43_checked : checkIndexedRow table [3,3,2,1,1,1] classes refs43 = true := by
  change checkIndexedRow table [3,3,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs43Segment0 ++ (refs43Segment1 ++ (refs43Segment2 ++ refs43Segment3))) = true
  rw [checkIndexedRow_append table [3,3,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs43Segment0 (refs43Segment1 ++ (refs43Segment2 ++ refs43Segment3)) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs43Segment1 (refs43Segment2 ++ refs43Segment3) (by decide),
    checkIndexedRow_append table [3,3,2,1,1,1] classSegment2 classSegment3 refs43Segment2 refs43Segment3 (by decide)]
  decide

theorem residue43_checked : (2 * indexedCoverSum table 11 classes refs23 refs43) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs43Segment0 ++ (refs43Segment1 ++ (refs43Segment2 ++ refs43Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs43Segment0 (refs43Segment1 ++ (refs43Segment2 ++ refs43Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs43Segment1 (refs43Segment2 ++ refs43Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs43Segment2 refs43Segment3 (by decide) (by decide)]
  decide

theorem row44_checked : checkIndexedRow table [3,3,1,1,1,1,1] classes refs44 = true := by
  change checkIndexedRow table [3,3,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs44Segment0 ++ (refs44Segment1 ++ (refs44Segment2 ++ refs44Segment3))) = true
  rw [checkIndexedRow_append table [3,3,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs44Segment0 (refs44Segment1 ++ (refs44Segment2 ++ refs44Segment3)) (by decide),
    checkIndexedRow_append table [3,3,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs44Segment1 (refs44Segment2 ++ refs44Segment3) (by decide),
    checkIndexedRow_append table [3,3,1,1,1,1,1] classSegment2 classSegment3 refs44Segment2 refs44Segment3 (by decide)]
  decide

theorem residue44_checked : (2 * indexedCoverSum table 11 classes refs23 refs44) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs44Segment0 ++ (refs44Segment1 ++ (refs44Segment2 ++ refs44Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs44Segment0 (refs44Segment1 ++ (refs44Segment2 ++ refs44Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs44Segment1 (refs44Segment2 ++ refs44Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs44Segment2 refs44Segment3 (by decide) (by decide)]
  decide

theorem row45_checked : checkIndexedRow table [3,2,2,2,2] classes refs45 = true := by
  change checkIndexedRow table [3,2,2,2,2] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs45Segment0 ++ (refs45Segment1 ++ (refs45Segment2 ++ refs45Segment3))) = true
  rw [checkIndexedRow_append table [3,2,2,2,2] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs45Segment0 (refs45Segment1 ++ (refs45Segment2 ++ refs45Segment3)) (by decide),
    checkIndexedRow_append table [3,2,2,2,2] classSegment1 (classSegment2 ++ classSegment3) refs45Segment1 (refs45Segment2 ++ refs45Segment3) (by decide),
    checkIndexedRow_append table [3,2,2,2,2] classSegment2 classSegment3 refs45Segment2 refs45Segment3 (by decide)]
  decide

theorem residue45_checked : (2 * indexedCoverSum table 11 classes refs23 refs45) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs45Segment0 ++ (refs45Segment1 ++ (refs45Segment2 ++ refs45Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs45Segment0 (refs45Segment1 ++ (refs45Segment2 ++ refs45Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs45Segment1 (refs45Segment2 ++ refs45Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs45Segment2 refs45Segment3 (by decide) (by decide)]
  decide

theorem row46_checked : checkIndexedRow table [3,2,2,2,1,1] classes refs46 = true := by
  change checkIndexedRow table [3,2,2,2,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs46Segment0 ++ (refs46Segment1 ++ (refs46Segment2 ++ refs46Segment3))) = true
  rw [checkIndexedRow_append table [3,2,2,2,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs46Segment0 (refs46Segment1 ++ (refs46Segment2 ++ refs46Segment3)) (by decide),
    checkIndexedRow_append table [3,2,2,2,1,1] classSegment1 (classSegment2 ++ classSegment3) refs46Segment1 (refs46Segment2 ++ refs46Segment3) (by decide),
    checkIndexedRow_append table [3,2,2,2,1,1] classSegment2 classSegment3 refs46Segment2 refs46Segment3 (by decide)]
  decide

theorem residue46_checked : (2 * indexedCoverSum table 11 classes refs23 refs46) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs46Segment0 ++ (refs46Segment1 ++ (refs46Segment2 ++ refs46Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs46Segment0 (refs46Segment1 ++ (refs46Segment2 ++ refs46Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs46Segment1 (refs46Segment2 ++ refs46Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs46Segment2 refs46Segment3 (by decide) (by decide)]
  decide

theorem row47_checked : checkIndexedRow table [3,2,2,1,1,1,1] classes refs47 = true := by
  change checkIndexedRow table [3,2,2,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs47Segment0 ++ (refs47Segment1 ++ (refs47Segment2 ++ refs47Segment3))) = true
  rw [checkIndexedRow_append table [3,2,2,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs47Segment0 (refs47Segment1 ++ (refs47Segment2 ++ refs47Segment3)) (by decide),
    checkIndexedRow_append table [3,2,2,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs47Segment1 (refs47Segment2 ++ refs47Segment3) (by decide),
    checkIndexedRow_append table [3,2,2,1,1,1,1] classSegment2 classSegment3 refs47Segment2 refs47Segment3 (by decide)]
  decide

theorem residue47_checked : (2 * indexedCoverSum table 11 classes refs23 refs47) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs47Segment0 ++ (refs47Segment1 ++ (refs47Segment2 ++ refs47Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs47Segment0 (refs47Segment1 ++ (refs47Segment2 ++ refs47Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs47Segment1 (refs47Segment2 ++ refs47Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs47Segment2 refs47Segment3 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D11
