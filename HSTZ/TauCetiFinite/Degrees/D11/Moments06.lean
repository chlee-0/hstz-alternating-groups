import HSTZ.TauCetiFinite.Degrees.D11.Segments

/-! Part of the degree-11 finite character certificate (`HSTZ.TauCetiFinite.D11`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D11
open HSTZ.MurnaghanNakayama

theorem row48_checked : checkIndexedRow table [3,2,1,1,1,1,1,1] classes refs48 = true := by
  change checkIndexedRow table [3,2,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs48Segment0 ++ (refs48Segment1 ++ (refs48Segment2 ++ refs48Segment3))) = true
  rw [checkIndexedRow_append table [3,2,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs48Segment0 (refs48Segment1 ++ (refs48Segment2 ++ refs48Segment3)) (by decide),
    checkIndexedRow_append table [3,2,1,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs48Segment1 (refs48Segment2 ++ refs48Segment3) (by decide),
    checkIndexedRow_append table [3,2,1,1,1,1,1,1] classSegment2 classSegment3 refs48Segment2 refs48Segment3 (by decide)]
  decide

theorem residue48_checked : (2 * indexedCoverSum table 11 classes refs23 refs48) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs48Segment0 ++ (refs48Segment1 ++ (refs48Segment2 ++ refs48Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs48Segment0 (refs48Segment1 ++ (refs48Segment2 ++ refs48Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs48Segment1 (refs48Segment2 ++ refs48Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs48Segment2 refs48Segment3 (by decide) (by decide)]
  decide

theorem row49_checked : checkIndexedRow table [3,1,1,1,1,1,1,1,1] classes refs49 = true := by
  change checkIndexedRow table [3,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs49Segment0 ++ (refs49Segment1 ++ (refs49Segment2 ++ refs49Segment3))) = true
  rw [checkIndexedRow_append table [3,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs49Segment0 (refs49Segment1 ++ (refs49Segment2 ++ refs49Segment3)) (by decide),
    checkIndexedRow_append table [3,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs49Segment1 (refs49Segment2 ++ refs49Segment3) (by decide),
    checkIndexedRow_append table [3,1,1,1,1,1,1,1,1] classSegment2 classSegment3 refs49Segment2 refs49Segment3 (by decide)]
  decide

theorem residue49_checked : (2 * indexedCoverSum table 11 classes refs23 refs49) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs49Segment0 ++ (refs49Segment1 ++ (refs49Segment2 ++ refs49Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs49Segment0 (refs49Segment1 ++ (refs49Segment2 ++ refs49Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs49Segment1 (refs49Segment2 ++ refs49Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs49Segment2 refs49Segment3 (by decide) (by decide)]
  decide

theorem row50_checked : checkIndexedRow table [2,2,2,2,2,1] classes refs50 = true := by
  change checkIndexedRow table [2,2,2,2,2,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs50Segment0 ++ (refs50Segment1 ++ (refs50Segment2 ++ refs50Segment3))) = true
  rw [checkIndexedRow_append table [2,2,2,2,2,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs50Segment0 (refs50Segment1 ++ (refs50Segment2 ++ refs50Segment3)) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,1] classSegment1 (classSegment2 ++ classSegment3) refs50Segment1 (refs50Segment2 ++ refs50Segment3) (by decide),
    checkIndexedRow_append table [2,2,2,2,2,1] classSegment2 classSegment3 refs50Segment2 refs50Segment3 (by decide)]
  decide

theorem residue50_checked : (2 * indexedCoverSum table 11 classes refs23 refs50) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs50Segment0 ++ (refs50Segment1 ++ (refs50Segment2 ++ refs50Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs50Segment0 (refs50Segment1 ++ (refs50Segment2 ++ refs50Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs50Segment1 (refs50Segment2 ++ refs50Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs50Segment2 refs50Segment3 (by decide) (by decide)]
  decide

theorem row51_checked : checkIndexedRow table [2,2,2,2,1,1,1] classes refs51 = true := by
  change checkIndexedRow table [2,2,2,2,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs51Segment0 ++ (refs51Segment1 ++ (refs51Segment2 ++ refs51Segment3))) = true
  rw [checkIndexedRow_append table [2,2,2,2,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs51Segment0 (refs51Segment1 ++ (refs51Segment2 ++ refs51Segment3)) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs51Segment1 (refs51Segment2 ++ refs51Segment3) (by decide),
    checkIndexedRow_append table [2,2,2,2,1,1,1] classSegment2 classSegment3 refs51Segment2 refs51Segment3 (by decide)]
  decide

theorem residue51_checked : (2 * indexedCoverSum table 11 classes refs23 refs51) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs51Segment0 ++ (refs51Segment1 ++ (refs51Segment2 ++ refs51Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs51Segment0 (refs51Segment1 ++ (refs51Segment2 ++ refs51Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs51Segment1 (refs51Segment2 ++ refs51Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs51Segment2 refs51Segment3 (by decide) (by decide)]
  decide

theorem row52_checked : checkIndexedRow table [2,2,2,1,1,1,1,1] classes refs52 = true := by
  change checkIndexedRow table [2,2,2,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs52Segment0 ++ (refs52Segment1 ++ (refs52Segment2 ++ refs52Segment3))) = true
  rw [checkIndexedRow_append table [2,2,2,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs52Segment0 (refs52Segment1 ++ (refs52Segment2 ++ refs52Segment3)) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs52Segment1 (refs52Segment2 ++ refs52Segment3) (by decide),
    checkIndexedRow_append table [2,2,2,1,1,1,1,1] classSegment2 classSegment3 refs52Segment2 refs52Segment3 (by decide)]
  decide

theorem residue52_checked : (2 * indexedCoverSum table 11 classes refs23 refs52) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs52Segment0 ++ (refs52Segment1 ++ (refs52Segment2 ++ refs52Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs52Segment0 (refs52Segment1 ++ (refs52Segment2 ++ refs52Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs52Segment1 (refs52Segment2 ++ refs52Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs52Segment2 refs52Segment3 (by decide) (by decide)]
  decide

theorem row53_checked : checkIndexedRow table [2,2,1,1,1,1,1,1,1] classes refs53 = true := by
  change checkIndexedRow table [2,2,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs53Segment0 ++ (refs53Segment1 ++ (refs53Segment2 ++ refs53Segment3))) = true
  rw [checkIndexedRow_append table [2,2,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs53Segment0 (refs53Segment1 ++ (refs53Segment2 ++ refs53Segment3)) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs53Segment1 (refs53Segment2 ++ refs53Segment3) (by decide),
    checkIndexedRow_append table [2,2,1,1,1,1,1,1,1] classSegment2 classSegment3 refs53Segment2 refs53Segment3 (by decide)]
  decide

theorem residue53_checked : (2 * indexedCoverSum table 11 classes refs23 refs53) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs53Segment0 ++ (refs53Segment1 ++ (refs53Segment2 ++ refs53Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs53Segment0 (refs53Segment1 ++ (refs53Segment2 ++ refs53Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs53Segment1 (refs53Segment2 ++ refs53Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs53Segment2 refs53Segment3 (by decide) (by decide)]
  decide

theorem row54_checked : checkIndexedRow table [2,1,1,1,1,1,1,1,1,1] classes refs54 = true := by
  change checkIndexedRow table [2,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs54Segment0 ++ (refs54Segment1 ++ (refs54Segment2 ++ refs54Segment3))) = true
  rw [checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs54Segment0 (refs54Segment1 ++ (refs54Segment2 ++ refs54Segment3)) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs54Segment1 (refs54Segment2 ++ refs54Segment3) (by decide),
    checkIndexedRow_append table [2,1,1,1,1,1,1,1,1,1] classSegment2 classSegment3 refs54Segment2 refs54Segment3 (by decide)]
  decide

theorem residue54_checked : (2 * indexedCoverSum table 11 classes refs23 refs54) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs54Segment0 ++ (refs54Segment1 ++ (refs54Segment2 ++ refs54Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs54Segment0 (refs54Segment1 ++ (refs54Segment2 ++ refs54Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs54Segment1 (refs54Segment2 ++ refs54Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs54Segment2 refs54Segment3 (by decide) (by decide)]
  decide

theorem row55_checked : checkIndexedRow table [1,1,1,1,1,1,1,1,1,1,1] classes refs55 = true := by
  change checkIndexedRow table [1,1,1,1,1,1,1,1,1,1,1] (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs55Segment0 ++ (refs55Segment1 ++ (refs55Segment2 ++ refs55Segment3))) = true
  rw [checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1] classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs55Segment0 (refs55Segment1 ++ (refs55Segment2 ++ refs55Segment3)) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1] classSegment1 (classSegment2 ++ classSegment3) refs55Segment1 (refs55Segment2 ++ refs55Segment3) (by decide),
    checkIndexedRow_append table [1,1,1,1,1,1,1,1,1,1,1] classSegment2 classSegment3 refs55Segment2 refs55Segment3 (by decide)]
  decide

theorem residue55_checked : (2 * indexedCoverSum table 11 classes refs23 refs55) % 1000000007 ≠ 0 := by
  change (2 * indexedCoverSum table 11 (classSegment0 ++ (classSegment1 ++ (classSegment2 ++ classSegment3))) (refs23Segment0 ++ (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3))) (refs55Segment0 ++ (refs55Segment1 ++ (refs55Segment2 ++ refs55Segment3)))) % 1000000007 ≠ 0
  rw [indexedCoverSum_append table 11 classSegment0 (classSegment1 ++ (classSegment2 ++ classSegment3)) refs23Segment0 (refs23Segment1 ++ (refs23Segment2 ++ refs23Segment3)) refs55Segment0 (refs55Segment1 ++ (refs55Segment2 ++ refs55Segment3)) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment1 (classSegment2 ++ classSegment3) refs23Segment1 (refs23Segment2 ++ refs23Segment3) refs55Segment1 (refs55Segment2 ++ refs55Segment3) (by decide) (by decide),
    indexedCoverSum_append table 11 classSegment2 classSegment3 refs23Segment2 refs23Segment3 refs55Segment2 refs55Segment3 (by decide) (by decide)]
  decide

end HSTZ.TauCetiFinite.D11
