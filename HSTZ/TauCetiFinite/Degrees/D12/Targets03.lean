import HSTZ.TauCetiFinite.Degrees.D12.Segments
import HSTZ.TauCetiFinite.Degrees.D12.Moments06
import HSTZ.TauCetiFinite.Degrees.D12.Moments07

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem targetsSegment3 : ∀ nu ∈ classSegment3, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 12 classes refs33 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment3, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs48, row48_checked, residue48_checked⟩
  · exact ⟨refs49, row49_checked, residue49_checked⟩
  · exact ⟨refs50, row50_checked, residue50_checked⟩
  · exact ⟨refs51, row51_checked, residue51_checked⟩
  · exact ⟨refs52, row52_checked, residue52_checked⟩
  · exact ⟨refs53, row53_checked, residue53_checked⟩
  · exact ⟨refs54, row54_checked, residue54_checked⟩
  · exact ⟨refs55, row55_checked, residue55_checked⟩
  · exact ⟨refs56, row56_checked, residue56_checked⟩
  · exact ⟨refs57, row57_checked, residue57_checked⟩
  · exact ⟨refs58, row58_checked, residue58_checked⟩
  · exact ⟨refs59, row59_checked, residue59_checked⟩
  · exact ⟨refs60, row60_checked, residue60_checked⟩
  · exact ⟨refs61, row61_checked, residue61_checked⟩
  · exact ⟨refs62, row62_checked, residue62_checked⟩
  · exact ⟨refs63, row63_checked, residue63_checked⟩

end HSTZ.TauCetiFinite.D12
