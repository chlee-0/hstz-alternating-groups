import HSTZ.TauCetiFinite.Degrees.D12.Segments
import HSTZ.TauCetiFinite.Degrees.D12.Moments08
import HSTZ.TauCetiFinite.Degrees.D12.Moments09

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem targetsSegment4 : ∀ nu ∈ classSegment4, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 12 classes refs33 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment4, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs64, row64_checked, residue64_checked⟩
  · exact ⟨refs65, row65_checked, residue65_checked⟩
  · exact ⟨refs66, row66_checked, residue66_checked⟩
  · exact ⟨refs67, row67_checked, residue67_checked⟩
  · exact ⟨refs68, row68_checked, residue68_checked⟩
  · exact ⟨refs69, row69_checked, residue69_checked⟩
  · exact ⟨refs70, row70_checked, residue70_checked⟩
  · exact ⟨refs71, row71_checked, residue71_checked⟩
  · exact ⟨refs72, row72_checked, residue72_checked⟩
  · exact ⟨refs73, row73_checked, residue73_checked⟩
  · exact ⟨refs74, row74_checked, residue74_checked⟩
  · exact ⟨refs75, row75_checked, residue75_checked⟩
  · exact ⟨refs76, row76_checked, residue76_checked⟩

end HSTZ.TauCetiFinite.D12
