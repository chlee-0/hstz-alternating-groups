import HSTZ.TauCetiFinite.DegreeFiveMoments
import HSTZ.TauCetiFinite.Degrees.D6
import HSTZ.TauCetiFinite.Degrees.D7
import HSTZ.TauCetiFinite.Degrees.D8
import HSTZ.TauCetiFinite.Degrees.D9
import HSTZ.TauCetiFinite.Degrees.D10
import HSTZ.TauCetiFinite.Degrees.D11
import HSTZ.TauCetiFinite.Degrees.D12
import HSTZ.TauCetiFinite.Degrees.D13
import HSTZ.TauCetiFinite.Degrees.D14
import HSTZ.TauCetiFinite.Degrees.D15

/-!
Finite arithmetic for the fixed witnesses in degrees five to fifteen. Each degree uses
its proved complete canonical class catalog and TauCeti's Specht characters. The
residue only certifies that an integer is nonzero; representation multiplicity and
alternating covering come from the separate representation-theoretic bridges.
-/
namespace HSTZ.TauCetiFinite

/-- All 672 target partitions, without reduction by transposition. -/
theorem finite_numerators (n : ℕ) (h5 : 5 ≤ n) (h15 : n ≤ 15) :
    ∃ lam : Nat.Partition n,
      evenNormNumerator lam = (n.factorial : ℤ) ∧
      ∀ nu : Nat.Partition n,
        evenCoverNumerator lam nu % 1000000007 ≠ 0 := by
  interval_cases n
  · exact ⟨witness5, degree_five_norm, degree_five_cover_residue⟩
  · exact ⟨D6.witness, D6.norm, D6.cover_residue⟩
  · exact ⟨D7.witness, D7.norm, D7.cover_residue⟩
  · exact ⟨D8.witness, D8.norm, D8.cover_residue⟩
  · exact ⟨D9.witness, D9.norm, D9.cover_residue⟩
  · exact ⟨D10.witness, D10.norm, D10.cover_residue⟩
  · exact ⟨D11.witness, D11.norm, D11.cover_residue⟩
  · exact ⟨D12.witness, D12.norm, D12.cover_residue⟩
  · exact ⟨D13.witness, D13.norm, D13.cover_residue⟩
  · exact ⟨D14.witness, D14.norm, D14.cover_residue⟩
  · exact ⟨D15.witness, D15.norm, D15.cover_residue⟩

/-- The integer target is nonzero; no modular division is performed. -/
theorem finite_numerators_nonzero (n : ℕ) (h5 : 5 ≤ n) (h15 : n ≤ 15) :
    ∃ lam : Nat.Partition n,
      evenNormNumerator lam = (n.factorial : ℤ) ∧
      ∀ nu : Nat.Partition n, evenCoverNumerator lam nu ≠ 0 := by
  obtain ⟨lam, hD, hE⟩ := finite_numerators n h5 h15
  refine ⟨lam, hD, fun nu hz => ?_⟩
  exact hE nu (by rw [hz]; rfl)

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.finite_numerators
#print axioms HSTZ.TauCetiFinite.finite_numerators_nonzero
