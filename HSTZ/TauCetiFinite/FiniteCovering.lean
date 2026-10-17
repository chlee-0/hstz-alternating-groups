import HSTZ.TauCetiFinite.FiniteNumerators
import HSTZ.TauCetiFinite.TensorCoverBridge

/-! Proves the finite-range conclusion for degrees five to fifteen by combining the
restriction-norm bridge, the embedding of the whole irreducible Specht module and the
two-projection argument with the kernel-checked numerators for each degree. -/
namespace HSTZ.TauCetiFinite

/-- The finite-range conclusion for every degree from five to fifteen. -/
theorem finiteRangeConclusion : HSTZ.FiniteRangeConclusion := by
  intro n h5 h15
  obtain ⟨lam, hD, hE⟩ := finite_numerators n h5 h15
  exact tensorSquareCovering_of_even_moments (by omega) lam 1000000007 hD hE

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.finiteRangeConclusion
