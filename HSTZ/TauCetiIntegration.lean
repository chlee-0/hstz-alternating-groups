import HSTZ.LargeDegreeStatements
import HSTZ.TauCetiFinite

/-!
Combines the large-degree Specht proof (`n ≥ 16`) and the finite-range proof
(`5 ≤ n ≤ 15`) into the tensor-square covering conclusion for every `n ≥ 5`.
Both ranges are stated through the model-independent proposition
`HSTZ.TensorSquareCovering`. `Statements` imports this module.
-/
namespace HSTZ.TauCetiIntegration

/-- Repackage the large-degree theorem `HSTZ.tensor_square_covering` as
`HSTZ.TensorSquareCovering n`. -/
theorem covering_ge16 (n : ℕ) (hn : 16 ≤ n) : HSTZ.TensorSquareCovering n := by
  obtain ⟨μ, t, hirr, hcover⟩ := HSTZ.tensor_square_covering n hn
  exact ⟨ModuleCat.of ℂ (OAI.Saxl.Specht t),
    (OAI.Saxl.spechtRep t).comp (alternatingGroup (Fin n)).subtype, hirr, hcover⟩

/-- The covering conclusion for every `n ≥ 5` from any proof of the finite-range
proposition; `covering_ge5` below supplies `HSTZ.TauCetiFinite.finiteRangeConclusion`. -/
theorem covering_ge5_of_finite_range (finiteRange : HSTZ.FiniteRangeConclusion)
    (n : ℕ) (hn : 5 ≤ n) : HSTZ.TensorSquareCovering n := by
  by_cases hlarge : 16 ≤ n
  · exact covering_ge16 n hlarge
  · exact finiteRange n hn (by omega)

end HSTZ.TauCetiIntegration
#print axioms HSTZ.TauCetiIntegration.covering_ge16
#print axioms HSTZ.TauCetiIntegration.covering_ge5_of_finite_range

-- The unconditional statement, using the proved finite range.
namespace HSTZ.TauCetiIntegration
/-- The tensor-square covering conclusion for every `n ≥ 5`. -/
theorem covering_ge5 (n : ℕ) (hn : 5 ≤ n) : HSTZ.TensorSquareCovering n := by
  exact covering_ge5_of_finite_range HSTZ.TauCetiFinite.finiteRangeConclusion n hn
end HSTZ.TauCetiIntegration
#print axioms HSTZ.TauCetiIntegration.covering_ge5
