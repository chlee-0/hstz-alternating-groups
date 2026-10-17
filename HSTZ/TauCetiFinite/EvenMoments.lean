import HSTZ.TauCetiFinite.CharacterBridge
import TauCeti.RepresentationTheory.Symmetric.ClassSize

/-!
Integer targets for the finite range, defined from TauCeti's Specht character values.
These are not executable checkers; complete partition enumeration and checked sums are
connected to them separately. The representation-theoretic identities are not
asserted by these definitions; they are proved in `RestrictionNorm` and
`EvenMultiplicity`.

The sums run over even classes directly rather than using an isomorphism between a
transposed Specht module and a sign twist. `evenNormNumerator lam = n!` gives the
norm-one condition once its restriction-character identity is proved, and
`evenCoverNumerator lam nu` is n! times the multiplicity of S^nu in X ⊕ (sgn ⊗ X),
where X = S^lam ⊗ S^lam.
-/
namespace HSTZ.TauCetiFinite
noncomputable section

/-- For the cycle partition of a permutation, this says that the permutation is even. -/
def EvenCycleShape {n : ℕ} (ρ : Nat.Partition n) : Prop :=
  (n - ρ.parts.card) % 2 = 0

open scoped Classical in
def evenNormNumerator {n : ℕ} (lam : Nat.Partition n) : ℤ :=
  2 * ∑ ρ : Nat.Partition n,
    if EvenCycleShape ρ then
      ((n.factorial / TauCeti.zPart ρ : ℕ) : ℤ) * TauCeti.spechtCharValue lam ρ ^ 2
    else 0

open scoped Classical in
def evenCoverNumerator {n : ℕ} (lam ν : Nat.Partition n) : ℤ :=
  2 * ∑ ρ : Nat.Partition n,
    if EvenCycleShape ρ then
      ((n.factorial / TauCeti.zPart ρ : ℕ) : ℤ) *
        TauCeti.spechtCharValue lam ρ ^ 2 * TauCeti.spechtCharValue ν ρ
    else 0

/-- Denominator-free nonvanishing; no inverse of n! or prime modulus is required. -/
theorem positive_of_scaled_residue (n multiplicity : ℕ) (numerator modulus : ℤ)
    (hscale : numerator = (n.factorial : ℤ) * (multiplicity : ℤ))
    (hres : numerator % modulus ≠ 0) : 0 < multiplicity := by
  by_contra h
  have hz : multiplicity = 0 := Nat.eq_zero_of_not_pos h
  simp [hscale, hz] at hres

end
end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.positive_of_scaled_residue
