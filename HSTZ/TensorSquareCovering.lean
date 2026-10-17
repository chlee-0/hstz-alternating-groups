import Mathlib

/-!
# The statement

This file imports only Mathlib, so every notion in the statement below is Mathlib's.
`HSTZ.TensorSquareCovering n` is the proposition proved for every `n ≥ 5` as
`HSTZ.tensor_square_covering_ge5` in `Statements.lean`. The carrier is packaged as a
`ModuleCat` object, so the statement mentions no Specht module, tableau or OpenAI (`OAI`)
definition; the large-degree and finite-range proofs both conclude this proposition.
-/
namespace HSTZ

/-- Some irreducible complex representation of the alternating group on `Fin n` has a
tensor square into which every irreducible complex representation maps by a nonzero
intertwiner. -/
def TensorSquareCovering (n : ℕ) : Prop :=
  ∃ (V : ModuleCat.{0} ℂ)
    (ρ : Representation ℂ (alternatingGroup (Fin n)) V),
    Representation.IsIrreducible ρ ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
        (σ : Representation ℂ (alternatingGroup (Fin n)) W)
        [Representation.IsIrreducible σ],
        ∃ f : Representation.IntertwiningMap σ (Representation.tprod ρ ρ), f ≠ 0

/-- The finite-range proposition for degrees 5 through 15, proved as
`HSTZ.TauCetiFinite.finiteRangeConclusion`. -/
def FiniteRangeConclusion : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≤ 15 → TensorSquareCovering n

end HSTZ
