import HSTZ.TensorSquareCovering
import HSTZ.TauCetiIntegration

/-!
# Tensor-square covering for every alternating group of degree at least five

The theorem below states, with Mathlib's notions only, that some irreducible complex
representation of the alternating group on `Fin n` has a tensor square into which every
irreducible complex representation maps by a nonzero intertwiner. A nonzero intertwiner
from an irreducible representation is injective, and irreducible representations of a
finite group are finite-dimensional, so no separate finiteness hypothesis is needed.

Degrees 5 through 15 are proved with finite character certificates; degrees `n ≥ 16` use an
explicit Specht-module witness (`HSTZ.tensor_square_covering`), built on the Specht-module
development from OpenAI's `math` repository in `OpenAITensorSquares`.
-/
namespace HSTZ

/-- For every `n ≥ 5`, some irreducible complex representation `ρ` of the alternating
group on `Fin n` has a tensor square `ρ ⊗ ρ` into which every irreducible complex
representation `σ` maps by a nonzero intertwiner. The statement is written out with
Mathlib's notions; it is `HSTZ.TensorSquareCovering n` from `HSTZ/TensorSquareCovering.lean`,
which imports only Mathlib. -/
theorem tensor_square_covering_ge5 (n : ℕ) (hn : 5 ≤ n) :
    ∃ (V : ModuleCat.{0} ℂ)
      (ρ : Representation ℂ (alternatingGroup (Fin n)) V),
      Representation.IsIrreducible ρ ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
          (σ : Representation ℂ (alternatingGroup (Fin n)) W)
          [Representation.IsIrreducible σ],
          ∃ f : Representation.IntertwiningMap σ (Representation.tprod ρ ρ), f ≠ 0 := by
  exact TauCetiIntegration.covering_ge5 n hn

end HSTZ

-- Print the fully elaborated statement (only Mathlib constants appear) and its axioms.
set_option pp.all true in
#check HSTZ.tensor_square_covering_ge5
#print axioms HSTZ.tensor_square_covering_ge5
