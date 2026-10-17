import HSTZ.PaperWitnessGe16

/-!
# Large-degree tensor-square covering for alternating groups

For every `n ≥ 16` there is an irreducible complex representation of the alternating
group on `Fin n` whose tensor square contains every irreducible complex representation.
The witness below is the restriction of a Specht representation.

`HSTZ.TauCetiIntegration` combines it with the finite-range proof to give the statement
for every `n ≥ 5` in `Statements.lean`.
-/

namespace HSTZ

open OAI.Saxl

/-- The Heide–Saxl–Tiep–Zalesski tensor-square covering conclusion for `n ≥ 16`.
A nonzero intertwiner from an irreducible representation is injective, so the
last quantifier expresses occurrence in the tensor square. -/
theorem tensor_square_covering (n : ℕ) (hn : 16 ≤ n) :
    ∃ (μ : YoungDiagram) (z : Tableau n μ),
      Representation.IsIrreducible ((spechtRep z).comp (alternatingGroup (Fin n)).subtype) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
        (σ : Representation ℂ (alternatingGroup (Fin n)) W) [Representation.IsIrreducible σ],
        ∃ f : Representation.IntertwiningMap σ
          (Representation.tprod ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)
            ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)), f ≠ 0 := by
  obtain ⟨k, b, delta, hp, hcard, h⟩ := paperWitness_alternating_ge16 n hn
  exact ⟨witnessDiagram k b delta hp.staircase_bound, canonicalTableau _ hcard, h _⟩

end HSTZ

#check HSTZ.tensor_square_covering
#print axioms HSTZ.tensor_square_covering
