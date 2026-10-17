import Mathlib.RepresentationTheory.Intertwining

/-! Pointwise action compatibility with representation parameters inferred. -/

namespace Representation.IntertwiningMap

theorem map_action {A G V W : Type*} [Semiring A] [Monoid G]
    [AddCommMonoid V] [AddCommMonoid W] [Module A V] [Module A W]
    {ρ : Representation A G V} {σ : Representation A G W}
    (f : IntertwiningMap ρ σ) (g : G) (v : V) : f (ρ g v) = σ g (f v) :=
  isIntertwining ρ σ f g v

end Representation.IntertwiningMap
