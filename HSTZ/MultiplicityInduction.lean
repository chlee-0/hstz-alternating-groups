import HSTZ.MultiplicityConstituent
import HSTZ.InducedTarget

/-! Induced target support with a selected irreducible complement. -/
namespace HSTZ
/-- Nonzero core multiplicity gives an irreducible complementary factor
and a target embedding in ordinary induction of the tensor. -/
theorem product_induced_embedding_of_core
    {G H A U V : Type*} [Group G] [Group H] [Finite H] [Group A] [Finite A]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (phi : G × H →* A) (rho : Representation ℂ G U) (tau : Representation ℂ A V)
    [Representation.IsIrreducible tau]
    (f : coreMultiplicity rho (tau.comp phi)) (hf : f ≠ 0) :
    ∃ S : Subrepresentation (complementMultiplicity rho (tau.comp phi)),
      Representation.IsIrreducible S.toRepresentation ∧
      ∃ E : Representation.IntertwiningMap tau
        (Representation.ind phi (independentTensor rho S.toRepresentation)), Function.Injective E := by
  letI : NeZero (Nat.card A : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card A).ne'⟩
  obtain ⟨S, hS, hmap⟩ := exists_multiplicity_constituent rho (tau.comp phi) f hf
  obtain ⟨E, hE⟩ := induced_target_embedding_of_nonzero phi
    (independentTensor rho S.toRepresentation) tau
    (multiplicitySectorMap rho (tau.comp phi) S) hmap
  exact ⟨S, hS, E, hE⟩

/-- Keep the original source carrier by precomposing with an injection.
The selected complement still belongs to the target multiplicity representation. -/
theorem product_induced_embedding_precompose
    {G H A U V W : Type*} [Group G] [Group H] [Finite H] [Group A] [Finite A]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (phi : G × H →* A) (rho : Representation ℂ G U) (tau : Representation ℂ A V)
    [Representation.IsIrreducible tau]
    (f : coreMultiplicity rho (tau.comp phi)) (hf : f ≠ 0)
    (sigma : Representation ℂ A W)
    (j : Representation.IntertwiningMap sigma tau) (hj : Function.Injective j) :
    ∃ S : Subrepresentation (complementMultiplicity rho (tau.comp phi)),
      Representation.IsIrreducible S.toRepresentation ∧
      ∃ E : Representation.IntertwiningMap sigma
        (Representation.ind phi (independentTensor rho S.toRepresentation)), Function.Injective E := by
  obtain ⟨S, hS, E, hE⟩ := product_induced_embedding_of_core phi rho tau f hf
  exact ⟨S, hS, E.comp j, hE.comp hj⟩

end HSTZ
#print axioms HSTZ.product_induced_embedding_of_core

#print axioms HSTZ.product_induced_embedding_precompose
