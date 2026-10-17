import HSTZ.PieriSupport

/-! A nonzero restricted tensor map suffices for induced target support.
The ambient irreducible target and a Maschke lift supply the reverse injection;
injectivity of the tensor evaluation map is not assumed. -/
namespace HSTZ

theorem induced_target_embedding_of_nonzero
    {K D A U V : Type*} [Field K] [Group D] [Group A] [Finite A]
    [NeZero (Nat.card A : K)] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V]
    (phi : D →* A) (sigma : Representation K D U) (rho : Representation K A V)
    [Representation.IsIrreducible rho]
    (j : Representation.IntertwiningMap sigma (rho.comp phi)) (hj : j ≠ 0) :
    ∃ E : Representation.IntertwiningMap rho (Representation.ind phi sigma),
      Function.Injective E := by
  have hpoint : ∃ u, j u ≠ 0 := by
    by_contra he
    push_neg at he
    apply hj
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    exact he u
  obtain ⟨u, hu⟩ := hpoint
  let J := inducedIntertwiner phi sigma rho j
  have hJ : J ≠ 0 := by
    intro he
    have hz : J (Representation.IndV.mk phi sigma 1 u) = 0 := by rw [he]; rfl
    change inducedLinearMap phi sigma rho j (Representation.IndV.mk phi sigma 1 u) = 0 at hz
    rw [inducedLinearMap_mk] at hz
    exact hu (by simpa using hz)
  have hsur := intertwiner_surjective_of_irreducible J hJ
  obtain ⟨E, hE, _⟩ := equivariant_injective_lift J hsur
    (Representation.IntertwiningMap.id rho) (fun _ _ he => he)
  exact ⟨E, hE⟩
end HSTZ
#print axioms HSTZ.induced_target_embedding_of_nonzero
