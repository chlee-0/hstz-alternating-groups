import HSTZ.CyclicSpan
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-! Lifting embeddings through an equivariant projection: the semisimple
image-transfer argument used in the HSTZ/OpenAI support arguments.
No irreducible, Specht or tensor constituent is assumed here. -/
namespace HSTZ

section Modules
variable {A U V W : Type*} [Ring A] [IsSemisimpleRing A]
  [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
  [AddCommGroup W] [Module A W]

/-- A submodule embedding in a quotient lifts to an embedding upstairs. -/
theorem semisimple_injective_lift (f : V →ₗ[A] W) (hf : Function.Surjective f)
    (j : U →ₗ[A] W) (hj : Function.Injective j) :
    ∃ i : U →ₗ[A] V, Function.Injective i ∧ ∀ u, f (i u)=j u := by
  letI : Module.Projective A U := Module.projective_of_isSemisimpleRing A U
  obtain ⟨i,hi⟩ := Module.projective_lifting_property f j hf
  refine ⟨i,?_,?_⟩
  · intro u w huw
    apply hj
    rw [← hi]
    simpa only [LinearMap.comp_apply] using congrArg f huw
  · intro u
    exact DFunLike.congr_fun hi u
end Modules

section Representations
variable {K G U V W : Type*} [Field K] [Group G] [Finite G]
  [NeZero (Nat.card G : K)]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Finite-group version with nonzero group order, using Maschke's theorem and
intertwining maps. Irreducibility or finite-dimensionality of the embedded
module is not needed. -/
theorem equivariant_injective_lift
    {rho : Representation K G V} {sigma : Representation K G W} {tau : Representation K G U}
    (phi : Representation.IntertwiningMap rho sigma) (hphi : Function.Surjective phi)
    (j : Representation.IntertwiningMap tau sigma) (hj : Function.Injective j) :
    ∃ i : Representation.IntertwiningMap tau rho,
      Function.Injective i ∧ ∀ u, phi (i u)=j u := by
  let f := Representation.IntertwiningMap.equivLinearMapAsModule rho sigma phi
  let j' := Representation.IntertwiningMap.equivLinearMapAsModule tau sigma j
  obtain ⟨i',hi,hcomp⟩ := semisimple_injective_lift f hphi j' hj
  let i := (Representation.IntertwiningMap.equivLinearMapAsModule tau rho).symm i'
  exact ⟨i,hi,hcomp⟩

/-- Every embedding in the projected cyclic image lifts into the original
cyclic space of the prescribed vector. It does not assert that any particular
irreducible module embeds in the image. -/
theorem cyclicImage_embedding_lift
    {rho : Representation K G V} {sigma : Representation K G W} {tau : Representation K G U}
    (phi : Representation.IntertwiningMap rho sigma) (v : V)
    (j : Representation.IntertwiningMap tau (cyclicSubrepresentation sigma (phi v)).toRepresentation)
    (hj : Function.Injective j) :
    ∃ i : Representation.IntertwiningMap tau (cyclicSubrepresentation rho v).toRepresentation,
      Function.Injective i ∧ ∀ u, cyclicImageMap phi v (i u)=j u :=
  equivariant_injective_lift (cyclicImageMap phi v) (cyclicImageMap_surjective phi v) j hj
end Representations

end HSTZ
#print axioms HSTZ.semisimple_injective_lift
#print axioms HSTZ.equivariant_injective_lift
#print axioms HSTZ.cyclicImage_embedding_lift
