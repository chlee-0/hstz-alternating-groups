import HSTZ.IntertwiningCompat
import HSTZ.ProjectionLift
import Mathlib.RepresentationTheory.Induced

/-! Split injections under ordinary induction. The induced map is Mathlib's
tensor/coinvariant construction with the inverse/right action convention.
Injectivity comes from a retraction; it is not assumed to survive an arbitrary
quotient. -/
namespace HSTZ
open TensorProduct

/-- A semisimple module embedding has a linear retraction. -/
theorem semisimple_retraction {A U V : Type*} [Ring A] [IsSemisimpleRing A]
    [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    (j : U →ₗ[A] V) (hj : Function.Injective j) :
    ∃ p : V →ₗ[A] U, ∀ u, p (j u) = u := by
  obtain ⟨p, hp⟩ := IsSemisimpleModule.extension_property j hj (LinearMap.id : U →ₗ[A] U)
  exact ⟨p, fun u => DFunLike.congr_fun hp u⟩

/-- Maschke's theorem supplies an equivariant retraction. -/
theorem equivariant_retraction {K H U V : Type*} [Field K] [Group H] [Finite H]
    [NeZero (Nat.card H : K)] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V]
    {tau : Representation K H U} {sigma : Representation K H V}
    (j : Representation.IntertwiningMap tau sigma) (hj : Function.Injective j) :
    ∃ p : Representation.IntertwiningMap sigma tau, ∀ u, p (j u) = u := by
  let j' := Representation.IntertwiningMap.equivLinearMapAsModule tau sigma j
  obtain ⟨p', hp⟩ := semisimple_retraction j' hj
  exact ⟨(Representation.IntertwiningMap.equivLinearMapAsModule sigma tau).symm p', hp⟩

section Induction
variable {R H G U V W : Type*} [CommRing R] [Group H] [Group G]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
  {tau : Representation R H U} {sigma : Representation R H V}
  {eta : Representation R H W}

/-- The induced linear map, reusing the library's coinvariant map. -/
noncomputable def inducedMapLinear (phi : H →* G)
    (j : Representation.IntertwiningMap tau sigma) :
    Representation.IndV phi tau →ₗ[R] Representation.IndV phi sigma :=
  Representation.Coinvariants.map _ _ ⟨LinearMap.lTensor (MonoidAlgebra R G) j.toLinearMap, fun h => by
    apply TensorProduct.ext'
    intro x u
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      LinearMap.lTensor_tmul]
    exact congrArg (fun v : V => (((Representation.leftRegular R G).comp phi) h x) ⊗ₜ[R] v)
      (j.map_action h u)⟩

@[simp] theorem inducedMapLinear_mk (phi : H →* G)
    (j : Representation.IntertwiningMap tau sigma) (g : G) (u : U) :
    inducedMapLinear phi j (Representation.IndV.mk phi tau g u) =
      Representation.IndV.mk phi sigma g (j u) := by
  simp [inducedMapLinear, Representation.IndV.mk]

/-- The tensor/coinvariant map is equivariant. -/
noncomputable def inducedMap (phi : H →* G)
    (j : Representation.IntertwiningMap tau sigma) :
    Representation.IntertwiningMap (Representation.ind phi tau) (Representation.ind phi sigma) where
  toLinearMap := inducedMapLinear phi j
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have he : (inducedMapLinear phi j).comp (Representation.ind phi tau g) =
        (Representation.ind phi sigma g).comp (inducedMapLinear phi j) := by
      apply Representation.IndV.hom_ext
      intro h
      ext u
      change inducedMapLinear phi j (Representation.ind phi tau g (Representation.IndV.mk phi tau h u)) =
        Representation.ind phi sigma g (inducedMapLinear phi j (Representation.IndV.mk phi tau h u))
      rw [Representation.ind_mk, inducedMapLinear_mk, inducedMapLinear_mk, Representation.ind_mk]
    exact DFunLike.congr_fun he x

@[simp] theorem inducedMap_mk (phi : H →* G)
    (j : Representation.IntertwiningMap tau sigma) (g : G) (u : U) :
    inducedMap phi j (Representation.IndV.mk phi tau g u) =
      Representation.IndV.mk phi sigma g (j u) := inducedMapLinear_mk phi j g u

/-- A retraction induces a retraction, over any commutative ring. -/
theorem inducedMap_leftInverse (phi : H →* G)
    (j : Representation.IntertwiningMap tau sigma) (p : Representation.IntertwiningMap sigma tau)
    (hp : ∀ u, p (j u) = u) : Function.LeftInverse (inducedMap phi p) (inducedMap phi j) := by
  have he : (inducedMap phi p).toLinearMap.comp (inducedMap phi j).toLinearMap = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext u
    change inducedMap phi p (inducedMap phi j (Representation.IndV.mk phi tau g u)) = _
    rw [inducedMap_mk, inducedMap_mk, hp]
    rfl
  exact fun x => DFunLike.congr_fun he x

end Induction

/-- Under Maschke hypotheses on the finite subgroup, induction preserves
embeddings. The ambient group need not be finite and the inducing homomorphism
need not be injective. -/
theorem inducedMap_injective {K H G U V : Type*} [Field K] [Group H] [Finite H]
    [NeZero (Nat.card H : K)] [Group G] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {tau : Representation K H U} {sigma : Representation K H V}
    (phi : H →* G) (j : Representation.IntertwiningMap tau sigma) (hj : Function.Injective j) :
    Function.Injective (inducedMap phi j) := by
  obtain ⟨p, hp⟩ := equivariant_retraction j hj
  exact (inducedMap_leftInverse phi j p hp).injective

end HSTZ
#print axioms HSTZ.semisimple_retraction
#print axioms HSTZ.equivariant_retraction
#print axioms HSTZ.inducedMap_mk
#print axioms HSTZ.inducedMap_leftInverse
#print axioms HSTZ.inducedMap_injective
