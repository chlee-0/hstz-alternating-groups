import HSTZ.CoreMultiplicity
import OAI.RepresentationTheory.Saxl.SupportSeparation

/-! An irreducible complement inside the core multiplicity representation.
This selects a subspace, not a Specht shape or a tensor dimension. -/
namespace HSTZ
open scoped MonoidAlgebra TensorProduct
noncomputable section
variable {G H U V : Type*} [Group G] [Group H]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G U) (tau : Representation ℂ (G × H) V)

instance multiplicityAddCommGroup : AddCommGroup (coreMultiplicity rho tau) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- Restrict evaluation to a complementary subrepresentation. -/
def multiplicitySectorMap (S : Subrepresentation (complementMultiplicity rho tau)) :
    Representation.IntertwiningMap (independentTensor rho S.toRepresentation) tau :=
  (multiplicityIntertwiner rho tau).comp
    (independentTensorMap (Representation.IntertwiningMap.id rho)
      ({ toLinearMap := S.toSubmodule.subtype
         isIntertwining' := fun _ => LinearMap.ext (fun _ => rfl) } :
        Representation.IntertwiningMap S.toRepresentation (complementMultiplicity rho tau)))

@[simp] theorem multiplicitySectorMap_tmul
    (S : Subrepresentation (complementMultiplicity rho tau)) (u : U) (f : S) :
    multiplicitySectorMap rho tau S (u ⊗ₜ[ℂ] f) = f.val u := rfl

/-- A nonzero coordinate in a sector forces nonzero evaluation there. -/
theorem multiplicitySectorMap_ne_zero
    (S : Subrepresentation (complementMultiplicity rho tau))
    (f : S) (hf : f.val ≠ 0) : multiplicitySectorMap rho tau S ≠ 0 := by
  intro he
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  have hx := congrArg (fun L : Representation.IntertwiningMap
    (independentTensor rho S.toRepresentation) tau => L (u ⊗ₜ[ℂ] f)) he
  exact hx

/-- Maschke's theorem selects an irreducible complement and a nonzero tensor map. -/
theorem exists_multiplicity_constituent [Finite H]
    (f : coreMultiplicity rho tau) (hf : f ≠ 0) :
    ∃ S : Subrepresentation (complementMultiplicity rho tau),
      Representation.IsIrreducible S.toRepresentation ∧
      multiplicitySectorMap rho tau S ≠ 0 := by
  classical
  let eta := complementMultiplicity rho tau
  letI : NeZero (Nat.card H : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'⟩
  have ht : (⊤ : Submodule ℂ[H] eta.asModule) ≠ ⊥ := by
    intro he
    have hm : eta.asModuleEquiv.symm f ∈ (⊤ : Submodule ℂ[H] eta.asModule) := trivial
    rw [he] at hm
    have hz := (Submodule.mem_bot _).mp hm
    exact hf (eta.asModuleEquiv.symm.injective (hz.trans (map_zero _).symm))
  obtain ⟨S, _, hS⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le (⊤ : Submodule ℂ[H] eta.asModule)).resolve_left ht
  letI := hS
  letI : Nontrivial S := IsSimpleModule.nontrivial (R := ℂ[H]) (M := S)
  let P := Subrepresentation.ofSubmodule' S
  have hP : Representation.IsIrreducible P.toRepresentation :=
    OAI.Saxl.subrep_irreducible_of_simple S
  obtain ⟨m, hm⟩ := exists_ne (0 : S)
  let p : P := ⟨eta.asModuleEquiv m.val, m.property⟩
  have hp : p.val ≠ 0 := by
    intro he
    apply hm
    apply Subtype.ext
    exact eta.asModuleEquiv.injective (he.trans (map_zero _).symm)
  exact ⟨P, hP, multiplicitySectorMap_ne_zero rho tau P p hp⟩
end
end HSTZ
#print axioms HSTZ.multiplicitySectorMap_tmul
#print axioms HSTZ.multiplicitySectorMap_ne_zero
#print axioms HSTZ.exists_multiplicity_constituent
