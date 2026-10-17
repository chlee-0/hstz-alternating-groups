import HSTZ.IntertwiningCompat
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.RepresentationTheory.Rep.Iso

/-! A bridge between finite-dimensional representations, their isomorphisms and the
categorical `FDRep` character API. The classification of Specht modules is not used. -/
namespace HSTZ
open CategoryTheory
open scoped MonoidAlgebra
noncomputable section
universe u
variable {k G U V : Type u} [Field k] [Monoid G]
  [AddCommGroup U] [Module k U] [Module.Finite k U]
  [AddCommGroup V] [Module k V] [Module.Finite k V]
  (rho : Representation k G U) (sigma : Representation k G V)

/-- A categorical morphism is an equivariant linear map. -/
def fdHomIntertwiner (f : FDRep.of rho ⟶ FDRep.of sigma) :
    Representation.IntertwiningMap rho sigma where
  toLinearMap := f.hom.hom.hom
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (congrArg (fun m => m.hom.hom) (f.comm g)) x

/-- A categorical isomorphism yields an intertwiner. -/
def fdIsoIntertwiner (i : FDRep.of rho ≅ FDRep.of sigma) :
    Representation.IntertwiningMap rho sigma := fdHomIntertwiner rho sigma i.hom

theorem fdIsoIntertwiner_bijective (i : FDRep.of rho ≅ FDRep.of sigma) :
    Function.Bijective (fdIsoIntertwiner rho sigma i) :=
  (FDRep.isoToLinearEquiv i).bijective

/-- A bijective intertwiner produces a categorical isomorphism, using its linear
inverse and its equivariance. -/
def fdIsoOfBijective (f : Representation.IntertwiningMap rho sigma)
    (hf : Function.Bijective f) : FDRep.of rho ≅ FDRep.of sigma := by
  let e := LinearEquiv.ofBijective f.toLinearMap hf
  exact Action.mkIso e.toFGModuleCatIso (fun g => by
    apply FGModuleCat.hom_ext
    ext x
    exact f.map_action g x)

/-- Irreducibility gives the categorical `Simple` hypothesis required by `FDRep`
character orthogonality, via the group-algebra functor. -/
theorem fdRep_simple [Representation.IsIrreducible rho] : Simple (FDRep.of rho) := by
  let F := (forget₂ (FDRep k G) (Rep k G)) ⋙
    (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).functor
  haveI : Simple (F.obj (FDRep.of rho)) := by
    change Simple (ModuleCat.of k[G] rho.asModule)
    infer_instance
  refine ⟨fun {Y} f _ => ?_⟩
  haveI : Mono (F.map f) := inferInstance
  have hz : F.map (0 : Y ⟶ FDRep.of rho) = 0 := rfl
  constructor
  · intro h he
    letI := h
    haveI : IsIso (F.map f) := inferInstance
    have hn := (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
    exact hn (by rw [he, hz])
  · intro hn
    have hmap : F.map f ≠ 0 := by
      intro he
      apply hn
      apply F.map_injective
      exact he.trans hz.symm
    haveI : IsIso (F.map f) := isIso_of_mono_of_nonzero hmap
    exact isIso_of_reflects_iso f F

end
end HSTZ
#print axioms HSTZ.fdHomIntertwiner
#print axioms HSTZ.fdIsoIntertwiner_bijective
#print axioms HSTZ.fdIsoOfBijective
#print axioms HSTZ.fdRep_simple
