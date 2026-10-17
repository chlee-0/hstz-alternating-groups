import HSTZ.IndependentTensor

/-! The core multiplicity space, the complement action on it, and tensor evaluation.
The core and complement act independently in a product group. -/
namespace HSTZ
open TensorProduct
section Multiplicity
variable {R G H U V : Type*} [CommRing R] [Monoid G] [Monoid H]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  (rho : Representation R G U) (tau : Representation R (G × H) V)

abbrev coreMultiplicity := Representation.IntertwiningMap rho
  (tau.comp (MonoidHom.inl G H))

theorem core_complement_commute (g : G) (h : H) (v : V) :
    tau (1,h) (tau (g,1) v) = tau (g,1) (tau (1,h) v) := by
  have he : (1,h) * (g,1) = (g,1) * (1,h) := by ext <;> simp
  rw [← Module.End.mul_apply, ← tau.map_mul, he, tau.map_mul, Module.End.mul_apply]

/-- The complement acts on core intertwiners by postcomposition. -/
def complementMultiplicity : Representation R H (coreMultiplicity rho tau) where
  toFun h :=
    { toFun := fun f =>
        { toLinearMap := (tau (1,h)).comp f.toLinearMap
          isIntertwining' := by
            intro g
            apply LinearMap.ext
            intro u
            change tau (1,h) (f (rho g u)) = tau (g,1) (tau (1,h) (f u))
            rw [Representation.IntertwiningMap.isIntertwining _ _ f g u]
            exact core_complement_commute tau g h (f u) }
      map_add' := by intro f k; ext u; exact (tau (1,h)).map_add (f u) (k u)
      map_smul' := by intro c f; ext u; exact (tau (1,h)).map_smul c (f u) }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    change tau (1,1) (f u) = f u
    have he := tau.map_one
    exact congrArg (fun L : Module.End R V => L (f u)) he
  map_mul' := by
    intro h k
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    change tau (1,h*k) (f u) = tau (1,h) (tau (1,k) (f u))
    have he := tau.map_mul (1,h) (1,k)
    simpa only [Prod.mk_mul_mk, one_mul, Module.End.mul_apply] using
      congrArg (fun L : Module.End R V => L (f u)) he

@[simp] theorem complementMultiplicity_apply (h : H) (f : coreMultiplicity rho tau) (u : U) :
    complementMultiplicity rho tau h f u = tau (1,h) (f u) := rfl

/-- Evaluation, in the core-first order used by block tensors. -/
def multiplicityEvaluation : U ⊗[R] coreMultiplicity rho tau →ₗ[R] V :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun f => f u
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := by intro u v; ext f; exact f.toLinearMap.map_add u v
      map_smul' := by intro c u; ext f; exact f.toLinearMap.map_smul c u }

@[simp] theorem multiplicityEvaluation_tmul (u : U) (f : coreMultiplicity rho tau) :
    multiplicityEvaluation rho tau (u ⊗ₜ[R] f) = f u := rfl

/-- Evaluation is a product-group intertwiner, not just a core map. -/
def multiplicityIntertwiner : Representation.IntertwiningMap
    (independentTensor rho (complementMultiplicity rho tau)) tau where
  toLinearMap := multiplicityEvaluation rho tau
  isIntertwining' gh := by
    apply LinearMap.ext
    intro z
    have he : (multiplicityEvaluation rho tau).comp
        (independentTensor rho (complementMultiplicity rho tau) gh) =
        (tau gh).comp (multiplicityEvaluation rho tau) := by
      apply TensorProduct.ext'
      intro u f
      change tau (1,gh.2) (f (rho gh.1 u)) = tau gh (f u)
      rw [Representation.IntertwiningMap.isIntertwining _ _ f gh.1 u]
      change tau (1,gh.2) (tau (gh.1,1) (f u)) = tau gh (f u)
      have hp := tau.map_mul (1,gh.2) (gh.1,1)
      simpa only [Prod.mk_mul_mk, one_mul, mul_one, Prod.eta, Module.End.mul_apply] using
        (congrArg (fun L : Module.End R V => L (f u)) hp).symm
    exact DFunLike.congr_fun he z

/-- The range is the supremum of the ranges of the core maps. -/
theorem multiplicityEvaluation_range :
    (multiplicityEvaluation rho tau).range =
      ⨆ f : coreMultiplicity rho tau, f.toLinearMap.range := by
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul u f => exact (le_iSup (fun f : coreMultiplicity rho tau => f.toLinearMap.range) f) ⟨u,rfl⟩
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply iSup_le
    intro f
    rintro _ ⟨u,rfl⟩
    exact ⟨u ⊗ₜ[R] f,rfl⟩

theorem multiplicityEvaluation_ne_zero (f : coreMultiplicity rho tau) (hf : f ≠ 0) :
    multiplicityEvaluation rho tau ≠ 0 := by
  intro he
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  exact LinearMap.congr_fun he (u ⊗ₜ[R] f)
end Multiplicity
end HSTZ
#print axioms HSTZ.complementMultiplicity_apply
#print axioms HSTZ.multiplicityEvaluation_tmul
#print axioms HSTZ.multiplicityEvaluation_range
#print axioms HSTZ.multiplicityEvaluation_ne_zero
#print axioms HSTZ.multiplicityIntertwiner
