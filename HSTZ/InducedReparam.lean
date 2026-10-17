import HSTZ.SectorInduction

/-! Ordinary-induction carrier maps under an isomorphism of inducing
groups. The ambient group, generators and inverse/right action are unchanged. -/
namespace HSTZ
section
variable {R H J G V : Type*} [CommRing R] [Group H] [Group J] [Group G]
  [AddCommGroup V] [Module R V]
  (e : H ≃* J) (phi : J →* G) (rho : Representation R J V)

noncomputable def reparamBase : Representation.IntertwiningMap (rho.comp e.toMonoidHom)
    ((Representation.ind phi rho).comp (phi.comp e.toMonoidHom)) where
  toLinearMap := Representation.IndV.mk phi rho 1
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    change Representation.IndV.mk phi rho 1 (rho (e h) u) =
      Representation.ind phi rho (phi (e h)) (Representation.IndV.mk phi rho 1 u)
    rw [Representation.ind_mk]
    simpa using (ind_mk_inv_mul phi rho (e h) 1 u).symm

/-- The forward intertwiner, retaining the ambient induced generators. -/
noncomputable def inducedReparam : Representation.IntertwiningMap
    (Representation.ind (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom))
    (Representation.ind phi rho) :=
  inducedIntertwiner (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom)
    (Representation.ind phi rho) (reparamBase e phi rho)

@[simp] theorem inducedReparam_mk (g : G) (u : V) :
    inducedReparam e phi rho (Representation.IndV.mk (phi.comp e.toMonoidHom)
      (rho.comp e.toMonoidHom) g u) = Representation.IndV.mk phi rho g u := by
  change inducedLinearMap _ _ _ _ _ = _
  rw [inducedLinearMap_mk]
  change Representation.ind phi rho g⁻¹ (Representation.IndV.mk phi rho 1 u) = _
  rw [Representation.ind_mk]
  simp

noncomputable def reparamInverseBase : Representation.IntertwiningMap rho
    ((Representation.ind (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom)).comp phi) where
  toLinearMap := Representation.IndV.mk (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom) 1
  isIntertwining' j := by
    apply LinearMap.ext
    intro u
    change Representation.IndV.mk (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom) 1
      (rho j u) = Representation.ind (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom)
      (phi j) (Representation.IndV.mk (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom) 1 u)
    rw [Representation.ind_mk]
    simpa using (ind_mk_inv_mul (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom)
      (e.symm j) 1 u).symm

noncomputable def inducedReparamInverse : Representation.IntertwiningMap
    (Representation.ind phi rho)
    (Representation.ind (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom)) :=
  inducedIntertwiner phi rho
    (Representation.ind (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom))
    (reparamInverseBase e phi rho)

@[simp] theorem inducedReparamInverse_mk (g : G) (u : V) :
    inducedReparamInverse e phi rho (Representation.IndV.mk phi rho g u) =
      Representation.IndV.mk (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom) g u := by
  change inducedLinearMap _ _ _ _ _ = _
  rw [inducedLinearMap_mk]
  change Representation.ind (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom) g⁻¹
    (Representation.IndV.mk (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom) 1 u) = _
  rw [Representation.ind_mk]
  simp

theorem inducedReparam_leftInverse : Function.LeftInverse
    (inducedReparamInverse e phi rho) (inducedReparam e phi rho) := by
  have he : (inducedReparamInverse e phi rho).toLinearMap.comp
      (inducedReparam e phi rho).toLinearMap = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext u
    change inducedReparamInverse e phi rho (inducedReparam e phi rho
      (Representation.IndV.mk (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom) g u)) = _
    rw [inducedReparam_mk, inducedReparamInverse_mk]
    rfl
  exact fun x => DFunLike.congr_fun he x

theorem inducedReparam_rightInverse : Function.RightInverse
    (inducedReparamInverse e phi rho) (inducedReparam e phi rho) := by
  have he : (inducedReparam e phi rho).toLinearMap.comp
      (inducedReparamInverse e phi rho).toLinearMap = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext u
    change inducedReparam e phi rho (inducedReparamInverse e phi rho
      (Representation.IndV.mk phi rho g u)) = _
    rw [inducedReparamInverse_mk, inducedReparam_mk]
    rfl
  exact fun x => DFunLike.congr_fun he x

theorem inducedReparam_bijective : Function.Bijective (inducedReparam e phi rho) :=
  ⟨(inducedReparam_leftInverse e phi rho).injective,
    (inducedReparam_rightInverse e phi rho).surjective⟩

noncomputable def inducedReparamEquiv :
    Representation.IndV (phi.comp e.toMonoidHom) (rho.comp e.toMonoidHom) ≃ₗ[R]
      Representation.IndV phi rho :=
  LinearEquiv.ofBijective (inducedReparam e phi rho).toLinearMap
    (inducedReparam_bijective e phi rho)
end
end HSTZ
#print axioms HSTZ.inducedReparam_mk
#print axioms HSTZ.inducedReparamInverse_mk
#print axioms HSTZ.inducedReparam_leftInverse
#print axioms HSTZ.inducedReparam_rightInverse
#print axioms HSTZ.inducedReparam_bijective
