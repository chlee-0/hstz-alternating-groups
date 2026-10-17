import HSTZ.IntertwiningCompat
import HSTZ.InducedTarget
import HSTZ.InducedReparam
import HSTZ.IndependentTensor
import HSTZ.PositionBlock
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Tactic.Group

/-! Generic ordered Young-subgroup induction with a Pi tensor source.

The sections `ProdFactor` and `Trans` are public versions over ℂ of the private
generic adapters in `WitnessBalancePackingFactorization` and
`WitnessBalancePackingTransitivity`, which use induction interfaces from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Everything here is independent of the witness: the tower
theorem turns a chain of one-step boundary injections into one injection into
induction from the ordered product of all local groups, with an explicit
position equivalence and a Pi tensor source. -/
namespace HSTZ
noncomputable section
open scoped TensorProduct

section Inverse
variable {G U V : Type*} [Group G] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V] {tau : Representation ℂ G U} {sigma : Representation ℂ G V}

/-- The inverse of a bijective intertwiner is an intertwiner. -/
def intertwiningInverse (F : Representation.IntertwiningMap tau sigma)
    (hF : Function.Bijective F) : Representation.IntertwiningMap sigma tau where
  toLinearMap := (LinearEquiv.ofBijective F.toLinearMap hF).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply hF.1
    change (LinearEquiv.ofBijective F.toLinearMap hF)
        ((LinearEquiv.ofBijective F.toLinearMap hF).symm (sigma g v)) =
      F (tau g ((LinearEquiv.ofBijective F.toLinearMap hF).symm v))
    rw [F.map_action, LinearEquiv.apply_symm_apply]
    exact congrArg (sigma g) (LinearEquiv.apply_symm_apply
      (LinearEquiv.ofBijective F.toLinearMap hF) v).symm

theorem intertwiningInverse_left (F : Representation.IntertwiningMap tau sigma)
    (hF : Function.Bijective F) (x : U) : intertwiningInverse F hF (F x) = x :=
  (LinearEquiv.ofBijective F.toLinearMap hF).symm_apply_apply x

theorem intertwiningInverse_right (F : Representation.IntertwiningMap tau sigma)
    (hF : Function.Bijective F) (y : V) : F (intertwiningInverse F hF y) = y :=
  (LinearEquiv.ofBijective F.toLinearMap hF).apply_symm_apply y

theorem intertwiningInverse_bijective (F : Representation.IntertwiningMap tau sigma)
    (hF : Function.Bijective F) : Function.Bijective (intertwiningInverse F hF) :=
  ⟨Function.LeftInverse.injective (g := F) (fun y => intertwiningInverse_right F hF y),
    Function.RightInverse.surjective (g := F) (fun x => intertwiningInverse_left F hF x)⟩

/-- Ordinary induction of a bijective intertwiner is bijective. -/
theorem inducedMap_bijective_of_bijective {H K : Type*} [Group H] [Group K]
    {tau : Representation ℂ H U} {sigma : Representation ℂ H V} (phi : H →* K)
    (F : Representation.IntertwiningMap tau sigma) (hF : Function.Bijective F) :
    Function.Bijective (inducedMap phi F) :=
  ⟨(inducedMap_leftInverse phi F (intertwiningInverse F hF)
      (intertwiningInverse_left F hF)).injective,
    (inducedMap_leftInverse phi (intertwiningInverse F hF) F
      (intertwiningInverse_right F hF)).surjective⟩
end Inverse

section Conj
variable {H H' G V V' : Type*} [Group H] [Group H'] [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (phi : H →* G) (phi' : H' →* G) (psi : H' ≃* H) (s : G)
  (rho : Representation ℂ H V) (rho' : Representation ℂ H' V') (T : V' ≃ₗ[ℂ] V)

/-- Base map for induction along a conjugated, reparametrized subgroup. -/
def inducedConjBase (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) : Representation.IntertwiningMap rho' ((Representation.ind phi rho).comp phi') where
  toLinearMap := (Representation.IndV.mk phi rho s⁻¹).comp T.toLinearMap
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    change Representation.IndV.mk phi rho s⁻¹ (T (rho' h v)) =
      Representation.ind phi rho (phi' h) (Representation.IndV.mk phi rho s⁻¹ (T v))
    rw [hT, Representation.ind_mk, ← ind_mk_inv_mul phi rho (psi h) s⁻¹ (T v), hphi,
      show s⁻¹ * (s * phi (psi h) * s⁻¹)⁻¹ = (phi (psi h))⁻¹ * s⁻¹ by group]

/-- Induction along `phi' = s (phi ∘ psi) s⁻¹` maps to induction along `phi`. -/
def inducedConj (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) :
    Representation.IntertwiningMap (Representation.ind phi' rho')
    (Representation.ind phi rho) :=
  inducedIntertwiner phi' rho' (Representation.ind phi rho)
    (inducedConjBase phi phi' psi s rho rho' T hphi hT)

theorem inducedConj_mk (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) (g : G) (v : V') :
    inducedConj phi phi' psi s rho rho' T hphi hT (Representation.IndV.mk phi' rho' g v) =
      Representation.IndV.mk phi rho (s⁻¹ * g) (T v) := by
  change inducedLinearMap _ _ _ _ _ = _
  rw [inducedLinearMap_mk]
  change Representation.ind phi rho g⁻¹ (Representation.IndV.mk phi rho s⁻¹ (T v)) = _
  rw [Representation.ind_mk, inv_inv]

theorem inducedConj_hphi_symm (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹) : ∀ h, phi h = s⁻¹ * phi' (psi.symm h) * s⁻¹⁻¹ := by
  intro h
  rw [hphi, MulEquiv.apply_symm_apply]
  group

theorem inducedConj_hT_symm (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) : ∀ h v, T.symm (rho h v) = rho' (psi.symm h) (T.symm v) := by
  intro h v
  apply T.injective
  rw [LinearEquiv.apply_symm_apply, hT, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The reverse conjugated induction map. -/
def inducedConjInv (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) : Representation.IntertwiningMap (Representation.ind phi rho)
    (Representation.ind phi' rho') :=
  inducedConj phi' phi psi.symm s⁻¹ rho' rho T.symm
    (inducedConj_hphi_symm phi phi' psi s hphi) (inducedConj_hT_symm psi rho rho' T hT)

theorem inducedConjInv_mk (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) (g : G) (v : V) :
    inducedConjInv phi phi' psi s rho rho' T hphi hT (Representation.IndV.mk phi rho g v) =
      Representation.IndV.mk phi' rho' (s * g) (T.symm v) := by
  change inducedConj phi' phi psi.symm s⁻¹ rho' rho T.symm _ _
    (Representation.IndV.mk phi rho g v) = _
  rw [inducedConj_mk, inv_inv]

theorem inducedConj_leftInverse (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) : Function.LeftInverse
    (inducedConjInv phi phi' psi s rho rho' T hphi hT)
    (inducedConj phi phi' psi s rho rho' T hphi hT) := by
  have he : (inducedConjInv phi phi' psi s rho rho' T hphi hT).toLinearMap.comp
      (inducedConj phi phi' psi s rho rho' T hphi hT).toLinearMap = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext v
    change inducedConjInv phi phi' psi s rho rho' T hphi hT
      (inducedConj phi phi' psi s rho rho' T hphi hT (Representation.IndV.mk phi' rho' g v)) = _
    rw [inducedConj_mk, inducedConjInv_mk, mul_inv_cancel_left, LinearEquiv.symm_apply_apply]
    rfl
  exact fun x => DFunLike.congr_fun he x

theorem inducedConj_rightInverse (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) : Function.RightInverse
    (inducedConjInv phi phi' psi s rho rho' T hphi hT)
    (inducedConj phi phi' psi s rho rho' T hphi hT) := by
  have he : (inducedConj phi phi' psi s rho rho' T hphi hT).toLinearMap.comp
      (inducedConjInv phi phi' psi s rho rho' T hphi hT).toLinearMap = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext v
    change inducedConj phi phi' psi s rho rho' T hphi hT
      (inducedConjInv phi phi' psi s rho rho' T hphi hT (Representation.IndV.mk phi rho g v)) = _
    rw [inducedConjInv_mk, inducedConj_mk, inv_mul_cancel_left, LinearEquiv.apply_symm_apply]
    rfl
  exact fun x => DFunLike.congr_fun he x

theorem inducedConj_bijective (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) : Function.Bijective (inducedConj phi phi' psi s rho rho' T hphi hT) :=
  ⟨(inducedConj_leftInverse phi phi' psi s rho rho' T hphi hT).injective,
    (inducedConj_rightInverse phi phi' psi s rho rho' T hphi hT).surjective⟩

theorem inducedConjInv_bijective (hphi : ∀ h, phi' h = s * phi (psi h) * s⁻¹)
    (hT : ∀ h v, T (rho' h v) = rho (psi h) (T v)) :
    Function.Bijective (inducedConjInv phi phi' psi s rho rho' T hphi hT) :=
  ⟨(inducedConj_rightInverse phi phi' psi s rho rho' T hphi hT).injective,
    (inducedConj_leftInverse phi phi' psi s rho rho' T hphi hT).surjective⟩
end Conj

section ProdFactor
variable {H G R V W : Type*} [Group H] [Group G] [Group R]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (phi : H →* G) (rho : Representation ℂ H V) (sigma : Representation ℂ R W)

private def pfBase : Representation.IntertwiningMap (independentTensor rho sigma)
    ((independentTensor (Representation.ind phi rho) sigma).comp
      (phi.prodMap (MonoidHom.id R))) where
  toLinearMap := TensorProduct.map (Representation.IndV.mk phi rho 1) LinearMap.id
  isIntertwining' hr := by
    apply LinearMap.ext
    intro q
    have he : (TensorProduct.map (Representation.IndV.mk phi rho 1) LinearMap.id).comp
        (independentTensor rho sigma hr) =
      ((independentTensor (Representation.ind phi rho) sigma).comp
        (phi.prodMap (MonoidHom.id R)) hr).comp
        (TensorProduct.map (Representation.IndV.mk phi rho 1) LinearMap.id) := by
      ext v w
      change Representation.IndV.mk phi rho 1 (rho hr.1 v) ⊗ₜ[ℂ] sigma hr.2 w =
        Representation.ind phi rho (phi hr.1)
          (Representation.IndV.mk phi rho 1 v) ⊗ₜ[ℂ] sigma hr.2 w
      rw [Representation.ind_mk]
      have hi := ind_mk_inv_mul phi rho hr.1 1 v
      simpa using congrArg (fun x => x ⊗ₜ[ℂ] sigma hr.2 w) hi.symm
    exact DFunLike.congr_fun he q

/-- Product induction `Ind_{phi × id}(rho ⊠ sigma) → Ind_phi(rho) ⊠ sigma`. -/
def inducedProdFactor : Representation.IntertwiningMap
    (Representation.ind (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma))
    (independentTensor (Representation.ind phi rho) sigma) :=
  inducedIntertwiner (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma)
    (independentTensor (Representation.ind phi rho) sigma) (pfBase phi rho sigma)

theorem inducedProdFactor_mk (g : G) (r : R) (v : V) (w : W) :
    inducedProdFactor phi rho sigma
      (Representation.IndV.mk (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma)
        (g,r) (v ⊗ₜ[ℂ] w)) =
    Representation.IndV.mk phi rho g v ⊗ₜ[ℂ] sigma r⁻¹ w := by
  change inducedLinearMap _ _ _ _ _ = _
  rw [inducedLinearMap_mk]
  change Representation.ind phi rho g⁻¹ (Representation.IndV.mk phi rho 1 v) ⊗ₜ[ℂ]
    sigma r⁻¹ w = _
  rw [Representation.ind_mk]
  simp

private def pfFirst : G →* G × R where
  toFun g := (g,1)
  map_one' := rfl
  map_mul' _ _ := by simp
private abbrev pfBackRep := (Representation.trivial ℂ G W).linHom
  ((Representation.ind (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma)).comp
    (pfFirst (R:=R)))

private def pfBackLinear : V →ₗ[ℂ] W →ₗ[ℂ]
    Representation.IndV (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) :=
  LinearMap.compr₂ (R:=ℂ) (A:=ℂ) (TensorProduct.mk ℂ V W)
    (Representation.IndV.mk (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) 1)

private def pfBackBase : Representation.IntertwiningMap rho
    ((pfBackRep phi rho sigma).comp phi) where
  toLinearMap := pfBackLinear phi rho sigma
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    ext w
    change Representation.IndV.mk (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) 1
        (rho h v ⊗ₜ[ℂ] w) =
      Representation.ind (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) (phi h,1)
        (Representation.IndV.mk (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) 1
          (v ⊗ₜ[ℂ] w))
    rw [Representation.ind_mk]
    have he := ind_mk_inv_mul (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma)
      (h,1) 1 (v ⊗ₜ[ℂ] w)
    simpa [independentTensor_tmul] using he.symm

private def pfBack : (Representation.IndV phi rho ⊗[ℂ] W) →ₗ[ℂ]
    Representation.IndV (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) :=
  TensorProduct.lift (inducedIntertwiner phi rho (pfBackRep phi rho sigma)
    (pfBackBase phi rho sigma)).toLinearMap

private theorem pfBack_mk (g : G) (v : V) (w : W) :
    pfBack phi rho sigma (Representation.IndV.mk phi rho g v ⊗ₜ[ℂ] w) =
    Representation.IndV.mk (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma)
      (g,1) (v ⊗ₜ[ℂ] w) := by
  change (inducedLinearMap phi rho (pfBackRep phi rho sigma) (pfBackBase phi rho sigma)
    (Representation.IndV.mk phi rho g v)) w = _
  rw [inducedLinearMap_mk]
  change Representation.ind (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) (g⁻¹,1)
    (Representation.IndV.mk (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) 1
      (v ⊗ₜ[ℂ] w)) = _
  rw [Representation.ind_mk]
  simp

theorem inducedProdFactor_bijective : Function.Bijective (inducedProdFactor phi rho sigma) := by
  have hl : (pfBack phi rho sigma).comp (inducedProdFactor phi rho sigma).toLinearMap =
      LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro gr
    ext v w
    change pfBack phi rho sigma (inducedProdFactor phi rho sigma
      (Representation.IndV.mk (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma)
        gr (v ⊗ₜ[ℂ] w))) = _
    rw [inducedProdFactor_mk, pfBack_mk]
    have hi := ind_mk_inv_mul (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma)
      (1,gr.2⁻¹) (gr.1,1) (v ⊗ₜ[ℂ] w)
    simpa [independentTensor_tmul] using hi.symm
  have hr : (inducedProdFactor phi rho sigma).toLinearMap.comp (pfBack phi rho sigma) =
      LinearMap.id := by
    apply TensorProduct.ext'
    intro u w
    have hh : ((inducedProdFactor phi rho sigma).toLinearMap.comp
        (pfBack phi rho sigma)).comp ((TensorProduct.mk ℂ _ W).flip w) =
      ((TensorProduct.mk ℂ _ W).flip w) := by
      apply Representation.IndV.hom_ext
      intro g
      ext v
      change inducedProdFactor phi rho sigma (pfBack phi rho sigma
        (Representation.IndV.mk phi rho g v ⊗ₜ[ℂ] w)) = _
      rw [pfBack_mk, inducedProdFactor_mk]
      simp
    exact DFunLike.congr_fun hh u
  have hleft : Function.LeftInverse (pfBack phi rho sigma) (inducedProdFactor phi rho sigma) :=
    fun x => DFunLike.congr_fun hl x
  have hright : Function.RightInverse (pfBack phi rho sigma) (inducedProdFactor phi rho sigma) :=
    fun x => DFunLike.congr_fun hr x
  exact ⟨hleft.injective, hright.surjective⟩
end ProdFactor

section Trans
variable {H K G V : Type*} [Group H] [Group K] [Group G]
  [AddCommGroup V] [Module ℂ V]
  (psi : H →* K) (phi : K →* G) (sigma : Representation ℂ H V)

private def trDirectBase : Representation.IntertwiningMap sigma
    ((Representation.ind (phi.comp psi) sigma).comp (phi.comp psi)) where
  toLinearMap := Representation.IndV.mk (phi.comp psi) sigma 1
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    change Representation.IndV.mk (phi.comp psi) sigma 1 (sigma h v) =
      Representation.ind (phi.comp psi) sigma (phi (psi h))
        (Representation.IndV.mk (phi.comp psi) sigma 1 v)
    rw [Representation.ind_mk]
    simpa using (ind_mk_inv_mul (phi.comp psi) sigma h 1 v).symm

private def trInner : Representation.IntertwiningMap (Representation.ind psi sigma)
    ((Representation.ind (phi.comp psi) sigma).comp phi) :=
  inducedIntertwiner psi sigma ((Representation.ind (phi.comp psi) sigma).comp phi)
    (trDirectBase psi phi sigma)

private theorem trInner_mk (h : K) (v : V) :
    trInner psi phi sigma (Representation.IndV.mk psi sigma h v) =
      Representation.IndV.mk (phi.comp psi) sigma (phi h) v := by
  change inducedLinearMap _ _ _ _ _ = _
  rw [inducedLinearMap_mk]
  change Representation.ind (phi.comp psi) sigma (phi h⁻¹)
    (Representation.IndV.mk (phi.comp psi) sigma 1 v) = _
  rw [Representation.ind_mk]
  simp

/-- Two-stage ordinary induction transitivity. -/
def inducedTransitivity : Representation.IntertwiningMap
    (Representation.ind phi (Representation.ind psi sigma))
    (Representation.ind (phi.comp psi) sigma) :=
  inducedIntertwiner phi (Representation.ind psi sigma)
    (Representation.ind (phi.comp psi) sigma) (trInner psi phi sigma)

theorem inducedTransitivity_mk (g : G) (h : K) (v : V) :
    inducedTransitivity psi phi sigma
      (Representation.IndV.mk phi (Representation.ind psi sigma) g
        (Representation.IndV.mk psi sigma h v)) =
    Representation.IndV.mk (phi.comp psi) sigma (phi h * g) v := by
  change inducedLinearMap _ _ _ _ _ = _
  rw [inducedLinearMap_mk, trInner_mk, Representation.ind_mk]
  simp

private def trStageBase : Representation.IntertwiningMap sigma
    ((Representation.ind phi (Representation.ind psi sigma)).comp (phi.comp psi)) where
  toLinearMap := (Representation.IndV.mk phi (Representation.ind psi sigma) 1).comp
    (Representation.IndV.mk psi sigma 1)
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    change Representation.IndV.mk phi (Representation.ind psi sigma) 1
      (Representation.IndV.mk psi sigma 1 (sigma h v)) =
      Representation.ind phi (Representation.ind psi sigma) (phi (psi h))
        (Representation.IndV.mk phi (Representation.ind psi sigma) 1
          (Representation.IndV.mk psi sigma 1 v))
    rw [Representation.ind_mk]
    have he := ind_mk_inv_mul phi (Representation.ind psi sigma) (psi h) 1
      (Representation.IndV.mk psi sigma 1 v)
    rw [mul_one] at he
    simp only [one_mul]
    rw [he, Representation.ind_mk]
    have hi := ind_mk_inv_mul psi sigma h 1 v
    simpa using congrArg (Representation.IndV.mk phi (Representation.ind psi sigma) 1) hi.symm

private def trStageBack : Representation.IntertwiningMap
    (Representation.ind (phi.comp psi) sigma)
    (Representation.ind phi (Representation.ind psi sigma)) :=
  inducedIntertwiner (phi.comp psi) sigma
    (Representation.ind phi (Representation.ind psi sigma)) (trStageBase psi phi sigma)

private theorem trStageBack_mk (g : G) (v : V) :
    trStageBack psi phi sigma (Representation.IndV.mk (phi.comp psi) sigma g v) =
      Representation.IndV.mk phi (Representation.ind psi sigma) g
        (Representation.IndV.mk psi sigma 1 v) := by
  change inducedLinearMap _ _ _ _ _ = _
  rw [inducedLinearMap_mk]
  change Representation.ind phi (Representation.ind psi sigma) g⁻¹
    (Representation.IndV.mk phi (Representation.ind psi sigma) 1
      (Representation.IndV.mk psi sigma 1 v)) = _
  rw [Representation.ind_mk]
  simp

theorem inducedTransitivity_bijective : Function.Bijective (inducedTransitivity psi phi sigma) := by
  have hl : (trStageBack psi phi sigma).toLinearMap.comp
      (inducedTransitivity psi phi sigma).toLinearMap = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    apply Representation.IndV.hom_ext
    intro h
    ext v
    change trStageBack psi phi sigma (inducedTransitivity psi phi sigma
      (Representation.IndV.mk phi (Representation.ind psi sigma) g
        (Representation.IndV.mk psi sigma h v))) = _
    rw [inducedTransitivity_mk, trStageBack_mk]
    have he := ind_mk_inv_mul phi (Representation.ind psi sigma) h⁻¹ g
      (Representation.IndV.mk psi sigma 1 v)
    simpa [Representation.ind_mk] using he
  have hr : (inducedTransitivity psi phi sigma).toLinearMap.comp
      (trStageBack psi phi sigma).toLinearMap = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext v
    change inducedTransitivity psi phi sigma (trStageBack psi phi sigma
      (Representation.IndV.mk (phi.comp psi) sigma g v)) = _
    rw [trStageBack_mk, inducedTransitivity_mk]
    simp
  have hleft : Function.LeftInverse (trStageBack psi phi sigma) (inducedTransitivity psi phi sigma) :=
    fun x => DFunLike.congr_fun hl x
  have hright : Function.RightInverse (trStageBack psi phi sigma)
      (inducedTransitivity psi phi sigma) := fun x => DFunLike.congr_fun hr x
  exact ⟨hleft.injective, hright.surjective⟩
end Trans

section PiRep
variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  (rho : ∀ i, Representation ℂ (G i) (M i))

/-- Independent action of a product of groups on the Pi tensor of their modules. -/
def piTensorRep : Representation ℂ (∀ i, G i) (⨂[ℂ] i, M i) where
  toFun g := PiTensorProduct.map fun i => rho i (g i)
  map_one' := by
    change PiTensorProduct.map (fun i => rho i 1) = 1
    simp only [map_one]
    exact PiTensorProduct.map_one
  map_mul' g h := by
    change PiTensorProduct.map (fun i => rho i (g i * h i)) = _
    simp only [map_mul]
    exact PiTensorProduct.map_mul _ _

theorem piTensorRep_tprod (g : ∀ i, G i) (f : ∀ i, M i) :
    piTensorRep rho g (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ fun i => rho i (g i) (f i) :=
  PiTensorProduct.map_tprod _ _
end PiRep

section TowerIndex
variable {m : ℕ} (d : Fin m → ℕ)

/-- Blocks strictly before the ordinal `j`. -/
abbrev TowerIdx (m j : ℕ) := {i : Fin m // i.val < j}

/-- The product of all local permutation groups strictly before `j`. -/
abbrev towerGroup (j : ℕ) := ∀ v : TowerIdx m j, Equiv.Perm (Fin (d v.val))

def towerIdxSplit (i : Fin m) : TowerIdx m (i.val+1) ≃ TowerIdx m i.val ⊕ Unit where
  toFun v := if h : v.val.val < i.val then .inl ⟨v.val, h⟩ else .inr ()
  invFun := Sum.elim (fun v => ⟨v.val, Nat.lt_succ_of_lt v.property⟩)
    (fun _ => ⟨i, Nat.lt_succ_self _⟩)
  left_inv v := by
    by_cases h : v.val.val < i.val
    · simp only [dif_pos h]
      try rfl
    · simp only [dif_neg h]
      exact Subtype.ext (Fin.ext (show i.val = v.val.val by have := v.property; omega))
  right_inv x := by
    rcases x with v | u
    · exact dif_pos v.property
    · exact dif_neg (lt_irrefl _)

def towerSigmaSplit (i : Fin m) :
    (Σ v : TowerIdx m (i.val+1), Fin (d v.val)) ≃
      (Σ v : TowerIdx m i.val, Fin (d v.val)) ⊕ Fin (d i) where
  toFun x := if h : x.1.val.val < i.val then .inl ⟨⟨x.1.val, h⟩, x.2⟩
    else .inr (Fin.cast (congrArg d (Fin.ext (by have := x.1.property; omega))) x.2)
  invFun := Sum.elim (fun y => ⟨⟨y.1.val, Nat.lt_succ_of_lt y.1.property⟩, y.2⟩)
    (fun y => ⟨⟨i, Nat.lt_succ_self _⟩, y⟩)
  left_inv x := by
    rcases x with ⟨⟨v, hv⟩, y⟩
    by_cases h : v.val < i.val
    · simp only [dif_pos h]
      try rfl
    · have he : v = i := Fin.ext (by omega)
      subst he
      simp only [dif_neg h]
      try rfl
  right_inv y := by
    rcases y with ⟨⟨v, hv⟩, y⟩ | y
    · exact dif_pos hv
    · exact dif_neg (lt_irrefl _)

def towerGroupSplit (i : Fin m) :
    towerGroup d (i.val+1) ≃* towerGroup d i.val × Equiv.Perm (Fin (d i)) where
  toFun g := (fun v => g ⟨v.val, Nat.lt_succ_of_lt v.property⟩, g ⟨i, Nat.lt_succ_self _⟩)
  invFun gh v := if h : v.val.val < i.val then gh.1 ⟨v.val, h⟩ else
    (finCongr (congrArg d (Fin.ext (show i.val = v.val.val by
      have := v.property; omega)))).permCongr gh.2
  left_inv g := by
    funext w
    rcases w with ⟨v, hv⟩
    by_cases h : v.val < i.val
    · exact dif_pos h
    · have he : v = i := Fin.ext (by omega)
      subst he
      exact (dif_neg h).trans (Equiv.ext fun x => rfl)
  right_inv gh := by
    rcases gh with ⟨g, h⟩
    exact Prod.ext (funext fun v => dif_pos v.property)
      ((dif_neg (lt_irrefl _)).trans (Equiv.ext fun x => rfl))
  map_mul' _ _ := rfl

theorem towerGroupSplit_apply (i : Fin m) (g : towerGroup d (i.val+1)) :
    towerGroupSplit d i g =
      (fun v : TowerIdx m i.val => g ⟨v.val, Nat.lt_succ_of_lt v.property⟩,
        g ⟨i, Nat.lt_succ_self _⟩) := rfl

theorem towerSigmaSplit_conj (i : Fin m) (g : towerGroup d (i.val+1))
    (w : (Σ v : TowerIdx m i.val, Fin (d v.val)) ⊕ Fin (d i)) :
    towerSigmaSplit d i (Equiv.sigmaCongrRight g ((towerSigmaSplit d i).symm w)) =
      Sum.map (Equiv.sigmaCongrRight (towerGroupSplit d i g).1) (towerGroupSplit d i g).2 w := by
  rcases w with ⟨⟨v, hv⟩, x⟩ | x
  · first
    | exact dif_pos hv
    | simp [towerSigmaSplit, towerGroupSplit, hv]
  · first
    | exact dif_neg (lt_irrefl _)
    | simp [towerSigmaSplit, towerGroupSplit]

theorem towerIdx_zero_false (v : TowerIdx m (0 : Fin (m+1)).val) : False := by
  have h := v.property
  simp at h

end TowerIndex

section Tower
variable {m : ℕ} (c : Fin (m+1) → ℕ) (d : Fin m → ℕ)
  (hc : ∀ i : Fin m, c i.succ = c i.castSucc + d i) (h0 : c 0 = 0)

/-- The adjacent-boundary cut. -/
def towerCut (i : Fin m) : Fin (c i.succ) ≃ Fin (c i.castSucc) ⊕ Fin (d i) :=
  (finCongr (hc i)).trans finSumFinEquiv.symm

private def towerPosZero : Fin (c 0) ≃ Σ v : TowerIdx m (0 : Fin (m+1)).val, Fin (d v.val) :=
  (finCongr h0).trans
    { toFun := fun x => Fin.elim0 x
      invFun := fun y => (towerIdx_zero_false y.1).elim
      left_inv := fun x => Fin.elim0 x
      right_inv := fun y => (towerIdx_zero_false y.1).elim }

def towerPosStep (i : Fin m) (e : Fin (c i.castSucc) ≃ Σ v : TowerIdx m i.val, Fin (d v.val)) :
    Fin (c i.succ) ≃ Σ v : TowerIdx m (i.val+1), Fin (d v.val) :=
  (towerCut c d hc i).trans ((Equiv.sumCongr e (Equiv.refl _)).trans (towerSigmaSplit d i).symm)

/-- Explicit positions of the ordered block decomposition at every boundary. -/
def towerPos : ∀ j : Fin (m+1), Fin (c j) ≃ Σ v : TowerIdx m j.val, Fin (d v.val) :=
  Fin.induction (motive := fun j => Fin (c j) ≃ Σ v : TowerIdx m j.val, Fin (d v.val))
    (towerPosZero c d h0) (fun i e => towerPosStep c d hc i e)

theorem towerPos_succ (i : Fin m) :
    towerPos c d hc h0 i.succ = towerPosStep c d hc i (towerPos c d hc h0 i.castSucc) := by
  first
  | rfl
  | simp only [towerPos, Fin.induction_succ]

/-- The ordered block product acting on its positions. -/
def towerHom (j : Fin (m+1)) : towerGroup d j.val →* Equiv.Perm (Fin (c j)) :=
  (towerPos c d hc h0 j).symm.permCongrHom.toMonoidHom.comp
    (Equiv.Perm.sigmaCongrRightHom fun v : TowerIdx m j.val => Fin (d v.val))

theorem towerHom_apply (j : Fin (m+1)) (g : towerGroup d j.val) (x : Fin (c j)) :
    towerHom c d hc h0 j g x =
      (towerPos c d hc h0 j).symm (Equiv.sigmaCongrRight g (towerPos c d hc h0 j x)) := rfl

/-- The next ordered block hom is the same cut of the previous hom times the new block. -/
theorem towerHom_succ (i : Fin m) (g : towerGroup d (i.val+1)) :
    towerHom c d hc h0 i.succ g = sumPermHom (towerCut c d hc i)
      (towerHom c d hc h0 i.castSucc (towerGroupSplit d i g).1, (towerGroupSplit d i g).2) := by
  apply Equiv.ext
  intro x
  rw [towerHom_apply, towerPos_succ]
  change (towerCut c d hc i).symm (Equiv.sumCongr (towerPos c d hc h0 i.castSucc).symm
      (Equiv.refl _) (towerSigmaSplit d i (Equiv.sigmaCongrRight g ((towerSigmaSplit d i).symm
        (Equiv.sumCongr (towerPos c d hc h0 i.castSucc) (Equiv.refl _)
          (towerCut c d hc i x)))))) =
    (towerCut c d hc i).symm (Equiv.sumCongr
      (towerHom c d hc h0 i.castSucc (towerGroupSplit d i g).1) (towerGroupSplit d i g).2
        (towerCut c d hc i x))
  rw [towerSigmaSplit_conj]
  generalize towerCut c d hc i x = y
  rcases y with y | y <;> rfl

variable {Wsp : Fin m → Type*} [∀ i, AddCommGroup (Wsp i)] [∀ i, Module ℂ (Wsp i)]
  (W : ∀ i, Representation ℂ (Equiv.Perm (Fin (d i))) (Wsp i))

/-- Pi tensor of all local modules strictly before `j`. -/
abbrev towerSpace (j : ℕ) := ⨂[ℂ] v : TowerIdx m j, Wsp v.val

/-- Independent action of the ordered block product on its Pi tensor source. -/
def towerRep (j : ℕ) : Representation ℂ (towerGroup d j) (towerSpace (Wsp := Wsp) j) :=
  piTensorRep (fun v : TowerIdx m j => W v.val)

def towerSpaceSplit (i : Fin m) :
    towerSpace (Wsp := Wsp) (i.val+1) ≃ₗ[ℂ] towerSpace (Wsp := Wsp) i.val ⊗[ℂ] Wsp i :=
  (PiTensorProduct.reindex ℂ (fun v : TowerIdx m (i.val+1) => Wsp v.val) (towerIdxSplit i)).trans
    ((PiTensorProduct.tmulEquivDep ℂ (fun x => Wsp ((towerIdxSplit i).symm x).val)).symm.trans
      (TensorProduct.congr (LinearEquiv.refl ℂ _)
        (PiTensorProduct.subsingletonEquiv (R := ℂ)
          (s := fun u : Unit => Wsp ((towerIdxSplit i).symm (Sum.inr u)).val) ())))

theorem towerSpaceSplit_tprod (i : Fin m) (F : ∀ v : TowerIdx m (i.val+1), Wsp v.val) :
    towerSpaceSplit i (PiTensorProduct.tprod ℂ F) =
      PiTensorProduct.tprod ℂ (fun v : TowerIdx m i.val => F ⟨v.val, Nat.lt_succ_of_lt v.property⟩)
        ⊗ₜ[ℂ] F ⟨i, Nat.lt_succ_self _⟩ := by
  erw [towerSpaceSplit, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
    TensorProduct.congr_tmul]
  congr 1
  exact PiTensorProduct.subsingletonEquiv_apply_tprod (R := ℂ) () _

theorem towerSpaceSplit_conj (i : Fin m) (g : towerGroup d (i.val+1))
    (x : towerSpace (Wsp := Wsp) (i.val+1)) :
    towerSpaceSplit i (towerRep d W (i.val+1) g x) =
      independentTensor (towerRep d W i.val) (W i) (towerGroupSplit d i g)
        (towerSpaceSplit i x) := by
  have he : (towerSpaceSplit (Wsp := Wsp) i).toLinearMap ∘ₗ (towerRep d W (i.val+1) g) =
      (independentTensor (towerRep d W i.val) (W i) (towerGroupSplit d i g)) ∘ₗ
        (towerSpaceSplit (Wsp := Wsp) i).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    change towerSpaceSplit i (towerRep d W (i.val+1) g (PiTensorProduct.tprod ℂ f)) =
      independentTensor (towerRep d W i.val) (W i) (towerGroupSplit d i g)
        (towerSpaceSplit i (PiTensorProduct.tprod ℂ f))
    rw [towerRep, towerRep, piTensorRep_tprod, towerSpaceSplit_tprod, towerSpaceSplit_tprod,
      towerGroupSplit_apply, independentTensor_tmul, piTensorRep_tprod]
  exact DFunLike.congr_fun he x

/-- Stage piece 1: factor the previous induced Pi tower out of the tensor. -/
def towerStageFactor (i : Fin m) : Representation.IntertwiningMap
    (Representation.ind (sumPermHom (towerCut c d hc i))
      (independentTensor (Representation.ind (towerHom c d hc h0 i.castSucc) (towerRep d W i.val))
        (W i)))
    (Representation.ind (sumPermHom (towerCut c d hc i))
      (Representation.ind ((towerHom c d hc h0 i.castSucc).prodMap
          (MonoidHom.id (Equiv.Perm (Fin (d i)))))
        (independentTensor (towerRep d W i.val) (W i)))) :=
  inducedMap (sumPermHom (towerCut c d hc i))
    (intertwiningInverse (inducedProdFactor (towerHom c d hc h0 i.castSucc) (towerRep d W i.val) (W i))
      (inducedProdFactor_bijective (towerHom c d hc h0 i.castSucc) (towerRep d W i.val) (W i)))

theorem towerStageFactor_bijective (i : Fin m) :
    Function.Bijective (towerStageFactor c d hc h0 W i) :=
  inducedMap_bijective_of_bijective _ _ (intertwiningInverse_bijective _ _)

/-- Stage piece 2: two-stage induction transitivity through the same cut. -/
def towerStageTrans (i : Fin m) : Representation.IntertwiningMap
    (Representation.ind (sumPermHom (towerCut c d hc i))
      (Representation.ind ((towerHom c d hc h0 i.castSucc).prodMap
          (MonoidHom.id (Equiv.Perm (Fin (d i)))))
        (independentTensor (towerRep d W i.val) (W i))))
    (Representation.ind ((sumPermHom (towerCut c d hc i)).comp
        ((towerHom c d hc h0 i.castSucc).prodMap (MonoidHom.id (Equiv.Perm (Fin (d i))))))
      (independentTensor (towerRep d W i.val) (W i))) :=
  inducedTransitivity ((towerHom c d hc h0 i.castSucc).prodMap
      (MonoidHom.id (Equiv.Perm (Fin (d i)))))
    (sumPermHom (towerCut c d hc i)) (independentTensor (towerRep d W i.val) (W i))

theorem towerStageTrans_bijective (i : Fin m) :
    Function.Bijective (towerStageTrans c d hc h0 W i) :=
  inducedTransitivity_bijective _ _ _

theorem towerStage_hphi (i : Fin m) (g : towerGroup d (i.val+1)) :
    towerHom c d hc h0 i.succ g = 1 * ((sumPermHom (towerCut c d hc i)).comp
        ((towerHom c d hc h0 i.castSucc).prodMap (MonoidHom.id (Equiv.Perm (Fin (d i))))))
      (towerGroupSplit d i g) * 1⁻¹ := by
  rw [one_mul, inv_one, mul_one]
  exact towerHom_succ c d hc h0 i g

/-- Stage piece 3: the same next ordered block hom, via the explicit group/module split. -/
def towerStageConj (i : Fin m) : Representation.IntertwiningMap
    (Representation.ind ((sumPermHom (towerCut c d hc i)).comp
        ((towerHom c d hc h0 i.castSucc).prodMap (MonoidHom.id (Equiv.Perm (Fin (d i))))))
      (independentTensor (towerRep d W i.val) (W i)))
    (Representation.ind (towerHom c d hc h0 i.succ) (towerRep d W (i.val+1))) :=
  inducedConjInv ((sumPermHom (towerCut c d hc i)).comp
      ((towerHom c d hc h0 i.castSucc).prodMap (MonoidHom.id (Equiv.Perm (Fin (d i))))))
    (towerHom c d hc h0 i.succ) (towerGroupSplit d i) 1
    (independentTensor (towerRep d W i.val) (W i)) (towerRep d W (i.val+1))
    (towerSpaceSplit i) (towerStage_hphi c d hc h0 i) (towerSpaceSplit_conj d W i)

theorem towerStageConj_bijective (i : Fin m) :
    Function.Bijective (towerStageConj c d hc h0 W i) :=
  inducedConjInv_bijective _ _ _ _ _ _ _ _ _

/-- One ordered stage: induction of the previous Pi-tower tensor the next local
module, through the same boundary cut, is the next Pi-tower induction. -/
def towerStage (i : Fin m) : Representation.IntertwiningMap
    (Representation.ind (sumPermHom (towerCut c d hc i))
      (independentTensor (Representation.ind (towerHom c d hc h0 i.castSucc) (towerRep d W i.val))
        (W i)))
    (Representation.ind (towerHom c d hc h0 i.succ) (towerRep d W (i.val+1))) :=
  (towerStageConj c d hc h0 W i).comp
    ((towerStageTrans c d hc h0 W i).comp (towerStageFactor c d hc h0 W i))

theorem towerStage_bijective (i : Fin m) : Function.Bijective (towerStage c d hc h0 W i) :=
  (towerStageConj_bijective c d hc h0 W i).comp
    ((towerStageTrans_bijective c d hc h0 W i).comp (towerStageFactor_bijective c d hc h0 W i))

theorem towerBase {V0 : Type*} [AddCommGroup V0] [Module ℂ V0]
    (rho0 : Representation ℂ (Equiv.Perm (Fin (c 0))) V0) [Representation.IsIrreducible rho0]
    (v0 : V0) (hv0 : v0 ≠ 0) :
    ∃ E : Representation.IntertwiningMap rho0
      (Representation.ind (towerHom c d hc h0 0) (towerRep d W (0 : Fin (m+1)).val)),
      Function.Injective E := by
  haveI : IsEmpty (TowerIdx m (0 : Fin (m+1)).val) := ⟨towerIdx_zero_false⟩
  let j : Representation.IntertwiningMap (towerRep d W (0 : Fin (m+1)).val)
      (rho0.comp (towerHom c d hc h0 0)) :=
    { toLinearMap := LinearMap.smulRight
        (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun v : TowerIdx m (0 : Fin (m+1)).val => Wsp v.val) (TowerIdx m (0 : Fin (m+1)).val)).toLinearMap v0
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        have hg : g = 1 := funext fun v => (IsEmpty.false v).elim
        subst hg
        rw [map_one, map_one]
        rfl }
  have hj : j ≠ 0 := by
    intro h
    apply hv0
    have hx := congrArg (fun F : Representation.IntertwiningMap (towerRep d W (0 : Fin (m+1)).val)
        (rho0.comp (towerHom c d hc h0 0)) =>
      F ((PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun v : TowerIdx m (0 : Fin (m+1)).val => Wsp v.val) (TowerIdx m (0 : Fin (m+1)).val)).symm 1)) h
    change (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun v : TowerIdx m (0 : Fin (m+1)).val => Wsp v.val) (TowerIdx m (0 : Fin (m+1)).val)
      ((PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun v : TowerIdx m (0 : Fin (m+1)).val => Wsp v.val) (TowerIdx m (0 : Fin (m+1)).val)).symm 1)) • v0 = 0 at hx
    rwa [LinearEquiv.apply_symm_apply, one_smul] at hx
  letI : NeZero (Nat.card (Equiv.Perm (Fin (c 0))) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (Equiv.Perm (Fin (c 0)))).ne'⟩
  exact induced_target_embedding_of_nonzero (towerHom c d hc h0 0)
    (towerRep d W (0 : Fin (m+1)).val) rho0 j hj

/-- Ordered tower theorem. Chained one-step boundary injections give an injection
of the final target into induction from the ordered product of all local groups,
acting on their block positions, of the Pi tensor of all local modules. -/
theorem tower_embedding
    {Vsp : Fin (m+1) → Type*} [∀ j, AddCommGroup (Vsp j)] [∀ j, Module ℂ (Vsp j)]
    (V : ∀ j, Representation ℂ (Equiv.Perm (Fin (c j))) (Vsp j))
    [Representation.IsIrreducible (V 0)] (v0 : Vsp 0) (hv0 : v0 ≠ 0)
    (hstep : ∀ i : Fin m, ∃ E : Representation.IntertwiningMap (V i.succ)
      (Representation.ind (sumPermHom (towerCut c d hc i))
        (independentTensor (V i.castSucc) (W i))), Function.Injective E) :
    ∀ j : Fin (m+1), ∃ E : Representation.IntertwiningMap (V j)
      (Representation.ind (towerHom c d hc h0 j) (towerRep d W j.val)),
      Function.Injective E := by
  intro j
  induction j using Fin.induction with
  | zero => exact towerBase c d hc h0 W (V 0) v0 hv0
  | succ i ih =>
    obtain ⟨J, hJ⟩ := ih
    obtain ⟨E, hE⟩ := hstep i
    letI : NeZero (Nat.card (Equiv.Perm (Fin (c i.castSucc)) × Equiv.Perm (Fin (d i))) : ℂ) :=
      ⟨by exact_mod_cast (Nat.card_pos :
        0 < Nat.card (Equiv.Perm (Fin (c i.castSucc)) × Equiv.Perm (Fin (d i)))).ne'⟩
    let M := independentTensorMap J (Representation.IntertwiningMap.id (W i))
    have hM : Function.Injective M := independentTensorMap_injective J
      (Representation.IntertwiningMap.id (W i)) hJ (fun _ _ he => he)
    let L := inducedMap (sumPermHom (towerCut c d hc i)) M
    have hL : Function.Injective L := inducedMap_injective (sumPermHom (towerCut c d hc i)) M hM
    exact ⟨(towerStage c d hc h0 W i).comp (L.comp E),
      (towerStage_bijective c d hc h0 W i).1.comp (hL.comp hE)⟩
end Tower

end
end HSTZ

#print axioms HSTZ.inducedConj_bijective
#print axioms HSTZ.inducedConjInv_bijective
#print axioms HSTZ.inducedProdFactor_bijective
#print axioms HSTZ.inducedTransitivity_bijective
#print axioms HSTZ.towerHom_succ
#print axioms HSTZ.towerSpaceSplit_tprod
#print axioms HSTZ.towerSpaceSplit_conj
#print axioms HSTZ.towerStage_bijective
#print axioms HSTZ.tower_embedding
