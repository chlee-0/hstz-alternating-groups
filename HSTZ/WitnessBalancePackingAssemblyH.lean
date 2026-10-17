import HSTZ.WitnessBalancePackingAssemblyPhysical

/-! Source transport for the same H, and return from the ordinary induced assembly.
Builds on interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Private hom-equality consumers reuse the identity and induced reparametrizations.
K is larger than H; the full rest and both independent layers are kept. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))
local instance : AddCommGroup (witnessBalancePackingRestTensorSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup (witnessBalancePackingJointPairRestSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : Module ℂ (witnessBalancePackingJointPairRestSpace hk z) := TensorProduct.leftModule
local instance : AddCommGroup (witnessBalancePackingAssemblySpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ

private def homTransport {A : Type*} [Group A] (phi psi : A →* Equiv.Perm (Fin n))
    (he : phi=psi) (rho : Representation ℂ A (witnessBalancePackingJointPairRestSpace hk z)) :
    Representation.IntertwiningMap (Representation.ind (k:=ℂ) phi rho)
      (Representation.ind (k:=ℂ) psi rho) := by
  subst psi
  exact Representation.IntertwiningMap.id _
private theorem homTransport_bijective {A : Type*} [Group A]
    (phi psi : A →* Equiv.Perm (Fin n)) (he : phi=psi)
    (rho : Representation ℂ A (witnessBalancePackingJointPairRestSpace hk z)) :
    Function.Bijective (homTransport hk z phi psi he rho) := by
  subst psi
  exact ⟨Function.injective_id,fun x => ⟨x,rfl⟩⟩
private theorem homTransport_mk {A : Type*} [Group A]
    (phi psi : A →* Equiv.Perm (Fin n)) (he : phi=psi)
    (rho : Representation ℂ A (witnessBalancePackingJointPairRestSpace hk z))
    (g : Equiv.Perm (Fin n)) (v : witnessBalancePackingJointPairRestSpace hk z) :
    homTransport hk z phi psi he rho (Representation.IndV.mk (k:=ℂ) phi rho g v)=
      Representation.IndV.mk (k:=ℂ) psi rho g v := by
  subst psi
  rfl

private abbrev nativeHom (hd : delta≤1) :=
  (witnessBalanceGroup hk z).subtype.comp (witnessBalancePackingOriginalEquiv hk z hd).toMonoidHom
private theorem physicalHom (hd : delta≤1) :
    (witnessBalancePackingCoarserHom hk z hd).comp (witnessBalancePackingOriginalToCoarser hk z)=
      nativeHom hk z hd := by
  rw [witnessBalancePackingInductionPhysicalHom]
  rfl
private theorem nativeCancel (hd : delta≤1) :
    (nativeHom hk z hd).comp (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom=
      (witnessBalanceGroup hk z).subtype := by
  apply MonoidHom.ext
  intro h
  change ((witnessBalancePackingOriginalEquiv hk z hd)
    ((witnessBalancePackingOriginalEquiv hk z hd).symm h)).val=h.val
  exact congrArg (fun q : witnessBalanceGroup hk z => q.val)
    ((witnessBalancePackingOriginalEquiv hk z hd).apply_symm_apply h)

private def toNative (hd : delta≤1) :=
  homTransport hk z
    ((witnessBalancePackingCoarserHom hk z hd).comp (witnessBalancePackingOriginalToCoarser hk z))
    (nativeHom hk z hd) (physicalHom hk z hd) (witnessBalancePackingJointPairRestAction hk z)
private def nativeReparam (hd : delta≤1) : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (nativeHom hk z hd) (witnessBalancePackingJointPairRestAction hk z))
    (Representation.ind (k:=ℂ) ((nativeHom hk z hd).comp
      (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom)
      (witnessBalancePackingJointPairRestHAction hk z hd)) :=
  inducedReparamInverse (witnessBalancePackingOriginalEquiv hk z hd).symm
    (nativeHom hk z hd) (witnessBalancePackingJointPairRestAction hk z)
private def toH (hd : delta≤1) :=
  homTransport hk z
    ((nativeHom hk z hd).comp (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom)
    (witnessBalanceGroup hk z).subtype (nativeCancel hk z hd)
    (witnessBalancePackingJointPairRestHAction hk z hd)

private theorem toNative_bijective (hd : delta≤1) : Function.Bijective (toNative hk z hd) :=
  homTransport_bijective hk z
    ((witnessBalancePackingCoarserHom hk z hd).comp (witnessBalancePackingOriginalToCoarser hk z))
    (nativeHom hk z hd) (physicalHom hk z hd) (witnessBalancePackingJointPairRestAction hk z)
private theorem toH_bijective (hd : delta≤1) : Function.Bijective (toH hk z hd) :=
  homTransport_bijective hk z
    ((nativeHom hk z hd).comp (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom)
    (witnessBalanceGroup hk z).subtype (nativeCancel hk z hd)
    (witnessBalancePackingJointPairRestHAction hk z hd)
private theorem nativeReparam_bijective (hd : delta≤1) : Function.Bijective (nativeReparam hk z hd) :=
  ⟨(inducedReparam_rightInverse (witnessBalancePackingOriginalEquiv hk z hd).symm
      (nativeHom hk z hd) (witnessBalancePackingJointPairRestAction hk z)).injective,
   (inducedReparam_leftInverse (witnessBalancePackingOriginalEquiv hk z hd).symm
      (nativeHom hk z hd) (witnessBalancePackingJointPairRestAction hk z)).surjective⟩
private theorem toNative_mk (hd : delta≤1) (g : Equiv.Perm (Fin n))
    (v : witnessBalancePackingJointPairRestSpace hk z) :
    toNative hk z hd (Representation.IndV.mk (k:=ℂ)
      ((witnessBalancePackingCoarserHom hk z hd).comp (witnessBalancePackingOriginalToCoarser hk z))
      (witnessBalancePackingJointPairRestAction hk z) g v)=
    Representation.IndV.mk (k:=ℂ) (nativeHom hk z hd) (witnessBalancePackingJointPairRestAction hk z) g v :=
  homTransport_mk hk z _ _ (physicalHom hk z hd) (witnessBalancePackingJointPairRestAction hk z) g v
private theorem nativeReparam_mk (hd : delta≤1) (g : Equiv.Perm (Fin n))
    (v : witnessBalancePackingJointPairRestSpace hk z) :
    nativeReparam hk z hd (Representation.IndV.mk (k:=ℂ) (nativeHom hk z hd)
      (witnessBalancePackingJointPairRestAction hk z) g v)=
    Representation.IndV.mk (k:=ℂ) ((nativeHom hk z hd).comp
      (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom)
      (witnessBalancePackingJointPairRestHAction hk z hd) g v :=
  inducedReparamInverse_mk (witnessBalancePackingOriginalEquiv hk z hd).symm
    (nativeHom hk z hd) (witnessBalancePackingJointPairRestAction hk z) g v
private theorem toH_mk (hd : delta≤1) (g : Equiv.Perm (Fin n))
    (v : witnessBalancePackingJointPairRestSpace hk z) :
    toH hk z hd (Representation.IndV.mk (k:=ℂ) ((nativeHom hk z hd).comp
      (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom)
      (witnessBalancePackingJointPairRestHAction hk z hd) g v)=
    Representation.IndV.mk (k:=ℂ) (witnessBalanceGroup hk z).subtype
      (witnessBalancePackingJointPairRestHAction hk z hd) g v :=
  homTransport_mk hk z _ _ (nativeCancel hk z hd) (witnessBalancePackingJointPairRestHAction hk z hd) g v

/-- Source transport to ordinary induction from the same original H. -/
def witnessBalancePackingHSourceReturn (hd : delta≤1) : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
      (witnessBalancePackingOriginalToCoarser hk z)) (witnessBalancePackingJointPairRestAction hk z))
    (Representation.ind (k:=ℂ) (witnessBalanceGroup hk z).subtype
      (witnessBalancePackingJointPairRestHAction hk z hd)) :=
  (toH hk z hd).comp ((nativeReparam hk z hd).comp (toNative hk z hd))

theorem witnessBalancePackingHSourceReturn_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingHSourceReturn hk z hd) := by
  change Function.Bijective ((toH hk z hd) ∘ (nativeReparam hk z hd) ∘ (toNative hk z hd))
  exact (toH_bijective hk z hd).comp
    ((nativeReparam_bijective hk z hd).comp (toNative_bijective hk z hd))

theorem witnessBalancePackingHSourceReturn_mk (hd : delta≤1)
    (g : Equiv.Perm (Fin n)) (v : witnessBalancePackingJointPairRestSpace hk z) :
    witnessBalancePackingHSourceReturn hk z hd
      (Representation.IndV.mk (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
        (witnessBalancePackingOriginalToCoarser hk z)) (witnessBalancePackingJointPairRestAction hk z) g v)=
    Representation.IndV.mk (k:=ℂ) (witnessBalanceGroup hk z).subtype
      (witnessBalancePackingJointPairRestHAction hk z hd) g v := by
  change toH hk z hd (nativeReparam hk z hd (toNative hk z hd
    (Representation.IndV.mk (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
      (witnessBalancePackingOriginalToCoarser hk z)) (witnessBalancePackingJointPairRestAction hk z) g v))) = _
  rw [toNative_mk,nativeReparam_mk,toH_mk]

/-- The ordinary induced assembly, returned bijectively to the original H source. -/
def witnessBalancePackingAssemblyHReturn (hd : delta≤1) : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
      (witnessBalancePackingAssemblyAction hk z))
    (Representation.ind (k:=ℂ) (witnessBalanceGroup hk z).subtype
      (witnessBalancePackingJointPairRestHAction hk z hd)) :=
  (witnessBalancePackingHSourceReturn hk z hd).comp (witnessBalancePackingAssemblyDirectReturn hk z hd)

theorem witnessBalancePackingAssemblyHReturn_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingAssemblyHReturn hk z hd) :=
  (witnessBalancePackingHSourceReturn_bijective hk z hd).comp
    (witnessBalancePackingAssemblyDirectReturn_bijective hk z hd)

theorem witnessBalancePackingAssemblyHReturn_mk (hd : delta≤1)
    (g : Equiv.Perm (Fin n)) (h : witnessBalancePackingCoarserGroup hk z)
    (v : witnessBalancePackingJointPairRestSpace hk z) :
    witnessBalancePackingAssemblyHReturn hk z hd
      (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
        (witnessBalancePackingAssemblyAction hk z) g
        (witnessBalancePackingAssemblyReturn hk z
          (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
            (witnessBalancePackingJointPairRestAction hk z) h v)))=
    Representation.IndV.mk (k:=ℂ) (witnessBalanceGroup hk z).subtype
      (witnessBalancePackingJointPairRestHAction hk z hd) (witnessBalancePackingCoarserHom hk z hd h*g) v := by
  change witnessBalancePackingHSourceReturn hk z hd
    (witnessBalancePackingAssemblyDirectReturn hk z hd
      (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
        (witnessBalancePackingAssemblyAction hk z) g
        (witnessBalancePackingAssemblyReturn hk z
          (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
            (witnessBalancePackingJointPairRestAction hk z) h v)))) = _
  rw [witnessBalancePackingAssemblyDirectReturn_mk,witnessBalancePackingHSourceReturn_mk]
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingHSourceReturn
#print axioms HSTZ.witnessBalancePackingHSourceReturn_bijective
#print axioms HSTZ.witnessBalancePackingHSourceReturn_mk
#print axioms HSTZ.witnessBalancePackingAssemblyHReturn
#print axioms HSTZ.witnessBalancePackingAssemblyHReturn_bijective
#print axioms HSTZ.witnessBalancePackingAssemblyHReturn_mk
