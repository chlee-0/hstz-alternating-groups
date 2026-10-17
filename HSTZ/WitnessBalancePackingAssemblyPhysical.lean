import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePackingAssemblyReturn

/-! The inverse of the assembly return map as an intertwiner, and ordinary
induction of the assembly to the physical positions, built from that bijection and
induction transitivity. The group K remains larger than H. Target support is not
addressed here. Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
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

private def assemblyEquiv :
    Representation.IndV (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
      (witnessBalancePackingJointPairRestAction hk z) ≃ₗ[ℂ]
    witnessBalancePackingAssemblySpace hk z :=
  LinearEquiv.ofBijective (witnessBalancePackingAssemblyReturn hk z).toLinearMap
    (witnessBalancePackingAssemblyReturn_bijective hk z)

/-- The inverse of the assembly return map, as an intertwiner for the K actions
rather than merely a linear inverse. -/
def witnessBalancePackingAssemblyInverse : Representation.IntertwiningMap
    (witnessBalancePackingAssemblyAction hk z)
    (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
      (witnessBalancePackingJointPairRestAction hk z)) where
  toLinearMap := (assemblyEquiv hk z).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    apply (witnessBalancePackingAssemblyReturn_bijective hk z).1
    change assemblyEquiv hk z ((assemblyEquiv hk z).symm
        (witnessBalancePackingAssemblyAction hk z g q)) =
      witnessBalancePackingAssemblyReturn hk z
        (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
          (witnessBalancePackingJointPairRestAction hk z) g ((assemblyEquiv hk z).symm q))
    calc
      _ = witnessBalancePackingAssemblyAction hk z g q :=
        (assemblyEquiv hk z).apply_symm_apply _
      _ = witnessBalancePackingAssemblyAction hk z g
        (witnessBalancePackingAssemblyReturn hk z ((assemblyEquiv hk z).symm q)) :=
        congrArg (fun x => witnessBalancePackingAssemblyAction hk z g x)
          ((assemblyEquiv hk z).apply_symm_apply q).symm
      _ = _ := ((witnessBalancePackingAssemblyReturn hk z).map_action g
        ((assemblyEquiv hk z).symm q)).symm

theorem witnessBalancePackingAssemblyInverse_return
    (q : Representation.IndV (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
      (witnessBalancePackingJointPairRestAction hk z)) :
    witnessBalancePackingAssemblyInverse hk z (witnessBalancePackingAssemblyReturn hk z q)=q :=
  (assemblyEquiv hk z).symm_apply_apply q

theorem witnessBalancePackingAssemblyReturn_inverse (q : witnessBalancePackingAssemblySpace hk z) :
    witnessBalancePackingAssemblyReturn hk z (witnessBalancePackingAssemblyInverse hk z q)=q :=
  (assemblyEquiv hk z).apply_symm_apply q

/-- The induced inverse; both inverse identities pass to the induced modules. -/
def witnessBalancePackingInducedAssemblyInverse (hd : delta≤1) : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
      (witnessBalancePackingAssemblyAction hk z))
    (Representation.ind (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
      (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
        (witnessBalancePackingJointPairRestAction hk z))) :=
  inducedMap (witnessBalancePackingCoarserHom hk z hd) (witnessBalancePackingAssemblyInverse hk z)

theorem witnessBalancePackingInducedAssemblyInverse_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingInducedAssemblyInverse hk z hd) := by
  let phi := witnessBalancePackingCoarserHom hk z hd
  have hleft := inducedMap_leftInverse phi (witnessBalancePackingAssemblyInverse hk z)
    (witnessBalancePackingAssemblyReturn hk z) (witnessBalancePackingAssemblyReturn_inverse hk z)
  have hright := inducedMap_leftInverse phi (witnessBalancePackingAssemblyReturn hk z)
    (witnessBalancePackingAssemblyInverse hk z) (witnessBalancePackingAssemblyInverse_return hk z)
  exact ⟨hleft.injective,hright.surjective⟩

theorem witnessBalancePackingInducedAssemblyInverse_mk (hd : delta≤1)
    (g : Equiv.Perm (Fin n)) (q : witnessBalancePackingAssemblySpace hk z) :
    witnessBalancePackingInducedAssemblyInverse hk z hd
      (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
        (witnessBalancePackingAssemblyAction hk z) g q)=
    Representation.IndV.mk (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
      (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
        (witnessBalancePackingJointPairRestAction hk z)) g
      (witnessBalancePackingAssemblyInverse hk z q) := inducedMap_mk _ _ g q

private def directLinear (hd : delta≤1) :
    Representation.IndV (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
      (witnessBalancePackingAssemblyAction hk z) →ₗ[ℂ]
    Representation.IndV (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
      (witnessBalancePackingOriginalToCoarser hk z)) (witnessBalancePackingJointPairRestAction hk z) :=
  (witnessBalancePackingInductionTransitivity hk z hd).toLinearMap.comp
    (witnessBalancePackingInducedAssemblyInverse hk z hd).toLinearMap

/-- The induced assembly, identified with ordinary induction to the physical
positions from the joint-pair-rest source over all labels. -/
def witnessBalancePackingAssemblyDirectReturn (hd : delta≤1) : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
      (witnessBalancePackingAssemblyAction hk z))
    (Representation.ind (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
      (witnessBalancePackingOriginalToCoarser hk z)) (witnessBalancePackingJointPairRestAction hk z)) where
  toLinearMap := directLinear hk z hd
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    change witnessBalancePackingInductionTransitivity hk z hd
      (witnessBalancePackingInducedAssemblyInverse hk z hd
        (Representation.ind (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
          (witnessBalancePackingAssemblyAction hk z) g q)) =
      Representation.ind (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
        (witnessBalancePackingOriginalToCoarser hk z)) (witnessBalancePackingJointPairRestAction hk z) g
        (witnessBalancePackingInductionTransitivity hk z hd
          (witnessBalancePackingInducedAssemblyInverse hk z hd q))
    calc
      _ = witnessBalancePackingInductionTransitivity hk z hd
        (Representation.ind (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
          (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
            (witnessBalancePackingJointPairRestAction hk z)) g
          (witnessBalancePackingInducedAssemblyInverse hk z hd q)) :=
        congrArg (fun x => witnessBalancePackingInductionTransitivity hk z hd x)
          ((witnessBalancePackingInducedAssemblyInverse hk z hd).map_action g q)
      _ = _ := (witnessBalancePackingInductionTransitivity hk z hd).map_action g
        (witnessBalancePackingInducedAssemblyInverse hk z hd q)

theorem witnessBalancePackingAssemblyDirectReturn_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingAssemblyDirectReturn hk z hd) := by
  change Function.Bijective ((witnessBalancePackingInductionTransitivity hk z hd) ∘
    (witnessBalancePackingInducedAssemblyInverse hk z hd))
  exact (witnessBalancePackingInductionTransitivity_bijective hk z hd).comp
    (witnessBalancePackingInducedAssemblyInverse_bijective hk z hd)


/-- The direct return is the composite of the induced inverse and induction
transitivity. -/
theorem witnessBalancePackingAssemblyDirectReturn_apply (hd : delta≤1)
    (q : Representation.IndV (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
      (witnessBalancePackingAssemblyAction hk z)) :
    witnessBalancePackingAssemblyDirectReturn hk z hd q =
      witnessBalancePackingInductionTransitivity hk z hd
        (witnessBalancePackingInducedAssemblyInverse hk z hd q) := rfl

/-- The direct return on induced generators. -/
theorem witnessBalancePackingAssemblyDirectReturn_mk (hd : delta≤1)
    (g : Equiv.Perm (Fin n)) (h : witnessBalancePackingCoarserGroup hk z)
    (v : witnessBalancePackingJointPairRestSpace hk z) :
    witnessBalancePackingAssemblyDirectReturn hk z hd
      (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
        (witnessBalancePackingAssemblyAction hk z) g
        (witnessBalancePackingAssemblyReturn hk z
          (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
            (witnessBalancePackingJointPairRestAction hk z) h v)))=
    Representation.IndV.mk (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
      (witnessBalancePackingOriginalToCoarser hk z)) (witnessBalancePackingJointPairRestAction hk z)
      (witnessBalancePackingCoarserHom hk z hd h*g) v := by
  rw [witnessBalancePackingAssemblyDirectReturn_apply,
    witnessBalancePackingInducedAssemblyInverse_mk, witnessBalancePackingAssemblyInverse_return,
    witnessBalancePackingInductionTransitivity_mk]

end
end HSTZ
#print axioms HSTZ.witnessBalancePackingAssemblyInverse
#print axioms HSTZ.witnessBalancePackingAssemblyInverse_return
#print axioms HSTZ.witnessBalancePackingAssemblyReturn_inverse
#print axioms HSTZ.witnessBalancePackingInducedAssemblyInverse
#print axioms HSTZ.witnessBalancePackingInducedAssemblyInverse_bijective
#print axioms HSTZ.witnessBalancePackingInducedAssemblyInverse_mk
#print axioms HSTZ.witnessBalancePackingAssemblyDirectReturn
#print axioms HSTZ.witnessBalancePackingAssemblyDirectReturn_bijective

#print axioms HSTZ.witnessBalancePackingAssemblyDirectReturn_apply
#print axioms HSTZ.witnessBalancePackingAssemblyDirectReturn_mk
