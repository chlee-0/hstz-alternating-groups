import HSTZ.WitnessBalancePackingProduct
import HSTZ.WitnessBalancePackingSelectedPrefix

/-! Ordinary induction through the larger physical block group.
Reuses OpenAI's `math` repository (commit adc7f1241, Apache-2.0). One private
adapter uses the existing inverse/right `mk` and universal induction interfaces.
This does not supply compatible Young target support. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

section Adapter
variable {H K G V : Type*} [Group H] [Group K] [Group G]
  [AddCommGroup V] [Module ℂ V]
  (psi : H →* K) (phi : K →* G) (sigma : Representation ℂ H V)

private def directBase : Representation.IntertwiningMap sigma
    ((Representation.ind (k:=ℂ) (phi.comp psi) sigma).comp (phi.comp psi)) where
  toLinearMap := Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma 1
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    change Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma 1 (sigma h v)=
      Representation.ind (k:=ℂ) (phi.comp psi) sigma (phi (psi h))
        (Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma 1 v)
    rw [Representation.ind_mk]
    simpa using (ind_mk_inv_mul (phi.comp psi) sigma h 1 v).symm

private def innerReturn : Representation.IntertwiningMap (Representation.ind (k:=ℂ) psi sigma)
    ((Representation.ind (k:=ℂ) (phi.comp psi) sigma).comp phi) :=
  inducedIntertwiner psi sigma ((Representation.ind (k:=ℂ) (phi.comp psi) sigma).comp phi)
    (directBase psi phi sigma)

private theorem innerReturn_mk (h : K) (v : V) :
    innerReturn psi phi sigma (Representation.IndV.mk (k:=ℂ) psi sigma h v)=
      Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma (phi h) v := by
  change inducedLinearMap _ _ _ _ _=_
  rw [inducedLinearMap_mk]
  change Representation.ind (k:=ℂ) (phi.comp psi) sigma (phi h⁻¹)
    (Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma 1 v)=_
  rw [Representation.ind_mk]
  simp

private def stageReturn : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma))
    (Representation.ind (k:=ℂ) (phi.comp psi) sigma) :=
  inducedIntertwiner phi (Representation.ind (k:=ℂ) psi sigma)
    (Representation.ind (k:=ℂ) (phi.comp psi) sigma) (innerReturn psi phi sigma)

private theorem stageReturn_mk (g : G) (h : K) (v : V) :
    stageReturn psi phi sigma
      (Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) g
        (Representation.IndV.mk (k:=ℂ) psi sigma h v))=
    Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma (phi h*g) v := by
  change inducedLinearMap _ _ _ _ _=_
  rw [inducedLinearMap_mk,innerReturn_mk,Representation.ind_mk]
  simp

private def stageBase : Representation.IntertwiningMap sigma
    ((Representation.ind (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma)).comp (phi.comp psi)) where
  toLinearMap := (Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) 1).comp
    (Representation.IndV.mk (k:=ℂ) psi sigma 1)
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    change Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) 1
      (Representation.IndV.mk (k:=ℂ) psi sigma 1 (sigma h v))=
      Representation.ind (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) (phi (psi h))
        (Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) 1
          (Representation.IndV.mk (k:=ℂ) psi sigma 1 v))
    rw [Representation.ind_mk]
    have he := ind_mk_inv_mul phi (Representation.ind (k:=ℂ) psi sigma) (psi h) 1
      (Representation.IndV.mk (k:=ℂ) psi sigma 1 v)
    rw [mul_one] at he
    simp only [one_mul]
    rw [he,Representation.ind_mk]
    have hi := ind_mk_inv_mul psi sigma h 1 v
    simpa using congrArg (Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) 1) hi.symm

private def stageBack : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (phi.comp psi) sigma)
    (Representation.ind (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma)) :=
  inducedIntertwiner (phi.comp psi) sigma
    (Representation.ind (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma)) (stageBase psi phi sigma)

private theorem stageBack_mk (g : G) (v : V) :
    stageBack psi phi sigma (Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma g v)=
      Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) g
        (Representation.IndV.mk (k:=ℂ) psi sigma 1 v) := by
  change inducedLinearMap _ _ _ _ _=_
  rw [inducedLinearMap_mk]
  change Representation.ind (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) g⁻¹
    (Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) 1
      (Representation.IndV.mk (k:=ℂ) psi sigma 1 v))=_
  rw [Representation.ind_mk]
  simp

private theorem stageReturn_bijective : Function.Bijective (stageReturn psi phi sigma) := by
  have hl : (stageBack psi phi sigma).toLinearMap.comp
      (stageReturn psi phi sigma).toLinearMap=LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    apply Representation.IndV.hom_ext
    intro h
    ext v
    change stageBack psi phi sigma (stageReturn psi phi sigma
      (Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) g
        (Representation.IndV.mk (k:=ℂ) psi sigma h v)))=
          Representation.IndV.mk (k:=ℂ) phi (Representation.ind (k:=ℂ) psi sigma) g
            (Representation.IndV.mk (k:=ℂ) psi sigma h v)
    rw [stageReturn_mk,stageBack_mk]
    have he := ind_mk_inv_mul phi (Representation.ind (k:=ℂ) psi sigma) h⁻¹ g
      (Representation.IndV.mk (k:=ℂ) psi sigma 1 v)
    simpa [Representation.ind_mk] using he
  have hr : (stageReturn psi phi sigma).toLinearMap.comp
      (stageBack psi phi sigma).toLinearMap=LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext v
    change stageReturn psi phi sigma (stageBack psi phi sigma
      (Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma g v))=
        Representation.IndV.mk (k:=ℂ) (phi.comp psi) sigma g v
    rw [stageBack_mk,stageReturn_mk]
    simp
  have hleft : Function.LeftInverse (stageBack psi phi sigma) (stageReturn psi phi sigma) :=
    fun x => DFunLike.congr_fun hl x
  have hright : Function.RightInverse (stageBack psi phi sigma) (stageReturn psi phi sigma) :=
    fun x => DFunLike.congr_fun hr x
  exact ⟨hleft.injective,hright.surjective⟩
end Adapter

section Actual
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))
local instance : AddCommGroup (witnessBalancePackingRestTensorSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup (witnessBalancePackingJointPairRestSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : Module ℂ (witnessBalancePackingJointPairRestSpace hk z) :=
  TensorProduct.leftModule

/-- Two-stage induction through K, whose full joint permutation group is larger than H. -/
def witnessBalancePackingInductionTransitivity (hd : delta≤1) : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
      (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
        (witnessBalancePackingJointPairRestAction hk z)))
    (Representation.ind (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
      (witnessBalancePackingOriginalToCoarser hk z))
      (witnessBalancePackingJointPairRestAction hk z)) :=
  stageReturn (witnessBalancePackingOriginalToCoarser hk z)
    (witnessBalancePackingCoarserHom hk z hd) (witnessBalancePackingJointPairRestAction hk z)

theorem witnessBalancePackingInductionTransitivity_mk (hd : delta≤1)
    (g : Equiv.Perm (Fin n)) (h : witnessBalancePackingCoarserGroup hk z)
    (v : witnessBalancePackingJointPairRestSpace hk z) :
    witnessBalancePackingInductionTransitivity hk z hd
      (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingCoarserHom hk z hd)
        (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
          (witnessBalancePackingJointPairRestAction hk z)) g
        (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
          (witnessBalancePackingJointPairRestAction hk z) h v))=
    Representation.IndV.mk (k:=ℂ) ((witnessBalancePackingCoarserHom hk z hd).comp
      (witnessBalancePackingOriginalToCoarser hk z))
      (witnessBalancePackingJointPairRestAction hk z)
      (witnessBalancePackingCoarserHom hk z hd h*g) v :=
  stageReturn_mk _ _ _ g h v

theorem witnessBalancePackingInductionTransitivity_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingInductionTransitivity hk z hd) :=
  stageReturn_bijective _ _ _

/-- The direct inducing homomorphism is the original inclusion of H in physical positions. -/
theorem witnessBalancePackingInductionPhysicalHom (hd : delta≤1) :
    (witnessBalancePackingCoarserHom hk z hd).comp
      (witnessBalancePackingOriginalToCoarser hk z)=
    (witnessBalanceGroup hk z).subtype.comp (witnessBalancePackingOriginalHom hk z hd) := by
  apply MonoidHom.ext
  intro g
  exact witnessBalancePackingCoarserHom_original hk z hd g
end Actual

section SelectedPrefix
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- Two-stage transitivity for the original selected prefix product homomorphism
and the next physical-degree boundary cut. -/
def witnessBalancePackingSelectedPrefixTransitivity D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :=
  stageReturn (witnessBalancePackingSelectedPrefixProductHom hk z D hc p i)
    (sumPermHom (witnessBalancePackingSelectedCut hk z i (D i.castSucc) (D i.succ) (hc i)))
    (witnessBalancePackingSelectedPrefixTensorAction hk z D hc p i)

theorem witnessBalancePackingSelectedPrefixTransitivity_bijective D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :
    Function.Bijective (witnessBalancePackingSelectedPrefixTransitivity hk z D hc p i) :=
  stageReturn_bijective _ _ _

end SelectedPrefix
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingInductionTransitivity
#print axioms HSTZ.witnessBalancePackingInductionTransitivity_mk
#print axioms HSTZ.witnessBalancePackingInductionTransitivity_bijective
#print axioms HSTZ.witnessBalancePackingInductionPhysicalHom
#print axioms HSTZ.witnessBalancePackingSelectedPrefixTransitivity
#print axioms HSTZ.witnessBalancePackingSelectedPrefixTransitivity_bijective
