import HSTZ.WitnessBalancePackingCoarserGroup
import HSTZ.InducedReparam

/-! The original-label group decomposed into the ordered component pair and the
entire rest. Uses dependent Pi/`Equiv` and tensor interfaces, building on
OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The full joint permutation group remains a larger induction group. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessBalancePackingPairGroup :=
  Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0)) ×
    Equiv.Perm (Fin (witnessBalanceComponentSize hk z (witnessBalancePackingJointLabel delta)))
abbrev witnessBalancePackingRestGroup :=
  ∀ a : witnessBalancePackingRestIndex k delta,
    Equiv.Perm (Fin (witnessBalanceComponentSize hk z a.val.val))
abbrev witnessBalancePackingProductGroup :=
  witnessBalancePackingPairGroup hk z × witnessBalancePackingRestGroup hk z

private def jointPermEquiv :
    (∀ a : witnessBalancePackingJointIndex k delta,
      Equiv.Perm (Fin (witnessBalanceComponentSize hk z a.val.val))) ≃
    witnessBalancePackingPairGroup hk z :=
  (Equiv.piCongrLeft (fun a : witnessBalancePackingJointIndex k delta =>
    Equiv.Perm (Fin (witnessBalanceComponentSize hk z a.val.val)))
    (witnessBalancePackingJointOrder k delta)).symm.trans
      ((Equiv.sumPiEquivProdPi (fun u : Unit ⊕ Unit =>
        Equiv.Perm (Fin (witnessBalanceComponentSize hk z
          (witnessBalancePackingJointOrder k delta u).val.val)))).trans
        (Equiv.prodCongr (Equiv.piUnique _) (Equiv.piUnique _)))

private def productPermEquiv : witnessBalancePackingOriginalGroup hk z ≃
    witnessBalancePackingProductGroup hk z :=
  (Equiv.piCongrLeft (fun a : witnessBalancePackingLabelIndex k delta =>
    Equiv.Perm (Fin (witnessBalanceComponentSize hk z a.val)))
    (witnessBalancePackingJointRestCut k delta).symm).symm.trans
      ((Equiv.sumPiEquivProdPi (fun a =>
        Equiv.Perm (Fin (witnessBalanceComponentSize hk z
          ((witnessBalancePackingJointRestCut k delta).symm a).val)))).trans
        (Equiv.prodCongr (jointPermEquiv hk z) (Equiv.refl _)))

/-- Restriction to label 0 and then the joint label (1 or 2), together with every
remaining label. The inverse uses the dependent cut and the ordered joint index. -/
def witnessBalancePackingProductEquiv : witnessBalancePackingOriginalGroup hk z ≃*
    witnessBalancePackingProductGroup hk z where
  toEquiv := productPermEquiv hk z
  map_mul' _ _ := rfl

theorem witnessBalancePackingProductEquiv_apply
    (g : witnessBalancePackingOriginalGroup hk z) :
    witnessBalancePackingProductEquiv hk z g=
      (witnessBalancePackingJointProductHom hk z g,
        fun a : witnessBalancePackingRestIndex k delta => g a.val) := rfl

theorem witnessBalancePackingProductEquiv_inverse
    (g : witnessBalancePackingOriginalGroup hk z) :
    (witnessBalancePackingProductEquiv hk z).symm
      (witnessBalancePackingJointProductHom hk z g,fun a => g a.val)=g :=
  (witnessBalancePackingProductEquiv hk z).symm_apply_apply g

/-- Independent action of all rest groups on their prescribed projected factors. -/
def witnessBalancePackingRestProductAction : Representation ℂ
    (witnessBalancePackingRestGroup hk z) (witnessBalancePackingRestTensorSpace hk z) where
  toFun g := PiTensorProduct.map fun a =>
    (witnessBalanceLocalProjectedFactor hk z a.val.val).toRepresentation (g a)
  map_one' := by
    change PiTensorProduct.map (fun a : witnessBalancePackingRestIndex k delta =>
      (witnessBalanceLocalProjectedFactor hk z a.val.val).toRepresentation 1)=1
    simp only [map_one]
    exact PiTensorProduct.map_one
  map_mul' g h := by
    change PiTensorProduct.map (fun a : witnessBalancePackingRestIndex k delta =>
      (witnessBalanceLocalProjectedFactor hk z a.val.val).toRepresentation (g a*h a))=_
    simp only [map_mul]
    exact PiTensorProduct.map_mul _ _

def witnessBalancePackingProductAction : Representation ℂ
    (witnessBalancePackingProductGroup hk z) (witnessBalancePackingJointPairRestSpace hk z) :=
  independentTensor
    (independentTensor (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
      (witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toRepresentation)
    (witnessBalancePackingRestProductAction hk z)

/-- The source module is the pair tensor the entire rest, with an explicit product group. -/
theorem witnessBalancePackingProductAction_original :
    (witnessBalancePackingProductAction hk z).comp
      (witnessBalancePackingProductEquiv hk z).toMonoidHom=
    witnessBalancePackingJointPairRestAction hk z := by
  rfl

/-- The larger physical block inclusion is the canonical pair hom and identity on rest. -/
def witnessBalancePackingProductToCoarser : witnessBalancePackingProductGroup hk z →*
    witnessBalancePackingCoarserGroup hk z :=
  (sumPermHom finSumFinEquiv.symm).prodMap (MonoidHom.id _)

theorem witnessBalancePackingProductToCoarser_original
    (g : witnessBalancePackingOriginalGroup hk z) :
    witnessBalancePackingProductToCoarser hk z (witnessBalancePackingProductEquiv hk z g)=
      witnessBalancePackingOriginalToCoarser hk z g := rfl

theorem witnessBalancePackingProduct_physical (hd : delta≤1)
    (g : witnessBalancePackingOriginalGroup hk z) :
    witnessBalancePackingCoarserHom hk z hd
      (witnessBalancePackingProductToCoarser hk z (witnessBalancePackingProductEquiv hk z g))=
    (witnessBalancePackingOriginalHom hk z hd g).val :=
  witnessBalancePackingCoarserHom_original hk z hd g

local instance : AddCommGroup (witnessBalancePackingRestTensorSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup (witnessBalancePackingJointPairRestSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : Module ℂ (witnessBalancePackingJointPairRestSpace hk z) :=
  TensorProduct.leftModule

/-- Source induction reparametrized by the product equivalence over all labels. -/
def witnessBalancePackingProductInduction : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
      (witnessBalancePackingJointPairRestAction hk z))
    (Representation.ind (k:=ℂ) (witnessBalancePackingProductToCoarser hk z)
      (witnessBalancePackingProductAction hk z)) :=
  inducedReparam (witnessBalancePackingProductEquiv hk z)
    (witnessBalancePackingProductToCoarser hk z) (witnessBalancePackingProductAction hk z)

theorem witnessBalancePackingProductInduction_mk
    (g : witnessBalancePackingCoarserGroup hk z)
    (v : witnessBalancePackingJointPairRestSpace hk z) :
    witnessBalancePackingProductInduction hk z
      (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingOriginalToCoarser hk z)
        (witnessBalancePackingJointPairRestAction hk z) g v)=
    Representation.IndV.mk (k:=ℂ) (witnessBalancePackingProductToCoarser hk z)
      (witnessBalancePackingProductAction hk z) g v :=
  inducedReparam_mk (witnessBalancePackingProductEquiv hk z)
    (witnessBalancePackingProductToCoarser hk z) (witnessBalancePackingProductAction hk z) g v

theorem witnessBalancePackingProductInduction_bijective :
    Function.Bijective (witnessBalancePackingProductInduction hk z) :=
  inducedReparam_bijective (witnessBalancePackingProductEquiv hk z)
    (witnessBalancePackingProductToCoarser hk z) (witnessBalancePackingProductAction hk z)

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingProductEquiv
#print axioms HSTZ.witnessBalancePackingProductEquiv_apply
#print axioms HSTZ.witnessBalancePackingProductEquiv_inverse
#print axioms HSTZ.witnessBalancePackingRestProductAction
#print axioms HSTZ.witnessBalancePackingProductAction
#print axioms HSTZ.witnessBalancePackingProductAction_original
#print axioms HSTZ.witnessBalancePackingProductToCoarser_original
#print axioms HSTZ.witnessBalancePackingProduct_physical
#print axioms HSTZ.witnessBalancePackingProductInduction
#print axioms HSTZ.witnessBalancePackingProductInduction_mk
#print axioms HSTZ.witnessBalancePackingProductInduction_bijective
