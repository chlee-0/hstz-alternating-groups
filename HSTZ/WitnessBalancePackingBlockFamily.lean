import HSTZ.SpechtPositionTransport
import HSTZ.WitnessBalancePackingPhysicalTower
import HSTZ.WitnessBalancePackingAssemblyH
import HSTZ.WitnessBalanceProjectedFactors
import HSTZ.WitnessBalanceAverage
import HSTZ.WitnessBalanceFrontier

/-! The joint/rest family of local factors and its splitting into the assembly space.
This is the first step of the packing support proof for the asymmetric witness, which
is assembled from the physical tower, the local injections and the projected range.
The local factor modules are indexed by joint ⊕ rest labels and reached from the
tower blocks by `PiTensorProduct.reindex` along `beta.symm`, so no casts are needed.
Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- Size of a joint/rest block. -/
abbrev witnessBalanceBlockSize (x : Unit ⊕ witnessBalancePackingRestIndex k delta) : ℕ :=
  Sum.elim (fun _ : Unit => witnessBalancePackingJointDegree hk z)
    (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val) x

local instance : AddCommGroup (witnessBalancePackingJointPairSpace hk z) :=
  TensorProduct.addCommGroup (R:=ℂ)
    (M:=(witnessBalanceLocalProjectedFactor hk z 0).toSubmodule)
    (N:=(witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toSubmodule)
local instance : Module ℂ (witnessBalancePackingJointPairSpace hk z) := TensorProduct.leftModule

/-- Joint pair source (same construction as the assembly's pair factor). -/
abbrev witnessBalanceJointPairRep : Representation ℂ (witnessBalancePackingPairGroup hk z)
    (witnessBalancePackingJointPairSpace hk z) := independentTensor
  (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
  (witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toRepresentation

abbrev witnessBalanceJointPairHom : witnessBalancePackingPairGroup hk z →*
    Equiv.Perm (Fin (witnessBalancePackingJointDegree hk z)) :=
  sumPermHom finSumFinEquiv.symm

/-- Joint induced pair space (the left factor of the assembly). -/
abbrev witnessBalanceJointSpace :=
  Representation.IndV (witnessBalanceJointPairHom hk z) (witnessBalanceJointPairRep hk z)

/-- Joint induced pair representation. -/
abbrev witnessBalanceJointRep : Representation ℂ (Equiv.Perm (Fin (witnessBalancePackingJointDegree hk z)))
    (witnessBalanceJointSpace hk z) :=
  Representation.ind (witnessBalanceJointPairHom hk z) (witnessBalanceJointPairRep hk z)

/-- Local factor module of a joint/rest block. -/
def witnessBalanceBlockSpace (x : Unit ⊕ witnessBalancePackingRestIndex k delta) : Type :=
  Sum.elim (fun _ : Unit => witnessBalanceJointSpace hk z)
    (fun r : witnessBalancePackingRestIndex k delta =>
      (witnessBalanceLocalProjectedFactor hk z r.val.val).toSubmodule) x

instance witnessBalanceBlockSpace.instACG :
    ∀ x, AddCommGroup (witnessBalanceBlockSpace hk z x)
  | .inl _ => (inferInstance : AddCommGroup (witnessBalanceJointSpace hk z))
  | .inr r => (inferInstance : AddCommGroup (witnessBalanceLocalProjectedFactor hk z r.val.val).toSubmodule)

instance witnessBalanceBlockSpace.instModule :
    ∀ x, Module ℂ (witnessBalanceBlockSpace hk z x)
  | .inl _ => (inferInstance : Module ℂ (witnessBalanceJointSpace hk z))
  | .inr r => (inferInstance : Module ℂ (witnessBalanceLocalProjectedFactor hk z r.val.val).toSubmodule)

/-- Local factor representation of a joint/rest block. -/
def witnessBalanceBlockRep : ∀ x : Unit ⊕ witnessBalancePackingRestIndex k delta,
    Representation ℂ (Equiv.Perm (Fin (witnessBalanceBlockSize hk z x))) (witnessBalanceBlockSpace hk z x)
  | .inl _ => witnessBalanceJointRep hk z
  | .inr r => (witnessBalanceLocalProjectedFactor hk z r.val.val).toRepresentation

/-- Split joint ⊕ rest Pi tensor into the assembly space. -/
def witnessBalanceBlockSplit :
    (⨂[ℂ] x, witnessBalanceBlockSpace hk z x) ≃ₗ[ℂ] witnessBalancePackingAssemblySpace hk z :=
  (PiTensorProduct.tmulEquivDep ℂ (witnessBalanceBlockSpace hk z)).symm.trans
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv (R := ℂ)
      (s := fun u : Unit => witnessBalanceBlockSpace hk z (.inl u)) ()) (LinearEquiv.refl ℂ _))

theorem witnessBalance_restProduct_tprod (g : witnessBalancePackingRestGroup hk z)
    (f : ∀ a : witnessBalancePackingRestIndex k delta,
      (witnessBalanceLocalProjectedFactor hk z a.val.val).toSubmodule) :
    witnessBalancePackingRestProductAction hk z g (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ fun a =>
        (witnessBalanceLocalProjectedFactor hk z a.val.val).toRepresentation (g a) (f a) :=
  PiTensorProduct.map_tprod _ _

theorem witnessBalanceBlockSplit_tprod
    (f : ∀ x : Unit ⊕ witnessBalancePackingRestIndex k delta, witnessBalanceBlockSpace hk z x) :
    witnessBalanceBlockSplit hk z (PiTensorProduct.tprod ℂ f) =
      f (.inl ()) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun r => f (.inr r)) := by
  erw [witnessBalanceBlockSplit,LinearEquiv.trans_apply,PiTensorProduct.tmulEquivDep_symm_apply,
    TensorProduct.congr_tmul]
  congr 1
  exact PiTensorProduct.subsingletonEquiv_apply_tprod (R := ℂ) () _

theorem witnessBalanceBlockSplit_conj
    (G : ∀ x : Unit ⊕ witnessBalancePackingRestIndex k delta,
      Equiv.Perm (Fin (witnessBalanceBlockSize hk z x)))
    (w : ⨂[ℂ] x, witnessBalanceBlockSpace hk z x) :
    witnessBalanceBlockSplit hk z (piTensorRep (witnessBalanceBlockRep hk z) G w) =
      witnessBalancePackingAssemblyAction hk z
        (sumSplitGroup (witnessBalancePackingJointDegree hk z)
          (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val) G)
        (witnessBalanceBlockSplit hk z w) := by
  have he : (witnessBalanceBlockSplit hk z).toLinearMap ∘ₗ piTensorRep (witnessBalanceBlockRep hk z) G =
      (witnessBalancePackingAssemblyAction hk z
        (sumSplitGroup (witnessBalancePackingJointDegree hk z)
          (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val) G)) ∘ₗ
        (witnessBalanceBlockSplit hk z).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    change witnessBalanceBlockSplit hk z (piTensorRep (witnessBalanceBlockRep hk z) G
        (PiTensorProduct.tprod ℂ f)) =
      witnessBalancePackingAssemblyAction hk z
        (sumSplitGroup (witnessBalancePackingJointDegree hk z)
          (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val) G)
        (witnessBalanceBlockSplit hk z (PiTensorProduct.tprod ℂ f))
    rw [piTensorRep_tprod,witnessBalanceBlockSplit_tprod,witnessBalanceBlockSplit_tprod]
    change (witnessBalanceJointRep hk z (G (.inl ())) (f (.inl ()))) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun r : witnessBalancePackingRestIndex k delta =>
          (witnessBalanceLocalProjectedFactor hk z r.val.val).toRepresentation
            (G (.inr r)) (f (.inr r))) =
      (witnessBalanceJointRep hk z (G (.inl ())) (f (.inl ()))) ⊗ₜ[ℂ]
        witnessBalancePackingRestProductAction hk z (fun r => G (.inr r))
          (PiTensorProduct.tprod ℂ fun r => f (.inr r))
    rw [witnessBalance_restProduct_tprod hk z (fun r => G (.inr r))
      (fun r => f (.inr r))]
  exact DFunLike.congr_fun he w

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceBlockSplit_conj
