import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePackingSupportReturn
import HSTZ.WitnessBalancePackingLocalSupport

/-! An injective equivariant map from the tower Pi tensor into the assembly. The
local injections are given as explicit data `L`; the map is
`split ∘ reindex(beta.symm)⁻¹ ∘ ⨂ L`. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))
local instance wbsmRestACG : AddCommGroup (witnessBalancePackingRestTensorSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance wbsmPairRestACG : AddCommGroup (witnessBalancePackingJointPairRestSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance wbsmPairRestModule : Module ℂ (witnessBalancePackingJointPairRestSpace hk z) := TensorProduct.leftModule
local instance wbsmAssemblyACG : AddCommGroup (witnessBalancePackingAssemblySpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- Joint × rest group split used by the block relabelling. -/
abbrev witnessBalanceSplitGroup :=
  sumSplitGroup (witnessBalancePackingJointDegree hk z)
    (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val)

/-- Reindex of the joint ⊕ rest Pi tensor to the tower block index. -/
abbrev witnessBalanceBlockReindex :=
  PiTensorProduct.reindex ℂ (witnessBalanceBlockSpace hk z) (witnessBalancePackingBlockBeta k delta).symm

theorem witnessBalanceRelabel_key (hd : delta ≤ 1)
    (g : witnessBalancePackingCoarserGroup hk z)
    (v : TowerIdx (witnessBalancePackingBlocks k delta).length (witnessBalancePackingBlocks k delta).length) :
    positionPermHom (witnessBalancePackingBlockFiber hk z hd v)
      ((witnessBalancePackingBlockRelabel hk z hd).symm g v) =
      (witnessBalanceSplitGroup hk z).symm g (witnessBalancePackingBlockBeta k delta v) := by
  have h := piRelabel_apply (witnessBalancePackingJointDegree hk z)
    (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val)
    (fun v : TowerIdx (witnessBalancePackingBlocks k delta).length
      (witnessBalancePackingBlocks k delta).length => witnessBalancePackingSelectedDegree hk z v.val)
    (witnessBalancePackingBlockBeta k delta) (witnessBalancePackingBlockFiber hk z hd)
    ((piRelabel _ _ _ (witnessBalancePackingBlockBeta k delta)
      (witnessBalancePackingBlockFiber hk z hd)).symm ((witnessBalanceSplitGroup hk z).symm g)) v
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem witnessBalanceBlockReindex_conj
    (G : ∀ x : Unit ⊕ witnessBalancePackingRestIndex k delta,
      Equiv.Perm (Fin (witnessBalanceBlockSize hk z x)))
    (w : ⨂[ℂ] x, witnessBalanceBlockSpace hk z x) :
    witnessBalanceBlockReindex hk z (piTensorRep (witnessBalanceBlockRep hk z) G w) =
      piTensorRep (fun v => witnessBalanceBlockRep hk z (witnessBalancePackingBlockBeta k delta v))
        (fun v => G (witnessBalancePackingBlockBeta k delta v)) (witnessBalanceBlockReindex hk z w) := by
  change PiTensorProduct.reindex ℂ (witnessBalanceBlockSpace hk z)
      (witnessBalancePackingBlockBeta k delta).symm
      (PiTensorProduct.map (fun x => witnessBalanceBlockRep hk z x (G x)) w) =
    PiTensorProduct.map
      (fun v => witnessBalanceBlockRep hk z (witnessBalancePackingBlockBeta k delta v)
        (G (witnessBalancePackingBlockBeta k delta v)))
      (PiTensorProduct.reindex ℂ (witnessBalanceBlockSpace hk z)
        (witnessBalancePackingBlockBeta k delta).symm w)
  exact (PiTensorProduct.map_reindex (R := ℂ)
    (fun x => witnessBalanceBlockRep hk z x (G x))
    (witnessBalancePackingBlockBeta k delta).symm w).symm

variable (hd : delta ≤ 1)
  (p : ∀ i, Nat.Partition (witnessBalancePackingSelectedDegree hk z i))
  (L : ∀ v : TowerIdx (witnessBalancePackingBlocks k delta).length
      (witnessBalancePackingBlocks k delta).length,
    Representation.IntertwiningMap (spechtRep (partitionTableau (p v.val)))
      ((witnessBalanceBlockRep hk z (witnessBalancePackingBlockBeta k delta v)).comp
        (positionPermHom (witnessBalancePackingBlockFiber hk z hd v))))

/-- Tensor of the local injections. -/
def witnessBalanceTowerLocalMap :
    (⨂[ℂ] v : TowerIdx (witnessBalancePackingBlocks k delta).length
      (witnessBalancePackingBlocks k delta).length, Specht (partitionTableau (p v.val))) →ₗ[ℂ]
      ⨂[ℂ] v : TowerIdx (witnessBalancePackingBlocks k delta).length
        (witnessBalancePackingBlocks k delta).length,
          witnessBalanceBlockSpace hk z (witnessBalancePackingBlockBeta k delta v) :=
  PiTensorProduct.map (fun v => (L v).toLinearMap)

theorem witnessBalanceTowerLocalMap_conj (g : witnessBalancePackingCoarserGroup hk z)
    (y : ⨂[ℂ] v : TowerIdx (witnessBalancePackingBlocks k delta).length
      (witnessBalancePackingBlocks k delta).length, Specht (partitionTableau (p v.val))) :
    witnessBalanceTowerLocalMap hk z hd p L
      (towerRep (witnessBalancePackingSelectedDegree hk z) (fun i => spechtRep (partitionTableau (p i)))
        (witnessBalancePackingBlocks k delta).length
        ((witnessBalancePackingBlockRelabel hk z hd).symm g) y) =
      piTensorRep (fun v => witnessBalanceBlockRep hk z (witnessBalancePackingBlockBeta k delta v))
        (fun v => (witnessBalanceSplitGroup hk z).symm g (witnessBalancePackingBlockBeta k delta v))
        (witnessBalanceTowerLocalMap hk z hd p L y) := by
  have he : (witnessBalanceTowerLocalMap hk z hd p L) ∘ₗ
      (towerRep (witnessBalancePackingSelectedDegree hk z) (fun i => spechtRep (partitionTableau (p i)))
        (witnessBalancePackingBlocks k delta).length ((witnessBalancePackingBlockRelabel hk z hd).symm g)) =
      (piTensorRep (fun v => witnessBalanceBlockRep hk z (witnessBalancePackingBlockBeta k delta v))
        (fun v => (witnessBalanceSplitGroup hk z).symm g (witnessBalancePackingBlockBeta k delta v))) ∘ₗ
        (witnessBalanceTowerLocalMap hk z hd p L) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change witnessBalanceTowerLocalMap hk z hd p L
        (towerRep (witnessBalancePackingSelectedDegree hk z) (fun i => spechtRep (partitionTableau (p i)))
          (witnessBalancePackingBlocks k delta).length ((witnessBalancePackingBlockRelabel hk z hd).symm g)
          (PiTensorProduct.tprod ℂ w)) =
      piTensorRep (fun v => witnessBalanceBlockRep hk z (witnessBalancePackingBlockBeta k delta v))
        (fun v => (witnessBalanceSplitGroup hk z).symm g (witnessBalancePackingBlockBeta k delta v))
        (witnessBalanceTowerLocalMap hk z hd p L (PiTensorProduct.tprod ℂ w))
    rw [towerRep,piTensorRep_tprod,witnessBalanceTowerLocalMap,PiTensorProduct.map_tprod,
      PiTensorProduct.map_tprod,piTensorRep_tprod]
    congr 1
    funext v
    rw [← witnessBalanceRelabel_key hk z hd g v]
    exact (L v).map_action ((witnessBalancePackingBlockRelabel hk z hd).symm g v) (w v)
  exact DFunLike.congr_fun he y

/-- The tower Pi tensor mapped equivariantly into the assembly. -/
def witnessBalanceTowerAssemblyMap : Representation.IntertwiningMap
    ((towerRep (witnessBalancePackingSelectedDegree hk z) (fun i => spechtRep (partitionTableau (p i)))
      (witnessBalancePackingBlocks k delta).length).comp
        (witnessBalancePackingBlockRelabel hk z hd).symm.toMonoidHom)
    (witnessBalancePackingAssemblyAction hk z) where
  toLinearMap := (witnessBalanceBlockSplit hk z).toLinearMap ∘ₗ
    (witnessBalanceBlockReindex hk z).symm.toLinearMap ∘ₗ witnessBalanceTowerLocalMap hk z hd p L
  isIntertwining' g := by
    apply LinearMap.ext
    intro y
    change witnessBalanceBlockSplit hk z ((witnessBalanceBlockReindex hk z).symm
        (witnessBalanceTowerLocalMap hk z hd p L
          (towerRep (witnessBalancePackingSelectedDegree hk z) (fun i => spechtRep (partitionTableau (p i)))
            (witnessBalancePackingBlocks k delta).length
            ((witnessBalancePackingBlockRelabel hk z hd).symm g) y))) =
      witnessBalancePackingAssemblyAction hk z g (witnessBalanceBlockSplit hk z
        ((witnessBalanceBlockReindex hk z).symm (witnessBalanceTowerLocalMap hk z hd p L y)))
    rw [witnessBalanceTowerLocalMap_conj]
    have h2 := witnessBalanceBlockReindex_conj hk z ((witnessBalanceSplitGroup hk z).symm g)
      ((witnessBalanceBlockReindex hk z).symm (witnessBalanceTowerLocalMap hk z hd p L y))
    rw [LinearEquiv.apply_symm_apply] at h2
    rw [← h2,LinearEquiv.symm_apply_apply,witnessBalanceBlockSplit_conj,MulEquiv.apply_symm_apply]

theorem witnessBalanceTowerAssemblyMap_injective (hL : ∀ v, Function.Injective (L v)) :
    Function.Injective (witnessBalanceTowerAssemblyMap hk z hd p L) :=
  (witnessBalanceBlockSplit hk z).injective.comp ((witnessBalanceBlockReindex hk z).symm.injective.comp
    (piTensorMap_injective (fun v => (L v).toLinearMap) hL))

/-- Positivity from the physical tower injection and local injections. -/
theorem witnessBalance_pos_of_tower_injection (hL : ∀ v, Function.Injective (L v))
    {mu : YoungDiagram} (s : Tableau n mu)
    (E : Representation.IntertwiningMap (spechtRep s)
      (Representation.ind (witnessBalancePackingCoarserHom hk z hd)
        ((towerRep (witnessBalancePackingSelectedDegree hk z) (fun i => spechtRep (partitionTableau (p i)))
          (witnessBalancePackingBlocks k delta).length).comp
            (witnessBalancePackingBlockRelabel hk z hd).symm.toMonoidHom)))
    (hE : Function.Injective E) : 0 < kronecker z z s := by
  haveI : Nonempty (witnessBalancePackingCoarserGroup hk z) := ⟨1⟩
  letI : NeZero (Nat.card (witnessBalancePackingCoarserGroup hk z) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (witnessBalancePackingCoarserGroup hk z)).ne'⟩
  exact witnessBalance_pos_of_assembly_injection hk z hd s
    ((inducedMap (witnessBalancePackingCoarserHom hk z hd)
      (witnessBalanceTowerAssemblyMap hk z hd p L)).comp E)
    ((inducedMap_injective (witnessBalancePackingCoarserHom hk z hd)
      (witnessBalanceTowerAssemblyMap hk z hd p L)
      (witnessBalanceTowerAssemblyMap_injective hk z hd p L hL)).comp hE)
end

end
end HSTZ
#print axioms HSTZ.witnessBalanceRelabel_key
#print axioms HSTZ.witnessBalanceBlockReindex_conj
#print axioms HSTZ.witnessBalanceTowerLocalMap_conj
#print axioms HSTZ.witnessBalanceTowerAssemblyMap_injective
#print axioms HSTZ.witnessBalance_pos_of_tower_injection
