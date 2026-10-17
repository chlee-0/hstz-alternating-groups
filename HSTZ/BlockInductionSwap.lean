import HSTZ.TensorInductionSwap
import HSTZ.PositionBlock

/-! Block-order normalization and the induced tensor exchange.
The ambient positions are retained, including empty blocks. -/
namespace HSTZ
open scoped TensorProduct

def swapPositionBlocks {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin n ≃ Fin b ⊕ Fin a := e.trans (Equiv.sumComm _ _)

theorem sumPermHom_swap {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    sumPermHom (swapPositionBlocks e) =
      (sumPermHom e).comp (productSwap (Equiv.Perm (Fin b)) (Equiv.Perm (Fin a))).toMonoidHom := by
  ext gh i
  obtain ⟨j, rfl⟩ := e.symm.surjective i
  cases j <;> simp [sumPermHom, swapPositionBlocks, OAI.Saxl.sumPerm,
    productSwap, Equiv.permCongr_apply]

theorem sumPermHom_swap_normalization {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (sumPermHom (swapPositionBlocks e)).comp
      (productSwap (Equiv.Perm (Fin a)) (Equiv.Perm (Fin b))).toMonoidHom = sumPermHom e := by
  rw [sumPermHom_swap]
  exact productSwap_inducing_normalization (sumPermHom e)

/-- The carrier bijection and an explicit formula on ambient generators. -/
theorem exists_blockInductionSwap {R U W : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup W] [Module R W]
    {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (rho : Representation R (Equiv.Perm (Fin a)) U)
    (sigma : Representation R (Equiv.Perm (Fin b)) W) :
    ∃ M : Representation.IntertwiningMap
      (Representation.ind (sumPermHom (swapPositionBlocks e)) (independentTensor sigma rho))
      (Representation.ind (sumPermHom e) (independentTensor rho sigma)),
      Function.Bijective M ∧ ∀ g z,
        M (Representation.IndV.mk (sumPermHom (swapPositionBlocks e))
          (independentTensor sigma rho) g z) =
        Representation.IndV.mk (sumPermHom e) (independentTensor rho sigma) g
          (TensorProduct.comm R W U z) := by
  have hm : ∃ M : Representation.IntertwiningMap
      (Representation.ind (sumPermHom (swapPositionBlocks e)) (independentTensor sigma rho))
      (Representation.ind ((sumPermHom (swapPositionBlocks e)).comp
        (productSwap (Equiv.Perm (Fin a)) (Equiv.Perm (Fin b))).toMonoidHom)
        (independentTensor rho sigma)),
      Function.Bijective M ∧ ∀ g z,
        M (Representation.IndV.mk (sumPermHom (swapPositionBlocks e))
          (independentTensor sigma rho) g z) =
        Representation.IndV.mk ((sumPermHom (swapPositionBlocks e)).comp
          (productSwap (Equiv.Perm (Fin a)) (Equiv.Perm (Fin b))).toMonoidHom)
          (independentTensor rho sigma) g (TensorProduct.comm R W U z) := by
    exact ⟨inducedTensorSwap sigma rho (sumPermHom (swapPositionBlocks e)),
      inducedTensorSwap_bijective sigma rho (sumPermHom (swapPositionBlocks e)),
      inducedTensorSwap_mk sigma rho (sumPermHom (swapPositionBlocks e))⟩
  rw [sumPermHom_swap_normalization] at hm
  exact hm

end HSTZ
#print axioms HSTZ.sumPermHom_swap
#print axioms HSTZ.sumPermHom_swap_normalization
#print axioms HSTZ.exists_blockInductionSwap
