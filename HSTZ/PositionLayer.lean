import OAI.RepresentationTheory.Saxl.PositionTensor

/-! Interchanging independent position blocks with the two paired-letter layers.
This is a coordinate identity; it says nothing about cyclic generation. -/
namespace HSTZ
open scoped TensorProduct

/-- Combining letter layers commutes with concatenating independent positions. -/
theorem wordTensor_positionProduct {n a b d f : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (ar : OAI.Saxl.WordSpace a d) (ac : OAI.Saxl.WordSpace a f)
    (br : OAI.Saxl.WordSpace b d) (bc : OAI.Saxl.WordSpace b f) :
    OAI.Saxl.wordTensor n d f
      (OAI.Saxl.positionProduct e ar br ⊗ₜ[ℂ] OAI.Saxl.positionProduct e ac bc) =
    OAI.Saxl.positionProduct e (OAI.Saxl.wordTensor a d f (ar ⊗ₜ[ℂ] ac))
      (OAI.Saxl.wordTensor b d f (br ⊗ₜ[ℂ] bc)) := by
  funext w
  simp only [OAI.Saxl.wordTensor_tmul,OAI.Saxl.positionProduct]
  change (ar (fun i => (finProdFinEquiv.symm (w (e.symm (Sum.inl i)))).1) *
    br (fun i => (finProdFinEquiv.symm (w (e.symm (Sum.inr i)))).1)) *
    (ac (fun i => (finProdFinEquiv.symm (w (e.symm (Sum.inl i)))).2) *
    bc (fun i => (finProdFinEquiv.symm (w (e.symm (Sum.inr i)))).2)) =
    (ar (fun i => (finProdFinEquiv.symm (w (e.symm (Sum.inl i)))).1) *
    ac (fun i => (finProdFinEquiv.symm (w (e.symm (Sum.inl i)))).2)) *
    (br (fun i => (finProdFinEquiv.symm (w (e.symm (Sum.inr i)))).1) *
    bc (fun i => (finProdFinEquiv.symm (w (e.symm (Sum.inr i)))).2))
  exact mul_mul_mul_comm _ _ _ _

end HSTZ
#print axioms HSTZ.wordTensor_positionProduct
