import HSTZ.WitnessBalancePackingRows

/-! Finite interchange of two independent layers on the original C_a. Uses
`PiTensorProduct.map₂` and `TensorProduct.exists_sum_tmul_eq`, building on
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
  (z : Tableau n (witnessDiagram k b delta hk))

def witnessBalancePackingSquareInterchange :
    (witnessBalancePackingRowsSpace hk z ⊗[ℂ] witnessBalancePackingRowsSpace hk z) →ₗ[ℂ]
      witnessBalancePackingSquareSpace hk z :=
  TensorProduct.lift (PiTensorProduct.map₂ (fun a : witnessBalancePackingLabelIndex k delta =>
    TensorProduct.mk ℂ (witnessBalanceComponentRows hk z a.val).toSubmodule
      (witnessBalanceComponentRows hk z a.val).toSubmodule))

theorem witnessBalancePackingSquareInterchange_tprod
    (x y : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceComponentRows hk z a.val).toSubmodule) :
    witnessBalancePackingSquareInterchange hk z
      (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)=
      PiTensorProduct.tprod ℂ (fun a => x a ⊗ₜ[ℂ] y a) := by
  rw [witnessBalancePackingSquareInterchange,TensorProduct.lift.tmul,
    PiTensorProduct.map₂_tprod_tprod]
  rfl

/-- Onto all independent local squares. A finite `tmul` expansion is needed because
pure repeated tensors do not span the full local square. Empty sums are allowed. -/
theorem witnessBalancePackingSquareInterchange_surjective :
    Function.Surjective (witnessBalancePackingSquareInterchange hk z) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_iff'.mpr
  intro q
  induction q using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    apply Submodule.smul_mem
    have hx : ∀ a : witnessBalancePackingLabelIndex k delta,
        ∃ (m : ℕ) (u v : Fin m → (witnessBalanceComponentRows hk z a.val).toSubmodule),
          x a=∑ j, u j ⊗ₜ[ℂ] v j := fun a => TensorProduct.exists_sum_tmul_eq (x a)
    choose m u v hx using hx
    have he : x=(fun a => ∑ j, u a j ⊗ₜ[ℂ] v a j) := funext hx
    rw [he,MultilinearMap.map_sum]
    apply Submodule.sum_mem
    intro t _
    refine ⟨PiTensorProduct.tprod ℂ (fun a => u a (t a)) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun a => v a (t a)),?_⟩
    exact witnessBalancePackingSquareInterchange_tprod hk z _ _
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingSquareInterchange
#print axioms HSTZ.witnessBalancePackingSquareInterchange_tprod
#print axioms HSTZ.witnessBalancePackingSquareInterchange_surjective
