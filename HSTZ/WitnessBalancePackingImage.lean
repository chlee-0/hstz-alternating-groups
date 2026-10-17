import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePackingRowsSquare

/-! The image of the tensor product of all projected factors equals the projected
range `range (P J)`. The proof goes through physical two-letter coordinates and a
nonzero normalization constant defined in this file. Uses declarations from OpenAI's
`math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
  (z : Tableau n (witnessDiagram k b delta hk))

def witnessBalancePackingNormalization : ℂ :=
  ∏ a : witnessBalancePackingLabelIndex k delta,
    (witnessBalancePackingBaseCoefficient hk z a.val)⁻¹

theorem witnessBalancePackingNormalization_ne_zero :
    witnessBalancePackingNormalization hk z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  exact inv_ne_zero (witnessBalancePackingBaseCoefficient_ne_zero hk z a.val)

/-- Equality of linear maps, keeping the physical positions and both decoded
letters. The two sides differ by the square of the normalization constant, which
need not be `1`. -/
theorem witnessBalancePackingRowsSquareWords_physical (hd : delta ≤ 1) :
    witnessBalancePackingRowsSquareWords hk z hd=
      (witnessBalancePackingNormalization hk z)^2 •
        ((witnessBalancePackingSquareWords hk z hd).comp (witnessBalancePackingSquareInterchange hk z)) := by
  apply TensorProduct.ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro y
  change witnessBalancePackingRowsSquareWords hk z hd
      (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)=
    (witnessBalancePackingNormalization hk z)^2 •
      witnessBalancePackingSquareWords hk z hd
        (witnessBalancePackingSquareInterchange hk z
          (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y))
  rw [witnessBalancePackingSquareInterchange_tprod]
  funext w
  change wordTensor _ _ _
    (TensorProduct.map (witnessBalancePackingRowsWords hk z hd) (witnessBalancePackingRowsWords hk z hd)
      (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)) w=
    (witnessBalancePackingNormalization hk z)^2 *
      witnessBalancePackingSquareWords hk z hd (PiTensorProduct.tprod ℂ (fun a => x a ⊗ₜ[ℂ] y a)) w
  rw [TensorProduct.map_tmul,wordTensor_tmul,
    witnessBalancePackingRowsWords_tprod_value,witnessBalancePackingRowsWords_tprod_value,
    witnessBalancePackingSquareWords_tprod_tmul_value]
  have hL (a : witnessBalancePackingLabelIndex k delta) :
      splitLeft (witnessBalancePackingPairRestriction hk z hd w a)=
        leftWord (witnessBalanceComponentCut hk z a.val) (splitLeft w) := rfl
  have hR (a : witnessBalancePackingLabelIndex k delta) :
      splitRight (witnessBalancePackingPairRestriction hk z hd w a)=
        leftWord (witnessBalanceComponentCut hk z a.val) (splitRight w) := rfl
  simp_rw [hL,hR,div_eq_mul_inv,Finset.prod_mul_distrib]
  change ((∏ a, (x a).val (leftWord (witnessBalanceComponentCut hk z a.val) (splitLeft w)))*
      witnessBalancePackingNormalization hk z)*
    ((∏ a, (y a).val (leftWord (witnessBalanceComponentCut hk z a.val) (splitRight w)))*
      witnessBalancePackingNormalization hk z)=
    (witnessBalancePackingNormalization hk z)^2 *
      ((∏ a, (x a).val (leftWord (witnessBalanceComponentCut hk z a.val) (splitLeft w)))*
        (∏ a, (y a).val (leftWord (witnessBalanceComponentCut hk z a.val) (splitRight w))))
  ring

/-- The same comparison with the coordinate selector applied after the source
interchange. -/
theorem witnessBalancePackingRowsProjectedSquareWords_physical (hd : delta ≤ 1) :
    witnessBalancePackingRowsProjectedSquareWords hk z hd=
      (witnessBalancePackingNormalization hk z)^2 •
        ((witnessBalancePackingProjectedSquareWords hk z hd).comp (witnessBalancePackingSquareInterchange hk z)) := by
  apply LinearMap.ext
  intro q
  change coordinateProjection (witnessBalanceComponentWords hk z
    (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
    (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk))
      (witnessBalancePackingRowsSquareWords hk z hd q)=
    (witnessBalancePackingNormalization hk z)^2 •
      witnessBalancePackingProjectedSquareWords hk z hd (witnessBalancePackingSquareInterchange hk z q)
  rw [witnessBalancePackingRowsSquareWords_physical,LinearMap.smul_apply,LinearMap.comp_apply,map_smul,
    witnessBalancePackingSquareWords_projection]

theorem witnessBalancePackingRowsProjectedSquareWords_range_local (hd : delta ≤ 1) :
    (witnessBalancePackingRowsProjectedSquareWords hk z hd).range=
      (witnessBalancePackingProjectedSquareWords hk z hd).range := by
  rw [witnessBalancePackingRowsProjectedSquareWords_physical,
    LinearMap.range_smul _ _ (pow_ne_zero 2 (witnessBalancePackingNormalization_ne_zero hk z)),
    LinearMap.range_comp,LinearMap.range_eq_top.mpr (witnessBalancePackingSquareInterchange_surjective hk z),
    Submodule.map_top]

/-- The image of the tensor product of all projected factors equals the projected
range, inside the same H word space. -/
theorem witnessBalancePackingTensorImage_eq_original (hd : delta ≤ 1) :
    (witnessBalancePackingTensorImage hk z hd).toSubmodule=
      (witnessBalanceProjectedRange hk z
        (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
        (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toSubmodule := by
  change (witnessBalancePackingTensorWords hk z hd).range=_
  calc
    _=(witnessBalancePackingProjectedSquareWords hk z hd).range :=
      (witnessBalancePackingProjectedSquareWords_range hk z hd).symm
    _=(witnessBalancePackingRowsProjectedSquareWords hk z hd).range :=
      (witnessBalancePackingRowsProjectedSquareWords_range_local hk z hd).symm
    _=_ := witnessBalancePackingRowsProjectedSquareWords_range hk z hd

/-- The tensor map of all factors into the projected range `range (P J)`,
equivariant for the H action. -/
def witnessBalancePackingTensorProjectedMap (hd : delta ≤ 1) : Representation.IntertwiningMap
    (witnessBalancePackingTensorHAction hk z hd)
    (witnessBalanceProjectedRange hk z
      (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toRepresentation where
  toLinearMap := (witnessBalancePackingTensorWords hk z hd).codRestrict _ (by
    intro q
    rw [← witnessBalancePackingTensorImage_eq_original hk z hd]
    exact ⟨q,rfl⟩)
  isIntertwining' g := LinearMap.ext fun q =>
    Subtype.ext ((witnessBalancePackingTensorHIntertwiner hk z hd).map_action g q)

theorem witnessBalancePackingTensorProjectedMap_bijective (hd : delta ≤ 1) :
    Function.Bijective (witnessBalancePackingTensorProjectedMap hk z hd) := by
  constructor
  · intro x y h
    apply witnessBalancePackingTensorWords_injective hk z hd
    exact congrArg Subtype.val h
  · rintro ⟨v,hv⟩
    rw [← witnessBalancePackingTensorImage_eq_original hk z hd] at hv
    obtain ⟨q,hq⟩ := hv
    exact ⟨q,Subtype.ext hq⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingNormalization
#print axioms HSTZ.witnessBalancePackingNormalization_ne_zero
#print axioms HSTZ.witnessBalancePackingRowsSquareWords_physical
#print axioms HSTZ.witnessBalancePackingRowsProjectedSquareWords_physical
#print axioms HSTZ.witnessBalancePackingRowsProjectedSquareWords_range_local
#print axioms HSTZ.witnessBalancePackingTensorImage_eq_original
#print axioms HSTZ.witnessBalancePackingTensorProjectedMap
#print axioms HSTZ.witnessBalancePackingTensorProjectedMap_bijective
