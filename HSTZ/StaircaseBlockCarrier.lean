import HSTZ.FinsuppAction
import HSTZ.IntertwiningCompat
import HSTZ.StaircaseBlock

/-! The label-orbit stabilizer carrier, transported to native position factors.
The induction source remains the selected-vector cyclic space. -/
namespace HSTZ
open scoped Classical TensorProduct

/-- Restrict the group of an intertwiner, preserving its linear map. -/
def pullbackIntertwiner {R G H V W : Type*} [CommRing R] [Monoid G] [Monoid H]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    {rho : Representation R G V} {sigma : Representation R G W}
    (phi : Representation.IntertwiningMap rho sigma) (f : H →* G) :
    Representation.IntertwiningMap (rho.comp f) (sigma.comp f) where
  toLinearMap := phi.toLinearMap
  isIntertwining' h := LinearMap.ext fun v => phi.map_action (f h) v

/-- The subgroup used by ordinary induction. -/
noncomputable abbrev staircaseLabelStabilizer (h s : ℕ) :=
  MulAction.stabilizer (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card))
    (labelOrbitBase (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card))
      (staircaseHighLabel h s))

theorem staircaseLabelStabilizer_eq (h s : ℕ) :
    staircaseLabelStabilizer h s =
      OAI.Saxl.sectorGroup (fun i => (OAI.Saxl.cutPositions h s i).isLeft = true) := by
  rw [staircaseLabelStabilizer,labelOrbitBase_stabilizer,staircaseHighLabel_stabilizer,
    cutSectorGroup_eq]

/-- The label-orbit stabilizer is the product of the two block groups. -/
noncomputable def staircaseLabelBlockEquiv (h s : ℕ) :
    (Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h s))) ≃* staircaseLabelStabilizer h s :=
  (positionBlockGroupEquiv (OAI.Saxl.cutPositions h s)).trans
    (MulEquiv.subgroupCongr (staircaseLabelStabilizer_eq h s).symm)

@[simp] theorem staircaseLabelBlockEquiv_val (h s : ℕ)
    (gh : Equiv.Perm (Fin (OAI.Saxl.staircase h).card) ×
      Equiv.Perm (Fin (OAI.Saxl.bandSize h s))) :
    (staircaseLabelBlockEquiv h s gh).val = sumPermHom (OAI.Saxl.cutPositions h s) gh := rfl

noncomputable def staircaseStabilizerEncoder (h s : ℕ) :=
  pullbackIntertwiner
    (encodedPairModelIntertwiner (OAI.Saxl.staircase (h+s)).card
      ((OAI.Saxl.staircase (h+s)).colLen 0) ((OAI.Saxl.staircase (h+s)).colLen 0))
    (staircaseLabelStabilizer h s).subtype

/-- Image of the ordinary-induction source under the encoder. -/
theorem staircaseLabel_factor_image (h s : ℕ) :
    (stabilizerCyclic (finsuppAction ℂ
      (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _)
      (labelOrbitBase (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card))
        (staircaseHighLabel h s)) (staircasePairCut h s)).map
      (encodedPairModelEquiv _ _ _).toLinearMap =
    (LinearMap.range (TensorProduct.mapIncl
      (cyclicSpan (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s))
      (cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h s)))).map
      (OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s)).toLinearMap := by
  have hi := cyclicSpan_image (staircaseStabilizerEncoder h s) (staircasePairCut h s)
  change (stabilizerCyclic _ _ (staircasePairCut h s)).map
      (encodedPairModelEquiv _ _ _).toLinearMap =
    cyclicSpan ((OAI.Saxl.wordRep _ _).comp (staircaseLabelStabilizer h s).subtype)
      (encodedPairModelEquiv _ _ _ (staircasePairCut h s)) at hi
  rw [encodedPair_staircaseCut,staircaseLabelStabilizer_eq] at hi
  exact hi.trans (staircaseCut_factor_range h s).symm

/-- Restricted encoding is a bijection between the cyclic carriers. -/
theorem staircaseStabilizerEncoder_cyclic_bijective (h s : ℕ) :
    Function.Bijective
      (cyclicImageMap (staircaseStabilizerEncoder h s) (staircasePairCut h s)) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact (encodedPairModelEquiv _ _ _).injective (congrArg Subtype.val he)
  · exact cyclicImageMap_surjective _ _

/-- Independent factor intertwiner back to the retained pair-word basis. -/
noncomputable def staircaseFactorToWords (h s : ℕ) :=
  (pullbackIntertwiner
    (encodedPairModelInverse (OAI.Saxl.staircase (h+s)).card
      ((OAI.Saxl.staircase (h+s)).colLen 0) ((OAI.Saxl.staircase (h+s)).colLen 0))
    (sumPermHom (OAI.Saxl.cutPositions h s))).comp
    ((positionTensorIntertwiner (OAI.Saxl.cutPositions h s)).comp
      (cyclicTensorInclusion (OAI.Saxl.wordRep _ _) (OAI.Saxl.wordRep _ _)
        (shiftedCoreWord h s) (bandPairWord h s)))

/-- Every factor tensor lands in the ordinary-induction source. -/
theorem staircaseFactorToWords_mem (h s : ℕ) (x :
    ↥(cyclicSpan (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s)) ⊗[ℂ]
    ↥(cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h s))) :
    staircaseFactorToWords h s x ∈ stabilizerCyclic
      (finsuppAction ℂ (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _)
      (labelOrbitBase (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card))
        (staircaseHighLabel h s)) (staircasePairCut h s) := by
  let inc := TensorProduct.mapIncl
    (cyclicSpan (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s))
    (cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h s))
  have he : OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s) (inc x) ∈
      (stabilizerCyclic (finsuppAction ℂ
        (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _)
        (labelOrbitBase (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card))
          (staircaseHighLabel h s)) (staircasePairCut h s)).map
        (encodedPairModelEquiv _ _ _).toLinearMap := by
    rw [staircaseLabel_factor_image]
    exact Submodule.mem_map.mpr ⟨inc x,⟨x,rfl⟩,rfl⟩
  obtain ⟨y,hy,hey⟩ := Submodule.mem_map.mp he
  have hf : staircaseFactorToWords h s x = y := by
    apply (encodedPairModelEquiv _ _ _).injective
    change encodedPairModelEquiv _ _ _ ((encodedPairModelEquiv _ _ _).symm
      (OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s) (inc x))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hey.symm
  rw [hf]
  exact hy

/-- Factor tensor and induction source, with the explicit product-group
identification of the stabilizer action. -/
noncomputable def staircaseFactorToStabilizer (h s : ℕ) :
    Representation.IntertwiningMap
      (independentTensor
        (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s)).toRepresentation
        (cyclicSubrepresentation (OAI.Saxl.wordRep _ _) (bandPairWord h s)).toRepresentation)
      (((cyclicSubrepresentation
        ((finsuppAction ℂ
          (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _).comp
          (staircaseLabelStabilizer h s).subtype) (staircasePairCut h s)).toRepresentation).comp
        (staircaseLabelBlockEquiv h s).toMonoidHom) where
  toLinearMap := (staircaseFactorToWords h s).toLinearMap.codRestrict _
    (staircaseFactorToWords_mem h s)
  isIntertwining' gh := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (staircaseFactorToWords h s).map_action gh x

/-- Bijective factor-to-stabilizer map, without a dimension comparison. -/
theorem staircaseFactorToStabilizer_bijective (h s : ℕ) :
    Function.Bijective (staircaseFactorToStabilizer h s) := by
  constructor
  · intro x y he
    have hword := congrArg Subtype.val he
    have henc := (encodedPairModelEquiv _ _ _).symm.injective hword
    have hpos := (OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s)).injective henc
    exact cyclicTensorInclusion_injective (OAI.Saxl.wordRep _ _) (OAI.Saxl.wordRep _ _)
      (shiftedCoreWord h s) (bandPairWord h s) hpos
  · intro y
    have he' : encodedPairModelEquiv _ _ _ y.val ∈
      (LinearMap.range (TensorProduct.mapIncl
        (cyclicSpan (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s))
        (cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h s)))).map
          (OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s)).toLinearMap := by
      rw [← staircaseLabel_factor_image]
      exact Submodule.mem_map.mpr ⟨y.val,y.property,rfl⟩
    obtain ⟨z,⟨x,hx⟩,hz⟩ := Submodule.mem_map.mp he'
    refine ⟨x,?_⟩
    apply Subtype.ext
    have hprod : OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s)
        (TensorProduct.mapIncl
          (cyclicSpan (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s))
          (cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h s)) x) =
        encodedPairModelEquiv _ _ _ y.val := by
      rw [hx]
      exact hz
    change (encodedPairModelEquiv _ _ _).symm
      (OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s)
        (TensorProduct.mapIncl
          (cyclicSpan (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s))
          (cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h s)) x)) = y.val
    rw [hprod,LinearEquiv.symm_apply_apply]

end HSTZ
#print axioms HSTZ.staircaseLabelStabilizer_eq
#print axioms HSTZ.staircaseLabel_factor_image
#print axioms HSTZ.staircaseStabilizerEncoder_cyclic_bijective

#print axioms HSTZ.staircaseLabelBlockEquiv_val

#print axioms HSTZ.staircaseFactorToWords_mem
#print axioms HSTZ.staircaseFactorToStabilizer_bijective
