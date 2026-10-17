import HSTZ.PositionBlock
import HSTZ.PositionLayer
import HSTZ.StaircaseFilter

/-! Core/band position factors of the staircase cut.
Vector identities and cyclic ranges alone give no local constituent support. -/
namespace HSTZ
open scoped Classical TensorProduct

/-- The shifted smaller-staircase tensor vector. -/
noncomputable def shiftedCoreWord (h s : ℕ) :
    OAI.Saxl.WordSpace (OAI.Saxl.staircase h).card
      ((OAI.Saxl.staircase (h+s)).colLen 0 * (OAI.Saxl.staircase (h+s)).colLen 0) :=
  OAI.Saxl.wordTensor _ _ _
    (OAI.Saxl.letterLift (OAI.Saxl.highLetter h s) (OAI.Saxl.polytabloid (OAI.Saxl.stairRowTableau h)) ⊗ₜ[ℂ]
      OAI.Saxl.letterLift (OAI.Saxl.highLetter h s) (OAI.Saxl.polytabloid (OAI.Saxl.stairTableau h)))

noncomputable def bandPairWord (h s : ℕ) :
    OAI.Saxl.WordSpace (OAI.Saxl.bandSize h s)
      ((OAI.Saxl.staircase (h+s)).colLen 0 * (OAI.Saxl.staircase (h+s)).colLen 0) :=
  OAI.Saxl.wordTensor _ _ _ (OAI.Saxl.bandRowWord h s ⊗ₜ[ℂ] OAI.Saxl.bandColumnWord h s)

/-- Core/band position factorization, using the generic layer interchange. -/
theorem staircaseCut_positionTensor (h s : ℕ) :
    OAI.Saxl.sameHighProjection _ _ _ s (OAI.Saxl.staircaseWord (h+s)) =
    OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s)
      (shiftedCoreWord h s ⊗ₜ[ℂ] bandPairWord h s) := by
  rw [OAI.Saxl.staircase_cut_layers,OAI.Saxl.cutRowWord_factor,
    OAI.Saxl.cutColumnWord_factor,OAI.Saxl.positionTensor_tmul]
  exact wordTensor_positionProduct (OAI.Saxl.cutPositions h s) _ _ _ _

/-- The selected pair generator maps to the core/band tensor product. -/
theorem staircasePairCut_positionTensor (h s : ℕ) :
    encodedPairModelEquiv _ _ _ (staircasePairCut h s) =
    OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s)
      (shiftedCoreWord h s ⊗ₜ[ℂ] bandPairWord h s) := by
  rw [encodedPair_staircaseCut,staircaseCut_positionTensor]

/-- The range of the factor inclusion identifies the selected stabilizer cyclic
space. -/
theorem staircaseCut_factor_range (h s : ℕ) :
    (LinearMap.range (TensorProduct.mapIncl
      (cyclicSpan (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s))
      (cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h s)))).map
        (OAI.Saxl.positionTensor (OAI.Saxl.cutPositions h s)).toLinearMap =
    cyclicSpan ((OAI.Saxl.wordRep _ _).comp
      (OAI.Saxl.sectorGroup (fun i => (OAI.Saxl.cutPositions h s i).isLeft = true)).subtype)
      (OAI.Saxl.sameHighProjection _ _ _ s (OAI.Saxl.staircaseWord (h+s))) := by
  rw [positionTensor_factor_range,blockSpan_eq_sectorSpan]
  rw [staircaseCut_positionTensor,OAI.Saxl.positionTensor_tmul]

/-- The sector is the geometric high-position stabilizer. -/
theorem cutSectorGroup_eq (h s : ℕ) :
    OAI.Saxl.sectorGroup (fun i => (OAI.Saxl.cutPositions h s i).isLeft = true) =
    OAI.Saxl.sectorGroup (OAI.Saxl.stairHigh h s) := by
  congr 1
  funext i
  exact propext (OAI.Saxl.cutPositions_high h s i)


/-- The Bool-label stabilizer is the geometric high-position group. -/
theorem staircaseHighLabel_stabilizer (h s : ℕ) :
    MulAction.stabilizer (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card))
      (staircaseHighLabel h s) = OAI.Saxl.sectorGroup (OAI.Saxl.stairHigh h s) := by
  ext g
  change (g • staircaseHighLabel h s = staircaseHighLabel h s) ↔
    (∀ i, OAI.Saxl.stairHigh h s (g i) ↔ OAI.Saxl.stairHigh h s i)
  constructor
  · intro hg i
    have he := congrArg (fun w => w.letters (g i)) hg
    change decide (OAI.Saxl.stairHigh h s (g⁻¹ (g i))) =
      decide (OAI.Saxl.stairHigh h s (g i)) at he
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at he
    exact (decide_eq_decide.mp he).symm
  · intro hg
    apply PositionWord.ext
    intro i
    change decide (OAI.Saxl.stairHigh h s (g⁻¹ i)) = decide (OAI.Saxl.stairHigh h s i)
    have he : OAI.Saxl.stairHigh h s (g⁻¹ i) ↔ OAI.Saxl.stairHigh h s i := by
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hg (g⁻¹ i)).symm
    exact decide_eq_decide.mpr he

end HSTZ
#print axioms HSTZ.staircaseCut_positionTensor
#print axioms HSTZ.staircasePairCut_positionTensor
#print axioms HSTZ.staircaseCut_factor_range
#print axioms HSTZ.cutSectorGroup_eq
#print axioms HSTZ.staircaseHighLabel_stabilizer
