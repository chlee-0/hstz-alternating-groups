import HSTZ.IntertwiningCompat
import HSTZ.WitnessAttachmentSignLine
import OAI.RepresentationTheory.Saxl.DominatedQuotient

/-! Transport of the sign-twisted attachment average. Uses the orthogonal
projection, inverse sign map and `wordTensor` interfaces adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). The averaged vector itself is
kept; this is not a character or dimension argument, and it does not assert
attachment target support. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

/-- First-layer inverse, extended equivariantly by the projection. -/
def witnessAttachmentAmbientInverse (b delta : ℕ) :
    Representation.IntertwiningMap
      (signTwist (wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).transpose.colLen 0)))
      (wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).colLen 0)) :=
  (spechtInclusion (witnessCanonicalAttachment b delta)).comp
    ((spechtSignInverseMap (witnessCanonicalAttachment b delta)).comp
      (signTwistMap (subrepProject (spechtSub (transposeTableau (witnessCanonicalAttachment b delta)))
        (fun _ hx => cyclic_star _ (polytabloid_real _) hx))))

theorem witnessAttachmentAmbientInverse_average (b delta : ℕ) :
    witnessAttachmentAmbientInverse b delta (witnessAttachmentRowAverage b delta) =
      (witnessAttachmentSignAverage b delta).val := by
  change (spechtSignInverseMap (witnessCanonicalAttachment b delta)
    (subrepProject (spechtSub (transposeTableau (witnessCanonicalAttachment b delta)))
      (fun _ hx => cyclic_star _ (polytabloid_real _) hx) (witnessAttachmentAverageSpecht b delta).val)).val = _
  erw [subrepProject_subtype]
  rfl

/-- The intrinsic sign stays on the full diagonal mixed action, and the first
layer is changed. Neither the positions nor the second layer are exchanged. -/
def witnessAttachmentTensorAnti (b delta : ℕ) :
    Representation.IntertwiningMap
      (signTwist ((wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).transpose.colLen 0)).tprod
        (wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).colLen 0))))
      ((wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).colLen 0)).tprod
        (wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).colLen 0))) where
  toLinearMap := TensorProduct.map (witnessAttachmentAmbientInverse b delta).toLinearMap LinearMap.id
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    have he : (TensorProduct.map (witnessAttachmentAmbientInverse b delta).toLinearMap LinearMap.id).comp
        (signTwist ((wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).transpose.colLen 0)).tprod
          (wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).colLen 0))) g) =
        (((wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).colLen 0)).tprod
          (wordRep (witnessAttachment b delta).card ((witnessAttachment b delta).colLen 0))) g).comp
            (TensorProduct.map (witnessAttachmentAmbientInverse b delta).toLinearMap LinearMap.id) := by
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change TensorProduct.map (witnessAttachmentAmbientInverse b delta).toLinearMap LinearMap.id
        (signC g • (wordRep _ _ g x ⊗ₜ[ℂ] wordRep _ _ g y)) =
          wordRep _ _ g (witnessAttachmentAmbientInverse b delta x) ⊗ₜ[ℂ] wordRep _ _ g y
      rw [TensorProduct.smul_tmul',TensorProduct.map_tmul,LinearMap.id_apply]
      exact congrArg (fun u => u ⊗ₜ[ℂ] wordRep _ _ g y)
        ((witnessAttachmentAmbientInverse b delta).map_action g x)
    exact DFunLike.congr_fun he z

def witnessAttachmentRepeatedMap (b delta : ℕ) :
    Representation.IntertwiningMap
      (signTwist (wordRep (witnessAttachment b delta).card
        ((witnessAttachment b delta).transpose.colLen 0 * (witnessAttachment b delta).colLen 0)))
      (wordRep (witnessAttachment b delta).card
        ((witnessAttachment b delta).colLen 0 * (witnessAttachment b delta).colLen 0)) :=
  (wordTensorIntertwiner _ _ _).comp ((witnessAttachmentTensorAnti b delta).comp
    (signTwistMap (HSTZ.wordTensorInverse _ _ _)))

theorem witnessAttachmentRepeatedMap_tensor (b delta : ℕ)
    (x : WordSpace (witnessAttachment b delta).card ((witnessAttachment b delta).transpose.colLen 0))
    (y : WordSpace (witnessAttachment b delta).card ((witnessAttachment b delta).colLen 0)) :
    witnessAttachmentRepeatedMap b delta (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) =
      wordTensor _ _ _ (witnessAttachmentAmbientInverse b delta x ⊗ₜ[ℂ] y) := by
  change wordTensor _ _ _ (TensorProduct.map (witnessAttachmentAmbientInverse b delta).toLinearMap LinearMap.id
    ((wordTensor _ _ _).symm (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply,TensorProduct.map_tmul,LinearMap.id_apply]
  rfl

/-- The repeated canonical generator in its alphabet. -/
def witnessAttachmentRepeatedWord (b delta : ℕ) :
    WordSpace (witnessAttachment b delta).card
      ((witnessAttachment b delta).colLen 0 * (witnessAttachment b delta).colLen 0) :=
  wordTensor _ _ _ (polytabloid (witnessCanonicalAttachment b delta) ⊗ₜ[ℂ]
    polytabloid (witnessCanonicalAttachment b delta))

theorem witnessAttachmentRepeatedMap_average (b delta : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ witnessAttachmentRepeatedMap b delta (witnessAttachmentSignedAverage b delta) =
      c • witnessAttachmentRepeatedWord b delta := by
  obtain ⟨c,hc0,hc⟩ := witnessAttachmentSignAverage_line b delta
  refine ⟨c,hc0,?_⟩
  rw [witnessAttachmentSignedAverage_tensor,witnessAttachmentRepeatedMap_tensor,
    witnessAttachmentAmbientInverse_average,hc,TensorProduct.smul_tmul,TensorProduct.tmul_smul,map_smul]
  rfl

/-- Inclusion in the image of the original sign-twisted mixed cyclic space.
It is not claimed that the whole image equals this smaller cyclic space. -/
theorem witnessAttachmentRepeatedWord_mem_image (b delta : ℕ) :
    witnessAttachmentRepeatedWord b delta ∈
      (cyclicSpan (signTwist (wordRep _ _)) (witnessCanonicalAttachmentPair b delta)).map
        (witnessAttachmentRepeatedMap b delta).toLinearMap := by
  obtain ⟨c,hc0,hc⟩ := witnessAttachmentRepeatedMap_average b delta
  have hm : c • witnessAttachmentRepeatedWord b delta ∈
      (cyclicSpan (signTwist (wordRep _ _)) (witnessCanonicalAttachmentPair b delta)).map
        (witnessAttachmentRepeatedMap b delta).toLinearMap := by
    rw [← hc]
    apply Submodule.mem_map.mpr
    refine ⟨witnessAttachmentSignedAverage b delta,?_,rfl⟩
    classical
    letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
    unfold witnessAttachmentSignedAverage
    apply Submodule.sum_mem
    intro g hg
    exact orbit_mem_cyclicSpan (signTwist (wordRep _ _)) _ g.val
  exact (Submodule.smul_mem_iff _ hc0).mp hm

end
end HSTZ
#print axioms HSTZ.witnessAttachmentAmbientInverse
#print axioms HSTZ.witnessAttachmentAmbientInverse_average
#print axioms HSTZ.witnessAttachmentTensorAnti
#print axioms HSTZ.witnessAttachmentRepeatedMap
#print axioms HSTZ.witnessAttachmentRepeatedMap_tensor
#print axioms HSTZ.witnessAttachmentRepeatedMap_average
#print axioms HSTZ.witnessAttachmentRepeatedWord_mem_image
