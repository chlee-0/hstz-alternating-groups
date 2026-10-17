import HSTZ.WitnessNativeAttachment

/-! Signed average over the canonical attachment column group. Reuses
`polytabloid_alternating` and the `signed_average_staircase` strategy from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0), with the asymmetric carriers.
No repeated-column identification or target support is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

/-- Unsigned first-layer average over the canonical column group. -/
def witnessAttachmentRowAverage (b delta : ℕ) :
    WordSpace (witnessAttachment b delta).card ((witnessAttachment b delta).transpose.colLen 0) := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  exact ∑ g : columnGroup (witnessCanonicalAttachment b delta),
    wordRep _ _ g.val (polytabloid (transposeTableau (witnessCanonicalAttachment b delta)))

/-- Signed full diagonal average, before any target contraction. -/
def witnessAttachmentSignedAverage (b delta : ℕ) :
    WordSpace (witnessAttachment b delta).card
      ((witnessAttachment b delta).transpose.colLen 0 * (witnessAttachment b delta).colLen 0) := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  exact ∑ g : columnGroup (witnessCanonicalAttachment b delta),
    signC g.val • wordRep _ _ g.val (witnessCanonicalAttachmentPair b delta)

theorem witnessAttachmentSignedAverage_tensor (b delta : ℕ) :
    witnessAttachmentSignedAverage b delta = wordTensor _ _ _
      (witnessAttachmentRowAverage b delta ⊗ₜ[ℂ] polytabloid (witnessCanonicalAttachment b delta)) := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  unfold witnessAttachmentSignedAverage witnessAttachmentRowAverage
  rw [TensorProduct.sum_tmul,map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  unfold witnessCanonicalAttachmentPair
  rw [← wordTensor_equivariant]
  change signC g.val • wordTensor _ _ _
    (wordRep _ _ g.val (polytabloid (transposeTableau (witnessCanonicalAttachment b delta))) ⊗ₜ[ℂ]
      wordRep _ _ g.val (polytabloid (witnessCanonicalAttachment b delta))) = _
  rw [polytabloid_alternating _ g,TensorProduct.tmul_smul,map_smul,
    smul_smul,signC_mul_self,one_smul]

/-- The signed diagonal average transforms by the sign character of the
canonical column group. -/
theorem witnessAttachmentSignedAverage_alternating (b delta : ℕ)
    (g : columnGroup (witnessCanonicalAttachment b delta)) :
    wordRep _ _ g.val (witnessAttachmentSignedAverage b delta) =
      signC g.val • witnessAttachmentSignedAverage b delta := by
  classical
  have he := congrArg (fun L : Module.End ℂ
    (WordSpace (witnessAttachment b delta).card
      ((witnessAttachment b delta).transpose.colLen 0 * (witnessAttachment b delta).colLen 0)) =>
    L (witnessCanonicalAttachmentPair b delta)) (columnAlt_left (witnessCanonicalAttachment b delta) g)
  simpa only [Module.End.mul_apply,columnAlt,LinearMap.sum_apply,LinearMap.smul_apply,
    witnessAttachmentSignedAverage] using he

theorem witnessAttachmentRowAverage_coefficient (b delta : ℕ) :
    witnessAttachmentRowAverage b delta
      (rowWord (transposeTableau (witnessCanonicalAttachment b delta))) =
      (Nat.card (columnGroup (witnessCanonicalAttachment b delta)) : ℂ) := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  have hf (g : columnGroup (witnessCanonicalAttachment b delta)) :
      rowWord (transposeTableau (witnessCanonicalAttachment b delta)) ∘ g.val =
        rowWord (transposeTableau (witnessCanonicalAttachment b delta)) := by
    funext i
    apply Fin.ext
    exact g.property i
  unfold witnessAttachmentRowAverage
  simp only [Finset.sum_apply]
  change (∑ g : columnGroup (witnessCanonicalAttachment b delta),
    polytabloid (transposeTableau (witnessCanonicalAttachment b delta))
      (rowWord (transposeTableau (witnessCanonicalAttachment b delta)) ∘ g.val)) = _
  simp only [hf,polytabloid_rowWord,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Nat.card_eq_fintype_card]

theorem witnessAttachmentSignedAverage_coefficient (b delta : ℕ) :
    witnessAttachmentSignedAverage b delta
      (mergeWords (rowWord (transposeTableau (witnessCanonicalAttachment b delta)))
        (rowWord (witnessCanonicalAttachment b delta))) =
      (Nat.card (columnGroup (witnessCanonicalAttachment b delta)) : ℂ) := by
  rw [witnessAttachmentSignedAverage_tensor,wordTensor_tmul,splitLeft_merge,splitRight_merge,
    witnessAttachmentRowAverage_coefficient,polytabloid_rowWord,mul_one]

theorem witnessAttachmentSignedAverage_ne_zero (b delta : ℕ) :
    witnessAttachmentSignedAverage b delta ≠ 0 := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  intro hz
  have hc := witnessAttachmentSignedAverage_coefficient b delta
  rw [hz] at hc
  have hn : (Nat.card (columnGroup (witnessCanonicalAttachment b delta)) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact hn hc.symm

theorem witnessAttachmentSignedAverage_mem (b delta : ℕ) :
    witnessAttachmentSignedAverage b delta ∈ (witnessCanonicalAttachmentCyclic b delta).toSubmodule := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  unfold witnessAttachmentSignedAverage
  apply Submodule.sum_mem
  intro g hg
  exact Submodule.smul_mem _ _ (orbit_mem_cyclicSpan _ _ g.val)

/-- The first average lies in the Specht carrier of the transposed attachment. -/
theorem witnessAttachmentRowAverage_mem (b delta : ℕ) :
    witnessAttachmentRowAverage b delta ∈ spechtSub (transposeTableau (witnessCanonicalAttachment b delta)) := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  unfold witnessAttachmentRowAverage
  apply Submodule.sum_mem
  intro g hg
  exact (spechtSub (transposeTableau (witnessCanonicalAttachment b delta))).apply_mem_toSubmodule
    g.val (mem_cyclic _ _)

/-- The unsigned average is invariant under the full column group. -/
theorem witnessAttachmentRowAverage_invariant (b delta : ℕ)
    (h : columnGroup (witnessCanonicalAttachment b delta)) :
    wordRep _ _ h.val (witnessAttachmentRowAverage b delta) = witnessAttachmentRowAverage b delta := by
  classical
  letI := Fintype.ofFinite (columnGroup (witnessCanonicalAttachment b delta))
  unfold witnessAttachmentRowAverage
  rw [map_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h)
    (fun g : columnGroup (witnessCanonicalAttachment b delta) =>
      wordRep _ _ g.val (polytabloid (transposeTableau (witnessCanonicalAttachment b delta))))
  change (∑ g : columnGroup (witnessCanonicalAttachment b delta),
    wordRep _ _ (h*g).val (polytabloid (transposeTableau (witnessCanonicalAttachment b delta)))) = _ at he
  simpa only [Subgroup.coe_mul,map_mul,Module.End.mul_apply] using he

/-- The signed encoded transport carries this nonzero average into
 the selected attachment cyclic space, with the full diagonal position action. -/
theorem witnessAttachmentMappedAverage_mem (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessNativeAttachmentMap k b delta hp.staircase_bound (witnessAttachmentSignedAverage b delta) ∈
      (witnessAttachmentCyclic k b delta hp).toSubmodule := by
  have hx := cyclicSpan_apply_mem (witnessNativeAttachmentMap k b delta hp.staircase_bound)
    (witnessCanonicalAttachmentPair b delta) (witnessAttachmentSignedAverage_mem b delta)
  rw [witnessNativeAttachmentMap_generator] at hx
  exact hx

theorem witnessAttachmentMappedAverage_ne_zero (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessNativeAttachmentMap k b delta hp.staircase_bound (witnessAttachmentSignedAverage b delta) ≠ 0 := by
  intro hz
  apply witnessAttachmentSignedAverage_ne_zero b delta
  apply witnessNativeAttachmentMap_injective k b delta hp.staircase_bound
  exact hz.trans (map_zero (witnessNativeAttachmentMap k b delta hp.staircase_bound).toLinearMap).symm

end
end HSTZ
#print axioms HSTZ.witnessAttachmentSignedAverage_tensor
#print axioms HSTZ.witnessAttachmentSignedAverage_alternating
#print axioms HSTZ.witnessAttachmentRowAverage_coefficient
#print axioms HSTZ.witnessAttachmentSignedAverage_coefficient
#print axioms HSTZ.witnessAttachmentSignedAverage_ne_zero
#print axioms HSTZ.witnessAttachmentSignedAverage_mem
#print axioms HSTZ.witnessAttachmentRowAverage_mem
#print axioms HSTZ.witnessAttachmentRowAverage_invariant
#print axioms HSTZ.witnessAttachmentMappedAverage_mem
#print axioms HSTZ.witnessAttachmentMappedAverage_ne_zero
