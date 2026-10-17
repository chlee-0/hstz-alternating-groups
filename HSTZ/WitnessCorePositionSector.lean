import HSTZ.WitnessCoreComplementProduct

/-! Normalization of the original core-position group, and block support for all vectors.
Reuses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No transitive sector family, induced target, full witness or kappa statement is proved here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct
variable (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
  (z : Tableau n (witnessDiagram k b delta hk))

/-- The binary-cut block predicate is exactly the original core range. -/
theorem witnessCorePosition_sectorGroup_eq :
    sectorGroup (fun i => (witnessBinaryCut k b delta hk z i).isLeft=true) =
      sectorGroup (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) := by
  apply congrArg sectorGroup
  funext i
  exact propext (witnessBinaryCut_mask k b delta hk z i)

/-- Every original core-range stabilizer is an independent block move. -/
theorem witnessCorePosition_group_iff (g : Equiv.Perm (Fin n)) :
    g∈sectorGroup (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) ↔
      ∃ gh, sumPermHom (witnessBinaryCut k b delta hk z) gh=g := by
  rw [← witnessCorePosition_sectorGroup_eq k b delta hk z]
  exact sumPermHom_sector_iff _ _

/-- Product-group identification with the original core-range group. -/
def witnessCorePositionGroupEquiv :
    (Equiv.Perm (Fin (staircase (k-2)).card) ×
      Equiv.Perm (Fin (witnessComplementSize k b delta))) ≃*
      sectorGroup (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) :=
  (positionBlockGroupEquiv (witnessBinaryCut k b delta hk z)).trans
    (MulEquiv.subgroupCongr (witnessCorePosition_sectorGroup_eq k b delta hk z))

theorem witnessCorePositionGroupEquiv_val (gh : Equiv.Perm (Fin (staircase (k-2)).card) ×
    Equiv.Perm (Fin (witnessComplementSize k b delta))) :
    (witnessCorePositionGroupEquiv k b delta hk z gh).val =
      sumPermHom (witnessBinaryCut k b delta hk z) gh := rfl

/-- All supported positions of the product generator have the core mask. -/
theorem witnessCoreComplement_product_support
    (w : Fin n → Fin ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0))
    (hw : witnessCoreComplementProduct k b delta hk z w≠0) :
    ∀ i, (witnessRowMarked k b (splitLeft w i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) ∧
      (witnessColumnMarked k (splitRight w i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) := by
  apply witness_filtered_core_positions k b delta hk z w
  rw [witness_filtered_core_factor]
  change witnessRotationPhase k b delta hk z * witnessCoreComplementProduct k b delta hk z w≠0
  exact mul_ne_zero (witnessRotationPhase_ne_zero k b delta hk z) hw

/-- Every vector in the independent block carrier remains in the same sector. -/
theorem witnessCoreComplement_block_support
    (x : witnessCoreComplementBlockCyclic k b delta hk z)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0)) (hx : x.val w≠0) :
    ∀ i, (witnessRowMarked k b (splitLeft w i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) ∧
      (witnessColumnMarked k (splitRight w i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) := by
  let P := fun w : Fin n → Fin ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) =>
    ∀ i, (witnessRowMarked k b (splitLeft w i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) ∧
      (witnessColumnMarked k (splitRight w i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk z))
  have hgen : (positionTensorIntertwiner (witnessBinaryCut k b delta hk z))
      (witnessEmbeddedCorePair k b delta hk ⊗ₜ[ℂ] witnessComplementPairWord k b delta hk z) =
      witnessCoreComplementProduct k b delta hk z := positionTensor_tmul _ _ _
  have hm := x.property
  change x.val∈cyclicSpan _ _ at hm
  rw [hgen] at hm
  have hvanish : ∀ v : WordSpace n
      ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0),
      v∈cyclicSpan ((wordRep n
        ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0)).comp
        (sumPermHom (witnessBinaryCut k b delta hk z)))
        (witnessCoreComplementProduct k b delta hk z) → ∀ a, ¬P a → v a=0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨gh,rfl⟩ := hy
      intro a ha
      by_contra hn
      let g := sumPermHom (witnessBinaryCut k b delta hk z) gh
      have hg : ∀ i, (g i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk z) :=
        (witnessCorePosition_group_iff k b delta hk z g).mpr ⟨gh,rfl⟩
      have h := witnessCoreComplement_product_support k b delta hk z (a ∘ g) hn
      apply ha
      intro i
      have hi := h (g.symm i)
      have hgi := (hg (g.symm i)).symm
      simpa only [splitLeft,splitRight,Function.comp_apply,Equiv.apply_symm_apply] using
        And.intro (hi.1.trans hgi) (hi.2.trans hgi)
    | zero => intro a ha; rfl
    | add y v hy hv iy iv =>
      intro a ha
      change y a+v a=0
      rw [iy a ha,iv a ha,add_zero]
    | smul c y hy iy => intro a ha; change c*y a=0; rw [iy a ha,mul_zero]
  by_contra hn
  exact hx (hvanish x.val hm w hn)
/-- The nonzero two-sign phase does not change the full orbit span. -/
theorem witnessCoreComplement_filtered_cyclic :
    cyclicSpan (wordRep n ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0))
      (witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk z)) =
        (witnessCoreComplementCyclic k b delta hk z).toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    rw [witness_filtered_core_factor]
    dsimp only
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    have he : witnessCoreComplementProduct k b delta hk z =
        witnessRotationPhase k b delta hk z •
          witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk z) := by
      rw [witness_filtered_core_factor,smul_smul,witnessRotationPhase_sq,one_smul]
    rw [he]
    dsimp only
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g,rfl⟩)

/-- The mask projection has exactly the full product cyclic image. -/
theorem witnessCoreComplement_projection_image :
    (cyclic (wordRep n ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0))
      (witnessMixedWord k b delta hk z)).toSubmodule.map
        (witnessMaskProjection n _ _ k b).toLinearMap =
          (witnessCoreComplementCyclic k b delta hk z).toSubmodule := by
  change (cyclicSpan _ _).map _ = _
  rw [cyclicSpan_image]
  exact witnessCoreComplement_filtered_cyclic k b delta hk z

end
end HSTZ
#print axioms HSTZ.witnessCorePosition_sectorGroup_eq
#print axioms HSTZ.witnessCorePosition_group_iff
#print axioms HSTZ.witnessCorePositionGroupEquiv_val
#print axioms HSTZ.witnessCoreComplement_product_support
#print axioms HSTZ.witnessCoreComplement_block_support

#print axioms HSTZ.witnessCoreComplement_filtered_cyclic
#print axioms HSTZ.witnessCoreComplement_projection_image
