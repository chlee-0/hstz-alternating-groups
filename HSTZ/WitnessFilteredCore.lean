import HSTZ.WitnessMixedWord
import HSTZ.WitnessMarkedRigidity
import HSTZ.WitnessCutPositions

/-! Nonzero common-mask filtered coordinates of the original mixed polytabloid
word force the core positions. The support/permutation argument adapts
`staircase_projected_high_positions` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Retained rotated words and the selected-generator identity are handled separately. -/
namespace HSTZ
open OAI.Saxl
open scoped TensorProduct

noncomputable def witnessCorePositionEmbedding (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    Fin (staircase (k-2)).card ↪ Fin n :=
  ⟨fun i => (witnessCutPositionEquiv k b delta hk t).symm (.inl i),
    (witnessCutPositionEquiv k b delta hk t).symm.injective.comp Sum.inl_injective⟩

theorem witnessCorePositionEmbedding_range (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) :
    i∈Set.range (witnessCorePositionEmbedding k b delta hk t) ↔
      t i∈Set.range (witnessCoreCell k b delta hk) := by
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨canonicalTableau (staircase (k-2)) rfl j,
      (witnessCutPosition_core k b delta hk t j).symm⟩
  · rintro ⟨x,hx⟩
    let j := (canonicalTableau (staircase (k-2)) rfl).symm x
    refine ⟨j,t.injective ?_⟩
    change t ((witnessCutPositionEquiv k b delta hk t).symm (.inl j))=t i
    rw [witnessCutPosition_core]
    exact (congrArg (witnessCoreCell k b delta hk)
      ((canonicalTableau (staircase (k-2)) rfl).apply_symm_apply x)).trans hx

theorem witness_filtered_core_positions (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk))
    (w : Fin n → Fin ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0))
    (hw : witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t) w ≠ 0) :
    ∀ i, (witnessRowMarked k b (splitLeft w i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) ∧
      (witnessColumnMarked k (splitRight w i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) := by
  classical
  obtain ⟨heq,hww⟩ := (witnessMaskProjection_nonzero_iff n _ _ k b _ w).mp hw
  have hp : polytabloid (transposeTableau t) (splitLeft w) *
      polytabloid t (splitRight w) ≠ 0 := by
    simpa only [witnessMixedWord_coordinate] using hww
  obtain ⟨g,hg⟩ := polytabloid_support (transposeTableau t) _ (mul_ne_zero_iff.mp hp).1
  obtain ⟨q,hq⟩ := polytabloid_support t _ (mul_ne_zero_iff.mp hp).2
  let gc : Equiv.Perm (witnessDiagram k b delta hk).cells :=
    (t.symm.trans (g : Equiv.Perm (Fin n))).trans t
  let qc : Equiv.Perm (witnessDiagram k b delta hk).cells :=
    (t.symm.trans (q : Equiv.Perm (Fin n))).trans t
  have hgc : ∀ x, (gc x).val.1=x.val.1 := by
    intro x
    have hh := g.property (t.symm x)
    change (t ((g : Equiv.Perm (Fin n)) (t.symm x))).val.1 =
      (t (t.symm x)).val.1 at hh
    simpa [gc] using hh
  have hqc : ∀ x, (qc x).val.2=x.val.2 := by
    intro x
    have hh := q.property (t.symm x)
    change (t ((q : Equiv.Perm (Fin n)) (t.symm x))).val.2 =
      (t (t.symm x)).val.2 at hh
    simpa [qc] using hh
  have hcommon : ∀ x, witnessRowMarked k b (gc x).val.2 ↔
      witnessColumnMarked k (qc x).val.1 := by
    intro x
    have hh := heq (t.symm x)
    rw [hg,hq] at hh
    exact hh
  have hr := witness_common_marked_core k b delta hk gc qc hgc hqc hcommon
  intro i
  have hh := hr (t i)
  rw [hg,hq]
  have hl : witnessRowMarked k b
      (rowWord (transposeTableau t) ((g : Equiv.Perm (Fin n)) i)).val ↔
      t i∈Set.range (witnessCoreCell k b delta hk) := by
    simpa [gc,rowWord,transposeTableau] using hh.1
  have hc : witnessColumnMarked k
      (rowWord t ((q : Equiv.Perm (Fin n)) i)).val ↔
      t i∈Set.range (witnessCoreCell k b delta hk) := by
    simpa [qc,rowWord] using hh.2
  exact ⟨hl.trans (witnessCorePositionEmbedding_range k b delta hk t i).symm,
    hc.trans (witnessCorePositionEmbedding_range k b delta hk t i).symm⟩


/-- Full coordinate identity; neither layer is a retained rotated alternant yet. -/
theorem witness_filtered_sector (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t) =
      coordinateProjection (fun w =>
        (∀ i, witnessRowMarked k b (splitLeft w i).val ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) ∧
        (∀ i, witnessColumnMarked k (splitRight w i).val ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk t)))
        (witnessMixedWord k b delta hk t) := by
  classical
  funext w
  by_cases he : witnessCommonMask n _ _ k b w
  · by_cases hw : witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t) w=0
    · have hw' : witnessMixedWord k b delta hk t w=0 := by
        simpa only [witnessMaskProjection_apply,if_pos he] using hw
      simp only [witnessMaskProjection_apply,coordinateProjection_apply,hw',ite_self]
    · have hD := witness_filtered_core_positions k b delta hk t w hw
      have hL := fun i => (hD i).1
      have hR := fun i => (hD i).2
      have hP : ((∀ i, witnessRowMarked k b (splitLeft w i).val ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) ∧
        (∀ i, witnessColumnMarked k (splitRight w i).val ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk t))) := ⟨hL,hR⟩
      simp only [witnessMaskProjection_apply,coordinateProjection_apply,if_pos he,if_pos hP]
  · have hn : ¬ ((∀ i, witnessRowMarked k b (splitLeft w i).val ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk t)) ∧
        (∀ i, witnessColumnMarked k (splitRight w i).val ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk t))) := by
      rintro ⟨hL,hR⟩
      exact he (fun i => (hL i).trans (hR i).symm)
    simp only [witnessMaskProjection_apply,coordinateProjection_apply,if_neg he,if_neg hn]

theorem witness_filtered_sector_tensor (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk t) =
      wordTensor n _ _
        (coordinateProjection (fun a => ∀ i, witnessRowMarked k b (a i).val ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk t))
          (polytabloid (transposeTableau t)) ⊗ₜ[ℂ]
        coordinateProjection (fun a => ∀ i, witnessColumnMarked k (a i).val ↔
          i∈Set.range (witnessCorePositionEmbedding k b delta hk t))
          (polytabloid t)) := by
  rw [witness_filtered_sector,witnessMixedWord]
  exact @coordinateProjection_tensor n
    ((witnessDiagram k b delta hk).transpose.colLen 0)
    ((witnessDiagram k b delta hk).colLen 0)
    (fun a => ∀ i, witnessRowMarked k b (a i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t))
    (fun a => ∀ i, witnessColumnMarked k (a i).val ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t))
    (polytabloid (transposeTableau t)) (polytabloid t)

end HSTZ
#print axioms HSTZ.witnessCorePositionEmbedding
#print axioms HSTZ.witnessCorePositionEmbedding_range
#print axioms HSTZ.witness_filtered_core_positions
#print axioms HSTZ.witness_filtered_sector
#print axioms HSTZ.witness_filtered_sector_tensor
