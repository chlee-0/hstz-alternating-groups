import HSTZ.WitnessSelectedCoefficients

/-! Pair projection, its signed coefficient and nonvanishing.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Nonvanishing of the projection is proved from the coefficient, not inferred from
nonvanishing of the source. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessComplementLowProjection (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    Module.End ℂ (WordSpace (witnessComplementSize k b delta)
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
       (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :=
  coordinateProjection (fun w => ∀ i, (splitLeft w i).val<2 ↔ witnessComplementPathMask k b delta i)

theorem witness_selected_pair_projection (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    witnessComplementLowProjection k b delta hp
      (witnessComplementPairWord k b delta hp.staircase_bound t)=
        -witnessSelectedComplementPairWord k b delta hp := by
  let P := fun a : Fin (witnessComplementSize k b delta) →
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0) =>
      ∀ i, (a i).val<2 ↔ witnessComplementPathMask k b delta i
  let Q := fun _ : Fin (witnessComplementSize k b delta) →
      Fin ((witnessDiagram k b delta hp.staircase_bound).colLen 0) => True
  have he := coordinateProjection_tensor P Q
    (witnessComplementRowWord k b delta hp.staircase_bound t)
    (witnessComplementColumnWord k b delta hp.staircase_bound t)
  have hpred : (fun w => P (splitLeft w) ∧ Q (splitRight w))=
      (fun w => P (splitLeft w))  := by
    funext w
    change (P (splitLeft w) ∧ True)=P (splitLeft w)
    exact and_true _
  rw [hpred] at he
  have hq : coordinateProjection Q (witnessComplementColumnWord k b delta hp.staircase_bound t)=
      witnessComplementColumnWord k b delta hp.staircase_bound t := by
    classical
    funext w
    simp only [coordinateProjection_apply,Q,if_true]
  rw [hq] at he
  have hrow := witness_selected_row_sector k b delta hp t
  change coordinateProjection P (witnessComplementRowWord k b delta hp.staircase_bound t)=
    -witnessSelectedRowWord k b delta hp at hrow
  rw [hrow] at he
  rw [TensorProduct.neg_tmul,map_neg] at he
  change witnessComplementLowProjection k b delta hp
    (witnessComplementPairWord k b delta hp.staircase_bound t)=_ at he
  rw [witness_complement_column_alternant] at he
  exact he

theorem witness_selected_pair_projected_coefficient (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    witnessComplementLowProjection k b delta hp
      (witnessComplementPairWord k b delta hp.staircase_bound t)
      (mergeWords (witnessExchangedRowBase k b delta hp.staircase_bound
        (paperWitness_attachment_positive k b delta hp))
        (witnessComplementColumnBase k b delta hp.staircase_bound))= -1 := by
  rw [witness_selected_pair_projection]
  change -(witnessSelectedComplementPairWord k b delta hp _)= -1
  rw [witnessSelectedComplementPairWord_coefficient]

theorem witness_selected_pair_projection_ne_zero (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    witnessComplementLowProjection k b delta hp
      (witnessComplementPairWord k b delta hp.staircase_bound t)≠0 := by
  rw [witness_selected_pair_projection]
  exact neg_ne_zero.mpr (witnessSelectedComplementPairWord_ne_zero k b delta hp)

end
end HSTZ
#print axioms HSTZ.witness_selected_pair_projection
#print axioms HSTZ.witness_selected_pair_projected_coefficient
#print axioms HSTZ.witness_selected_pair_projection_ne_zero
