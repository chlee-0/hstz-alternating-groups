import HSTZ.WitnessBalanceComponentProjection
import HSTZ.BalanceSingletonSupport
import HSTZ.WitnessAttachmentRowLetters

/-! The original optional height-3 component (delta = 1, label 2, column k-3).
Reuses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0) and existing
cell/`Fin` transport patterns. A one-column cell equivalence is constructed before
enumeration. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical
section
variable {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 1 hk))

include hk in
theorem witnessBalance_three_column_iff (c : ℕ) :
    witnessBalanceColumnLabel k b 1 c=2 ↔ c=k-3 := by
  constructor
  · intro h
    unfold witnessBalanceColumnLabel at h
    split_ifs at h <;> omega
  · rintro rfl
    have hfirst : ¬k-3<k-(2+1) := by omega
    have hsecond : k-3<k-2 := by omega
    simp only [witnessBalanceColumnLabel,if_neg hfirst,if_pos hsecond]

theorem witnessBalance_three_cell_iff (i c : ℕ) :
    (i,c)∈(oneRowDiagram 3).transpose ↔
      c=0 ∧ (i,k-3)∈witnessDiagram k b 1 hk := by
  rw [YoungDiagram.mem_transpose,mem_oneRowDiagram,YoungDiagram.mem_iff_lt_rowLen,
    witnessDiagram_row_length]
  change (c=0 ∧ i<3) ↔ c=0 ∧ k-3<witnessRow k b 1 i
  unfold witnessRow
  split_ifs <;> omega

def witnessBalanceThreeCellForward (u : (oneRowDiagram 3).transpose) :
    {i : Fin n // witnessBalanceLabel hk z i=2} :=
  ⟨z.symm ⟨(u.val.1,k-3),
    ((witnessBalance_three_cell_iff (k:=k) (b:=b) hk _ _).mp u.property).2⟩,by
    change witnessBalanceColumnLabel k b 1 (z (z.symm _)).val.2=2
    rw [z.apply_symm_apply]
    exact (witnessBalance_three_column_iff (k:=k) (b:=b) hk _).mpr rfl⟩

def witnessBalanceThreeCellBackward (i : {i : Fin n // witnessBalanceLabel hk z i=2}) :
    (oneRowDiagram 3).transpose :=
  ⟨((z i.val).val.1,0),by
    have hc := (witnessBalance_three_column_iff (k:=k) (b:=b) hk _).mp i.property
    apply (witnessBalance_three_cell_iff (k:=k) (b:=b) hk _ _).mpr
    refine ⟨rfl,?_⟩
    rw [← hc]
    exact (z i.val).property⟩

def witnessBalanceThreeCells : (oneRowDiagram 3).transpose ≃
    {i : Fin n // witnessBalanceLabel hk z i=2} where
  toFun := witnessBalanceThreeCellForward hk z
  invFun := witnessBalanceThreeCellBackward hk z
  left_inv u := by
    apply Subtype.ext
    change ((z (z.symm _)).val.1,0)=u.val
    rw [z.apply_symm_apply]
    have hu := (witnessBalance_three_cell_iff (k:=k) (b:=b) hk _ _).mp u.property
    exact Prod.ext rfl hu.1.symm
  right_inv i := by
    apply Subtype.ext
    apply z.injective
    change z (z.symm _)=z i.val
    rw [z.apply_symm_apply]
    apply Subtype.ext
    have hc := (witnessBalance_three_column_iff (k:=k) (b:=b) hk _).mp i.property
    exact Prod.ext rfl hc.symm

def witnessBalanceThreePositions : Fin 3 ≃ Fin (witnessBalanceComponentSize hk z 2) :=
  (balanceSingletonTableau 3).trans
    ((witnessBalanceThreeCells hk z).trans (Fintype.equivFin _))

theorem witnessBalance_three_positions_card : witnessBalanceComponentSize hk z 2=3 := by
  simpa using (Fintype.card_congr (witnessBalanceThreePositions hk z)).symm

theorem witnessBalance_three_positions_cell (i : Fin 3) :
    (z ((witnessBalanceComponentCut hk z 2).symm
      (.inl (witnessBalanceThreePositions hk z i)))).val=
    ((balanceSingletonTableau 3 i).val.1,k-3) := by
  change (z (((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=2}).symm
    ((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=2})
      (witnessBalanceThreeCells hk z (balanceSingletonTableau 3 i)))).val)).val=_
  rw [Equiv.symm_apply_apply]
  change (z (z.symm _)).val=_
  rw [z.apply_symm_apply]

theorem witnessBalance_three_positions_inverse
    (i : Fin (witnessBalanceComponentSize hk z 2)) :
    (balanceSingletonTableau 3 ((witnessBalanceThreePositions hk z).symm i)).val=
    ((z ((witnessBalanceComponentCut hk z 2).symm (.inl i))).val.1,0) := by
  have he := witnessBalance_three_positions_cell hk z ((witnessBalanceThreePositions hk z).symm i)
  rw [Equiv.apply_symm_apply] at he
  exact Prod.ext (congrArg Prod.fst he).symm rfl

/-- The full original column fibers are transported to the full column group. -/
theorem witnessBalance_three_full_column_fiber :
    fiberGroup (fun i => (z ((witnessBalanceComponentCut hk z 2).symm
      (.inl (witnessBalanceThreePositions hk z i)))).val.2)=
    columnGroup (balanceSingletonTableau 3) := by
  rw [balanceSingleton_full_column_group]
  ext g
  change (∀ i, (z ((witnessBalanceComponentCut hk z 2).symm
    (.inl (witnessBalanceThreePositions hk z (g i))))).val.2=
      (z ((witnessBalanceComponentCut hk z 2).symm
        (.inl (witnessBalanceThreePositions hk z i)))).val.2) ↔ True
  simp only [witnessBalance_three_positions_cell hk z]
  simp

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_three_column_iff
#print axioms HSTZ.witnessBalance_three_cell_iff
#print axioms HSTZ.witnessBalanceThreeCells
#print axioms HSTZ.witnessBalanceThreePositions
#print axioms HSTZ.witnessBalance_three_positions_card
#print axioms HSTZ.witnessBalance_three_positions_cell
#print axioms HSTZ.witnessBalance_three_positions_inverse
#print axioms HSTZ.witnessBalance_three_full_column_fiber
