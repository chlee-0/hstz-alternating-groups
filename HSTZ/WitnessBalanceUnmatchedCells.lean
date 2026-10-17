import HSTZ.WitnessBalanceComponentProjection
import HSTZ.BalanceSingletonSupport
import HSTZ.WitnessAttachmentRowLetters

/-! The unmatched early singleton component: when the cutoff `k-(2+delta)` is odd,
the component with label `3+s` is the single column `2*s`. Its cells are identified
before the component is enumerated by `Fin`, following the height-three
component. Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (s : ℕ) (hd : delta≤1) (hs : k-(2+delta)=2*s+1)

include hk hd hs

include hk hd hs in
theorem witnessBalance_unmatched_column_iff (c : ℕ) :
    witnessBalanceColumnLabel k b delta c=3+s ↔ c=2*s := by
  constructor
  · intro h
    unfold witnessBalanceColumnLabel at h
    split_ifs at h <;> omega
  · rintro rfl
    have hfirst : 2*s<k-(2+delta) := by omega
    simp only [witnessBalanceColumnLabel,if_pos hfirst]
    omega

theorem witnessBalance_unmatched_cell_iff (i c : ℕ) :
    (i,c)∈(oneRowDiagram (k-2*s)).transpose ↔
      c=0 ∧ (i,2*s)∈witnessDiagram k b delta hk := by
  rw [YoungDiagram.mem_transpose,mem_oneRowDiagram,YoungDiagram.mem_iff_lt_rowLen,
    witnessDiagram_row_length]
  change (c=0 ∧ i<k-2*s) ↔ c=0 ∧ 2*s<witnessRow k b delta i
  unfold witnessRow
  split_ifs <;> omega

def witnessBalanceUnmatchedCellForward (u : (oneRowDiagram (k-2*s)).transpose) :
    {i : Fin n // witnessBalanceLabel hk z i=3+s} :=
  ⟨z.symm ⟨(u.val.1,2*s),
    ((witnessBalance_unmatched_cell_iff (k:=k) (b:=b) hk s hd hs _ _).mp u.property).2⟩,by
    change witnessBalanceColumnLabel k b delta (z (z.symm _)).val.2=3+s
    rw [z.apply_symm_apply]
    exact (witnessBalance_unmatched_column_iff (k:=k) (b:=b) hk s hd hs _).mpr rfl⟩

def witnessBalanceUnmatchedCellBackward (i : {i : Fin n // witnessBalanceLabel hk z i=3+s}) :
    (oneRowDiagram (k-2*s)).transpose :=
  ⟨((z i.val).val.1,0),by
    have hc := (witnessBalance_unmatched_column_iff (k:=k) (b:=b) hk s hd hs _).mp i.property
    apply (witnessBalance_unmatched_cell_iff (k:=k) (b:=b) hk s hd hs _ _).mpr
    refine ⟨rfl,?_⟩
    rw [← hc]
    exact (z i.val).property⟩

def witnessBalanceUnmatchedCells : (oneRowDiagram (k-2*s)).transpose ≃
    {i : Fin n // witnessBalanceLabel hk z i=3+s} where
  toFun := witnessBalanceUnmatchedCellForward hk z s hd hs
  invFun := witnessBalanceUnmatchedCellBackward hk z s hd hs
  left_inv u := by
    apply Subtype.ext
    change ((z (z.symm _)).val.1,0)=u.val
    rw [z.apply_symm_apply]
    have hu := (witnessBalance_unmatched_cell_iff (k:=k) (b:=b) hk s hd hs _ _).mp u.property
    exact Prod.ext rfl hu.1.symm
  right_inv i := by
    apply Subtype.ext
    apply z.injective
    change z (z.symm _)=z i.val
    rw [z.apply_symm_apply]
    apply Subtype.ext
    have hc := (witnessBalance_unmatched_column_iff (k:=k) (b:=b) hk s hd hs _).mp i.property
    exact Prod.ext rfl hc.symm

def witnessBalanceUnmatchedPositions : Fin (k-2*s) ≃ Fin (witnessBalanceComponentSize hk z (3+s)) :=
  (balanceSingletonTableau (k-2*s)).trans
    ((witnessBalanceUnmatchedCells hk z s hd hs).trans (Fintype.equivFin _))

theorem witnessBalance_unmatched_positions_card : witnessBalanceComponentSize hk z (3+s)=k-2*s := by
  simpa using (Fintype.card_congr (witnessBalanceUnmatchedPositions hk z s hd hs)).symm

theorem witnessBalance_unmatched_positions_cell (i : Fin (k-2*s)) :
    (z ((witnessBalanceComponentCut hk z (3+s)).symm
      (.inl (witnessBalanceUnmatchedPositions hk z s hd hs i)))).val=
    ((balanceSingletonTableau (k-2*s) i).val.1,2*s) := by
  change (z (((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=3+s}).symm
    ((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=3+s})
      (witnessBalanceUnmatchedCells hk z s hd hs (balanceSingletonTableau (k-2*s) i)))).val)).val=_
  rw [Equiv.symm_apply_apply]
  change (z (z.symm _)).val=_
  rw [z.apply_symm_apply]

theorem witnessBalance_unmatched_positions_inverse
    (i : Fin (witnessBalanceComponentSize hk z (3+s))) :
    (balanceSingletonTableau (k-2*s) ((witnessBalanceUnmatchedPositions hk z s hd hs).symm i)).val=
    ((z ((witnessBalanceComponentCut hk z (3+s)).symm (.inl i))).val.1,0) := by
  have he := witnessBalance_unmatched_positions_cell hk z s hd hs ((witnessBalanceUnmatchedPositions hk z s hd hs).symm i)
  rw [Equiv.apply_symm_apply] at he
  exact Prod.ext (congrArg Prod.fst he).symm rfl

/-- The column fibers of the component, transported to the native tableau, form the
full native column group. -/
theorem witnessBalance_unmatched_full_column_fiber :
    fiberGroup (fun i => (z ((witnessBalanceComponentCut hk z (3+s)).symm
      (.inl (witnessBalanceUnmatchedPositions hk z s hd hs i)))).val.2)=
    columnGroup (balanceSingletonTableau (k-2*s)) := by
  rw [balanceSingleton_full_column_group]
  ext g
  change (∀ i, (z ((witnessBalanceComponentCut hk z (3+s)).symm
    (.inl (witnessBalanceUnmatchedPositions hk z s hd hs (g i))))).val.2=
      (z ((witnessBalanceComponentCut hk z (3+s)).symm
        (.inl (witnessBalanceUnmatchedPositions hk z s hd hs i)))).val.2) ↔ True
  simp only [witnessBalance_unmatched_positions_cell hk z s hd hs]
  simp

include hk hd hs in
theorem witnessBalance_unmatched_height : k-2*s=3+delta := by omega

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_unmatched_column_iff
#print axioms HSTZ.witnessBalance_unmatched_cell_iff
#print axioms HSTZ.witnessBalanceUnmatchedCells
#print axioms HSTZ.witnessBalanceUnmatchedPositions
#print axioms HSTZ.witnessBalance_unmatched_positions_card
#print axioms HSTZ.witnessBalance_unmatched_positions_cell
#print axioms HSTZ.witnessBalance_unmatched_positions_inverse
#print axioms HSTZ.witnessBalance_unmatched_full_column_fiber

#print axioms HSTZ.witnessBalance_unmatched_height
