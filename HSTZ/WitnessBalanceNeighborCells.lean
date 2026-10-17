import HSTZ.WitnessBalanceComponentProjection
import HSTZ.WitnessAttachmentRowLetters

/-! The neighboring component formed by witness columns `2*s` and `2*s+1`. Its cells
are identified with an explicit inverse before any `Fin` enumeration or transport to
the native tableau. Uses declarations from OpenAI's `math` repository (commit
adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (s : ℕ)
    (hs : 2*s+1<k-(2+delta))

abbrev witnessBalanceNeighborSize := k-2*s-1

include hs

theorem witnessBalance_neighbor_column_iff (c : ℕ) :
    witnessBalanceColumnLabel k b delta c=3+s ↔ c=2*s ∨ c=2*s+1 := by
  unfold witnessBalanceColumnLabel
  split_ifs <;> omega

theorem witnessBalance_neighbor_cell_iff (i c : ℕ) :
    (i,c)∈(witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose ↔
      (c=0 ∨ c=1) ∧ (i,2*s+c)∈witnessDiagram k b delta hk := by
  have hcut : k-(2+delta)≤k-2 := Nat.sub_le_sub_left (by omega) k
  have hks : 2*s+4≤k := by omega
  rw [YoungDiagram.mem_transpose,mem_witnessAttachment,YoungDiagram.mem_iff_lt_rowLen,
    witnessDiagram_row_length]
  change ((c=0 ∧ i<witnessBalanceNeighborSize (k:=k) s+1) ∨
    (c=1 ∧ i<witnessBalanceNeighborSize (k:=k) s)) ↔
    (c=0 ∨ c=1) ∧ 2*s+c<witnessRow k b delta i
  unfold witnessBalanceNeighborSize witnessRow
  split_ifs <;> omega

def witnessBalanceNeighborCellForward
    (u : (witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose) :
    {i : Fin n // witnessBalanceLabel hk z i=3+s} :=
  ⟨z.symm ⟨(u.val.1,2*s+u.val.2),(witnessBalance_neighbor_cell_iff (k:=k) (b:=b) (delta:=delta) hk s hs _ _).mp u.property |>.2⟩,by
    have hu := (witnessBalance_neighbor_cell_iff (k:=k) (b:=b) (delta:=delta) hk s hs _ _).mp u.property
    change witnessBalanceColumnLabel k b delta (z (z.symm _)).val.2=3+s
    rw [z.apply_symm_apply]
    apply (witnessBalance_neighbor_column_iff (k:=k) (b:=b) (delta:=delta) s hs _).mpr
    rcases hu.1 with h | h <;> simp [h]⟩

def witnessBalanceNeighborCellBackward
    (i : {i : Fin n // witnessBalanceLabel hk z i=3+s}) :
    (witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose :=
  ⟨((z i.val).val.1,(z i.val).val.2-2*s),by
    have hi := (witnessBalance_neighbor_column_iff (k:=k) (b:=b) (delta:=delta) s hs _).mp i.property
    apply (witnessBalance_neighbor_cell_iff (k:=k) (b:=b) (delta:=delta) hk s hs _ _).mpr
    refine ⟨by omega,?_⟩
    have hc : 2*s+((z i.val).val.2-2*s)=(z i.val).val.2 := by omega
    rw [hc]
    exact (z i.val).property⟩

def witnessBalanceNeighborCells :
    (witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose ≃
      {i : Fin n // witnessBalanceLabel hk z i=3+s} where
  toFun := witnessBalanceNeighborCellForward hk z s hs
  invFun := witnessBalanceNeighborCellBackward hk z s hs
  left_inv u := by
    apply Subtype.ext
    change ((z (z.symm _)).val.1,(z (z.symm _)).val.2-2*s)=u.val
    rw [z.apply_symm_apply]
    exact Prod.ext rfl (by simp)
  right_inv i := by
    apply Subtype.ext
    apply z.injective
    change z (z.symm _) = z i.val
    rw [z.apply_symm_apply]
    apply Subtype.ext
    have hi := (witnessBalance_neighbor_column_iff (k:=k) (b:=b) (delta:=delta) s hs _).mp i.property
    exact Prod.ext rfl (by change 2*s+((z i.val).val.2-2*s)=(z i.val).val.2; omega)

/-- Native local positions, transported explicitly through the cells of the
component. -/
def witnessBalanceNeighborPositions :
    Fin (2*witnessBalanceNeighborSize (k:=k) s+1) ≃ Fin (witnessBalanceComponentSize hk z (3+s)) :=
  (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)).trans
    ((witnessBalanceNeighborCells hk z s hs).trans (Fintype.equivFin _))

theorem witnessBalance_neighbor_positions_card :
    witnessBalanceComponentSize hk z (3+s)=2*witnessBalanceNeighborSize (k:=k) s+1 := by
  simpa using (Fintype.card_congr (witnessBalanceNeighborPositions hk z s hs)).symm

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_neighbor_column_iff
#print axioms HSTZ.witnessBalance_neighbor_cell_iff
#print axioms HSTZ.witnessBalanceNeighborCells
#print axioms HSTZ.witnessBalanceNeighborPositions
#print axioms HSTZ.witnessBalance_neighbor_positions_card
