import HSTZ.WitnessBalanceComponentProjection
import HSTZ.WitnessAttachmentRowLetters
import HSTZ.BalanceOutputTwoSupport

/-! The cells of the label-0 (twos) component of the witness and their identification
with the native ordered two-row tableau. The cell bijection is given with an explicit
inverse before the component is enumerated by `Fin`. Uses declarations from OpenAI's
`math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

theorem witnessBalance_twos_column_iff (c : ℕ) :
    witnessBalanceColumnLabel k b delta c=0 ↔ k-2≤c ∧ c<k-1+b := by
  have hcut : k-(2+delta)≤k-2 := Nat.sub_le_sub_left (by omega) k
  constructor
  · intro h
    unfold witnessBalanceColumnLabel at h
    split_ifs at h <;> omega
  · rintro ⟨hlo,hhi⟩
    have hfirst : ¬c<k-(2+delta) := by omega
    have hsecond : ¬c<k-2 := by omega
    simp only [witnessBalanceColumnLabel,if_neg hfirst,if_neg hsecond,if_pos hhi]

theorem witnessBalance_twos_cell_iff (i c : ℕ) :
    (i,c)∈witnessAttachment (b+1) 0 ↔
      c<b+1 ∧ (i,k-2+c)∈witnessDiagram k b delta hk := by
  rw [mem_witnessAttachment,YoungDiagram.mem_iff_lt_rowLen,witnessDiagram_row_length]
  change ((i=0 ∧ c<b+1+0) ∨ (i=1 ∧ c<b+1)) ↔
    c<b+1 ∧ k-2+c<witnessRow k b delta i
  unfold witnessRow
  split_ifs <;> omega

def witnessBalanceTwosCellForward (u : witnessAttachment (b+1) 0) :
    {i : Fin n // witnessBalanceLabel hk z i=0} :=
  ⟨z.symm ⟨(u.val.1,k-2+u.val.2),
    (witnessBalance_twos_cell_iff (k:=k) (b:=b) (delta:=delta) hk _ _).mp u.property |>.2⟩,by
    have hu : u.val.2<b+1 :=
      ((witnessBalance_twos_cell_iff (k:=k) (b:=b) (delta:=delta) hk _ _).mp u.property).1
    change witnessBalanceColumnLabel k b delta (z (z.symm _)).val.2=0
    rw [z.apply_symm_apply]
    apply (witnessBalance_twos_column_iff (k:=k) (b:=b) (delta:=delta) _).mpr
    change k-2≤k-2+u.val.2 ∧ k-2+u.val.2<k-1+b
    omega⟩

def witnessBalanceTwosCellBackward (i : {i : Fin n // witnessBalanceLabel hk z i=0}) :
    witnessAttachment (b+1) 0 :=
  ⟨((z i.val).val.1,(z i.val).val.2-(k-2)),by
    have hi := (witnessBalance_twos_column_iff (k:=k) (b:=b) (delta:=delta) _).mp i.property
    apply (witnessBalance_twos_cell_iff (k:=k) (b:=b) (delta:=delta) hk _ _).mpr
    refine ⟨by omega,?_⟩
    have hc : k-2+((z i.val).val.2-(k-2))=(z i.val).val.2 := by omega
    rw [hc]
    exact (z i.val).property⟩

def witnessBalanceTwosCells : witnessAttachment (b+1) 0 ≃
    {i : Fin n // witnessBalanceLabel hk z i=0} where
  toFun := witnessBalanceTwosCellForward hk z
  invFun := witnessBalanceTwosCellBackward hk z
  left_inv u := by
    apply Subtype.ext
    change ((z (z.symm _)).val.1,(z (z.symm _)).val.2-(k-2))=u.val
    rw [z.apply_symm_apply]
    exact Prod.ext rfl (by simp)
  right_inv i := by
    apply Subtype.ext
    apply z.injective
    change z (z.symm _) = z i.val
    rw [z.apply_symm_apply]
    apply Subtype.ext
    have hi := (witnessBalance_twos_column_iff (k:=k) (b:=b) (delta:=delta) _).mp i.property
    exact Prod.ext rfl (by change k-2+((z i.val).val.2-(k-2))=(z i.val).val.2; omega)

def witnessBalanceTwosPositions :
    Fin (witnessAttachment (b+1) 0).card ≃ Fin (witnessBalanceComponentSize hk z 0) :=
  (balanceOutputTwoTableau (b+1)).trans
    ((witnessBalanceTwosCells hk z).trans (Fintype.equivFin _))

theorem witnessBalance_twos_positions_card :
    witnessBalanceComponentSize hk z 0=(witnessAttachment (b+1) 0).card := by
  simpa using (Fintype.card_congr (witnessBalanceTwosPositions hk z)).symm

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_twos_column_iff
#print axioms HSTZ.witnessBalance_twos_cell_iff
#print axioms HSTZ.witnessBalanceTwosCells
#print axioms HSTZ.witnessBalanceTwosPositions
#print axioms HSTZ.witnessBalance_twos_positions_card
