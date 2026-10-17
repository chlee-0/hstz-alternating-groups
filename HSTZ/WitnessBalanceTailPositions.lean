import HSTZ.WitnessBalanceTailProjectedSupport

/-! Positions of the whole tail component (label 1) of the witness, and its projected
one-row support in native degree. All physical tail columns and both generators are
kept. Uses declarations from OpenAI's `math` repository (commit adc7f1241,
Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

include hk in
theorem witnessBalance_tail_column_iff (c : ℕ) :
    witnessBalanceColumnLabel k b delta c=1 ↔ k-1+b≤c := by
  constructor
  · intro h
    unfold witnessBalanceColumnLabel at h
    split_ifs at h <;> omega
  · intro h
    have hfirst : ¬c<k-(2+delta) := by omega
    have hsecond : ¬c<k-2 := by omega
    have hthird : ¬c<k-1+b := by omega
    simp only [witnessBalanceColumnLabel,if_neg hfirst,if_neg hsecond,if_neg hthird]

include hk in
theorem witnessBalance_tail_cell_iff (r c : ℕ) :
    ((r,c)∈witnessDiagram k b delta hk ∧ k-1+b≤c) ↔
      r=0 ∧ k-1+b≤c ∧ c<k+b+delta := by
  rw [YoungDiagram.mem_iff_lt_rowLen,witnessDiagram_row_length]
  unfold witnessRow
  split_ifs <;> omega

def witnessBalanceTailCellForward (i : Fin (1+delta)) :
    {j : Fin n // witnessBalanceLabel hk z j=1} :=
  ⟨z.symm ⟨(0,k-1+b+i.val),
    ((witnessBalance_tail_cell_iff (k:=k) (b:=b) hk _ _).mpr
      ⟨rfl,by omega,by have hi:=i.isLt;omega⟩).1⟩,by
    change witnessBalanceColumnLabel k b delta (z (z.symm _)).val.2=1
    rw [z.apply_symm_apply]
    exact (witnessBalance_tail_column_iff (k:=k) (b:=b) hk _).mpr (by change k-1+b≤k-1+b+i.val;omega)⟩

def witnessBalanceTailCellBackward (j : {j : Fin n // witnessBalanceLabel hk z j=1}) :
    Fin (1+delta) :=
  ⟨(z j.val).val.2-(k-1+b),by
    have hc := (witnessBalance_tail_column_iff (k:=k) (b:=b) hk _).mp j.property
    have hg := (witnessBalance_tail_cell_iff (k:=k) (b:=b) hk _ _).mp
      ⟨(z j.val).property,hc⟩
    change (z j.val).val.2-(k-1+b)<1+delta
    have hu : (z j.val).val.2<k+b+delta := hg.2.2
    omega⟩

/-- The tail cells identified with the label-1 subtype, before the component is
enumerated by `Fin`. -/
def witnessBalanceTailCells : Fin (1+delta) ≃
    {j : Fin n // witnessBalanceLabel hk z j=1} where
  toFun := witnessBalanceTailCellForward hk z
  invFun := witnessBalanceTailCellBackward hk z
  left_inv i := by
    apply Fin.ext
    change (z (z.symm _)).val.2-(k-1+b)=i.val
    rw [z.apply_symm_apply]
    change k-1+b+i.val-(k-1+b)=i.val
    omega
  right_inv j := by
    apply Subtype.ext
    apply z.injective
    change z (z.symm _)=z j.val
    rw [z.apply_symm_apply]
    apply Subtype.ext
    have hc := (witnessBalance_tail_column_iff (k:=k) (b:=b) hk _).mp j.property
    have hg := (witnessBalance_tail_cell_iff (k:=k) (b:=b) hk _ _).mp
      ⟨(z j.val).property,hc⟩
    exact Prod.ext hg.1.symm (by change k-1+b+((z j.val).val.2-(k-1+b))=(z j.val).val.2;omega)

def witnessBalanceTailPositions : Fin (1+delta) ≃ Fin (witnessBalanceComponentSize hk z 1) :=
  (witnessBalanceTailCells hk z).trans (Fintype.equivFin _)

theorem witnessBalance_tail_positions_card : witnessBalanceComponentSize hk z 1=1+delta := by
  simpa using (Fintype.card_congr (witnessBalanceTailPositions hk z)).symm

theorem witnessBalance_tail_positions_cell (i : Fin (1+delta)) :
    (z ((witnessBalanceComponentCut hk z 1).symm
      (.inl (witnessBalanceTailPositions hk z i)))).val=(0,k-1+b+i.val) := by
  change (z (((Fintype.equivFin {j : Fin n // witnessBalanceLabel hk z j=1}).symm
    ((Fintype.equivFin {j : Fin n // witnessBalanceLabel hk z j=1})
      (witnessBalanceTailCells hk z i))).val)).val=_
  rw [Equiv.symm_apply_apply]
  change (z (z.symm _)).val=_
  rw [z.apply_symm_apply]

theorem witnessBalance_tail_positions_inverse
    (i : Fin (witnessBalanceComponentSize hk z 1)) :
    ((witnessBalanceTailPositions hk z).symm i).val=
      (z ((witnessBalanceComponentCut hk z 1).symm (.inl i))).val.2-(k-1+b) := by
  have he := witnessBalance_tail_positions_cell hk z ((witnessBalanceTailPositions hk z).symm i)
  rw [Equiv.apply_symm_apply] at he
  have hc := congrArg Prod.snd he
  omega

/-- One-row support for the whole tail in native degree, with the position action
transported along the tail positions. The projected tail vector is reused. -/
theorem witnessBalanceTail_native_projected_support :
    ∃ J : Representation.IntertwiningMap (spechtRep (oneRowTableau (1+delta)))
      ((witnessBalanceLocalProjectedFactor hk z 1).toRepresentation.comp
        (positionPermHom (witnessBalanceTailPositions hk z))), Function.Injective J := by
  let u := oneRowTableau (1+delta)
  let y := witnessBalanceTailProjectedVector hk z
  let J : Representation.IntertwiningMap (spechtRep u)
      ((witnessBalanceLocalProjectedFactor hk z 1).toRepresentation.comp
        (positionPermHom (witnessBalanceTailPositions hk z))) :=
    { toLinearMap :=
        { toFun := fun x => oneRowEvaluation u x • y
          map_add' := by intro x v; simp only [map_add,add_smul]
          map_smul' := by intro c x; simp only [map_smul,smul_smul]; rfl }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        change oneRowEvaluation u (spechtRep u g x) • y =
          (witnessBalanceLocalProjectedFactor hk z 1).toRepresentation
            (positionPermHom (witnessBalanceTailPositions hk z) g) (oneRowEvaluation u x • y)
        rw [oneRow_specht_fixed u (oneRowDiagram_rows (1+delta)),map_smul]
        exact congrArg (fun v => oneRowEvaluation u x • v)
          (witnessBalanceTailProjectedVector_fixed hk z (positionPermHom (witnessBalanceTailPositions hk z) g)).symm }
  have hn : J≠0 := by
    intro hz
    let p : Specht u := ⟨polytabloid u,mem_cyclic _ _⟩
    have he := congrArg (fun F => F p) hz
    change oneRowEvaluation u p • y=0 at he
    have hp : oneRowEvaluation u p=1 := polytabloid_rowWord u
    rw [hp,one_smul] at he
    exact witnessBalanceTailProjectedVector_ne_zero hk z he
  letI := specht_irreducible u
  exact ⟨J,(Representation.IsIrreducible.injective_or_eq_zero J).resolve_right hn⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_tail_column_iff
#print axioms HSTZ.witnessBalance_tail_cell_iff
#print axioms HSTZ.witnessBalanceTailCells
#print axioms HSTZ.witnessBalanceTailPositions
#print axioms HSTZ.witnessBalance_tail_positions_card
#print axioms HSTZ.witnessBalance_tail_positions_cell
#print axioms HSTZ.witnessBalance_tail_positions_inverse
#print axioms HSTZ.witnessBalanceTail_native_projected_support
