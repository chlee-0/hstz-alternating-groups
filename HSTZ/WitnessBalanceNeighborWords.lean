import HSTZ.WitnessBalanceNeighborCells
import HSTZ.LetterLift

/-! From native local positions, letters and full columns to the original
component. Reuses the fiber relabel and letter lift calculation from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (s : ℕ)
    (hs : 2*s+1<k-(2+delta))
include hs

theorem witnessBalance_neighbor_positions_cell
    (i : Fin (2*witnessBalanceNeighborSize (k:=k) s+1)) :
    (z ((witnessBalanceComponentCut hk z (3+s)).symm
      (.inl (witnessBalanceNeighborPositions hk z s hs i)))).val =
    ((balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s) i).val.1,
      2*s+(balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s) i).val.2) := by
  change (z (((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=3+s}).symm
    ((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=3+s})
      (witnessBalanceNeighborCells hk z s hs
        (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s) i)))).val)).val = _
  rw [Equiv.symm_apply_apply]
  change (z (z.symm _)).val=_
  rw [z.apply_symm_apply]

theorem witnessBalance_neighbor_positions_inverse
    (i : Fin (witnessBalanceComponentSize hk z (3+s))) :
    (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)
      ((witnessBalanceNeighborPositions hk z s hs).symm i)).val =
    ((z ((witnessBalanceComponentCut hk z (3+s)).symm (.inl i))).val.1,
      (z ((witnessBalanceComponentCut hk z (3+s)).symm (.inl i))).val.2-2*s) := by
  have he := witnessBalance_neighbor_positions_cell hk z s hs
    ((witnessBalanceNeighborPositions hk z s hs).symm i)
  rw [Equiv.apply_symm_apply] at he
  have hr := congrArg Prod.fst he
  have hc := congrArg Prod.snd he
  exact Prod.ext hr.symm (by omega)

theorem witnessBalance_neighbor_rows_bound :
    (witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0 ≤
      (witnessDiagram k b delta hk).colLen 0 := by
  rw [witnessAttachment_width,witnessDiagram_height]
  unfold witnessBalanceNeighborSize
  omega

def witnessBalanceNeighborRowLetter :
    Fin ((witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0) ↪
      Fin ((witnessDiagram k b delta hk).colLen 0) where
  toFun i := ⟨i.val,lt_of_lt_of_le i.isLt (witnessBalance_neighbor_rows_bound (k:=k) (b:=b) (delta:=delta) hk s hs)⟩
  inj' i j h := by
    apply Fin.ext
    exact congrArg (fun t : Fin ((witnessDiagram k b delta hk).colLen 0) => t.val) h

theorem witnessBalance_neighbor_row_word :
    leftWord (witnessBalanceComponentCut hk z (3+s)) (rowWord z) ∘
      witnessBalanceNeighborPositions hk z s hs =
    witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs ∘
      rowWord (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)) := by
  funext i
  apply Fin.ext
  have he := witnessBalance_neighbor_positions_cell hk z s hs i
  have hr := congrArg Prod.fst he
  change (z ((witnessBalanceComponentCut hk z (3+s)).symm
    (.inl (witnessBalanceNeighborPositions hk z s hs i)))).val.1 =
    (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s) i).val.1
  exact hr

theorem witnessBalance_neighbor_full_column_fiber :
    fiberGroup (fun i => (z ((witnessBalanceComponentCut hk z (3+s)).symm
      (.inl (witnessBalanceNeighborPositions hk z s hs i)))).val.2) =
    columnGroup (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)) := by
  ext g
  change (∀ i, (z ((witnessBalanceComponentCut hk z (3+s)).symm
    (.inl (witnessBalanceNeighborPositions hk z s hs (g i))))).val.2 =
    (z ((witnessBalanceComponentCut hk z (3+s)).symm
      (.inl (witnessBalanceNeighborPositions hk z s hs i)))).val.2) ↔
    (∀ i, (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s) (g i)).val.2 =
      (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s) i).val.2)
  simp only [witnessBalance_neighbor_positions_cell hk z s hs,Nat.add_left_cancel_iff]

/-- The same prescribed component generator, via inverse positional transport
and a row-letter cast. -/
theorem witnessBalance_neighbor_component_word :
    witnessBalanceComponentWord hk z (3+s) =
    positionRelabel (witnessBalanceNeighborPositions hk z s hs)
      (letterLift (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs)
        (polytabloid (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)))) := by
  funext w
  let E := witnessBalanceNeighborPositions hk z s hs
  let c := fun i => (z ((witnessBalanceComponentCut hk z (3+s)).symm (.inl i))).val.2
  let a := leftWord (witnessBalanceComponentCut hk z (3+s)) (rowWord z)
  have he := altWord_fiber_relabel E c a (w ∘ E)
  have hw : (w ∘ E) ∘ E.symm=w := by funext i; simp
  rw [hw] at he
  have hG : fiberGroup (c ∘ E)=
      columnGroup (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)) :=
    witnessBalance_neighbor_full_column_fiber hk z s hs
  have hA : a ∘ E=witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs ∘
      rowWord (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)) :=
    witnessBalance_neighbor_row_word hk z s hs
  rw [hG,hA] at he
  change altWord (fiberGroup c) a w =
    letterLift (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs)
      (polytabloid (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))) (w ∘ E)
  rw [polytabloid_eq_altWord,letterLift_altWord]
  exact he

/-- The letter/position embedding of the full position group. -/
def witnessBalanceNeighborWordMap :=
  (positionRelabelIntertwiner (witnessBalanceNeighborPositions hk z s hs)).comp
    (letterLift (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs))

theorem witnessBalanceNeighborWordMap_injective :
    Function.Injective (witnessBalanceNeighborWordMap hk z s hs) :=
  (positionRelabel (witnessBalanceNeighborPositions hk z s hs)).injective.comp
    (letterLift_injective (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs)
      (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs).injective)

theorem witnessBalanceNeighborWordMap_generator :
    witnessBalanceNeighborWordMap hk z s hs
      (polytabloid (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)))=
        witnessBalanceComponentWord hk z (3+s) :=
  (witnessBalance_neighbor_component_word hk z s hs).symm

/-- The output key; this is not a packing or Specht support statement. -/
theorem witnessBalance_neighbor_output_iff (x : ℕ) (hx : 0<x) :
    x≤k ∧ witnessBalanceOutputLabel k delta x=3+s ↔
      witnessBalanceNeighborSize (k:=k) s≤x ∧ x≤witnessBalanceNeighborSize (k:=k) s+1 := by
  have hcut : k-(2+delta)≤k-2 := Nat.sub_le_sub_left (by omega) k
  have hks : 2*s+4≤k := by omega
  unfold witnessBalanceNeighborSize witnessBalanceOutputLabel
  split_ifs <;> omega

theorem witnessBalance_neighbor_native_guard : 2≤witnessBalanceNeighborSize (k:=k) s := by
  have hcut : k-(2+delta)≤k-2 := Nat.sub_le_sub_left (by omega) k
  unfold witnessBalanceNeighborSize
  omega

def witnessBalanceNeighborPairLetter
    (x : Fin ((witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0 *
      (witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0)) :
    Fin (witnessBalancePairDim k b delta hk) :=
  finProdFinEquiv
    (witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs
      (finProdFinEquiv.symm x).1,
     witnessBalanceNeighborRowLetter (k:=k) (b:=b) (delta:=delta) hk s hs
      (finProdFinEquiv.symm x).2)

theorem witnessBalance_neighbor_pair_output (x) :
    balancePairOutput (witnessBalanceNeighborPairLetter (k:=k) (b:=b) (delta:=delta) hk s hs x)=
      balancePairOutput x := by
  simp only [witnessBalanceNeighborPairLetter,balancePairOutput,Equiv.symm_apply_apply]
  rfl

/-- All native paired words, keeping both letters: the local filter holds iff
the output lies in the interval. This is not a projected-module support map. -/
theorem witnessBalance_neighbor_pair_filter
    (w : Fin (2*witnessBalanceNeighborSize (k:=k) s+1) →
      Fin ((witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0 *
        (witnessAttachment (witnessBalanceNeighborSize (k:=k) s) 1).transpose.colLen 0)) :
    witnessBalanceLocalPairWords hk z (3+s)
      (witnessBalanceNeighborPairLetter (k:=k) (b:=b) (delta:=delta) hk s hs ∘ w ∘
        (witnessBalanceNeighborPositions hk z s hs).symm) ↔
    balanceInOutputs (Set.Icc (witnessBalanceNeighborSize (k:=k) s)
      (witnessBalanceNeighborSize (k:=k) s+1)) w := by
  let E := witnessBalanceNeighborPositions hk z s hs
  change ((∀ i, balancePairOutput (witnessBalanceNeighborPairLetter (k:=k) (b:=b) (delta:=delta) hk s hs (w (E.symm i)))≤k) ∧
    ∀ i, witnessBalanceOutputLabel k delta
      (balancePairOutput (witnessBalanceNeighborPairLetter (k:=k) (b:=b) (delta:=delta) hk s hs (w (E.symm i))))=3+s) ↔
      ∀ i, balancePairOutput (w i)∈Set.Icc (witnessBalanceNeighborSize (k:=k) s)
        (witnessBalanceNeighborSize (k:=k) s+1)
  simp only [witnessBalance_neighbor_pair_output,Set.mem_Icc]
  have hp (i) : 0<balancePairOutput (w i) := by unfold balancePairOutput; omega
  constructor
  · rintro ⟨hA,hL⟩ i
    apply (witnessBalance_neighbor_output_iff (k:=k) (delta:=delta) s hs _ (hp i)).mp
    simpa only [Equiv.symm_apply_apply] using And.intro (hA (E i)) (hL (E i))
  · intro hw
    constructor <;> intro i
    · exact ((witnessBalance_neighbor_output_iff (k:=k) (delta:=delta) s hs _ (hp (E.symm i))).mpr (hw (E.symm i))).1
    · exact ((witnessBalance_neighbor_output_iff (k:=k) (delta:=delta) s hs _ (hp (E.symm i))).mpr (hw (E.symm i))).2

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_neighbor_positions_cell
#print axioms HSTZ.witnessBalance_neighbor_positions_inverse
#print axioms HSTZ.witnessBalance_neighbor_rows_bound
#print axioms HSTZ.witnessBalance_neighbor_row_word
#print axioms HSTZ.witnessBalance_neighbor_full_column_fiber
#print axioms HSTZ.witnessBalance_neighbor_component_word
#print axioms HSTZ.witnessBalanceNeighborWordMap_injective
#print axioms HSTZ.witnessBalanceNeighborWordMap_generator
#print axioms HSTZ.witnessBalance_neighbor_output_iff
#print axioms HSTZ.witnessBalance_neighbor_native_guard
#print axioms HSTZ.witnessBalance_neighbor_pair_output
#print axioms HSTZ.witnessBalance_neighbor_pair_filter
