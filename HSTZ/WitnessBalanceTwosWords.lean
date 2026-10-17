import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalanceTwosCells
import HSTZ.LetterLift

/-! Transport from the native ordered two-row tableau to the positions, letters
and columns of the label-0 (twos) component of the witness. Uses the fiber relabel
and letter lift calculation from OpenAI's `math` repository (commit adc7f1241,
Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

theorem witnessBalance_twos_positions_cell
    (i : Fin ((witnessAttachment (b+1) 0).card)) :
    (z ((witnessBalanceComponentCut hk z 0).symm
      (.inl (witnessBalanceTwosPositions hk z i)))).val =
    ((balanceOutputTwoTableau (b+1) i).val.1,
      (k-2)+(balanceOutputTwoTableau (b+1) i).val.2) := by
  change (z (((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=0}).symm
    ((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=0})
      (witnessBalanceTwosCells hk z
        (balanceOutputTwoTableau (b+1) i)))).val)).val = _
  rw [Equiv.symm_apply_apply]
  change (z (z.symm _)).val=_
  rw [z.apply_symm_apply]

theorem witnessBalance_twos_positions_inverse
    (i : Fin (witnessBalanceComponentSize hk z 0)) :
    (balanceOutputTwoTableau (b+1)
      ((witnessBalanceTwosPositions hk z).symm i)).val =
    ((z ((witnessBalanceComponentCut hk z 0).symm (.inl i))).val.1,
      (z ((witnessBalanceComponentCut hk z 0).symm (.inl i))).val.2-(k-2)) := by
  have he := witnessBalance_twos_positions_cell hk z
    ((witnessBalanceTwosPositions hk z).symm i)
  rw [Equiv.apply_symm_apply] at he
  have hr := congrArg Prod.fst he
  have hc := congrArg Prod.snd he
  exact Prod.ext hr.symm (by omega)

theorem witnessBalance_twos_rows_bound :
    (witnessAttachment (b+1) 0).colLen 0 ≤ (witnessDiagram k b delta hk).colLen 0 := by
  rw [witnessDiagram_height]
  exact (witnessAttachment_rows (b+1) 0).trans (by omega)

def witnessBalanceTwosRowLetter :
    Fin ((witnessAttachment (b+1) 0).colLen 0) ↪
      Fin ((witnessDiagram k b delta hk).colLen 0) where
  toFun i := ⟨i.val,lt_of_lt_of_le i.isLt (witnessBalance_twos_rows_bound (k:=k) (b:=b) (delta:=delta) hk)⟩
  inj' i j h := by
    apply Fin.ext
    exact congrArg (fun t : Fin ((witnessDiagram k b delta hk).colLen 0) => t.val) h

theorem witnessBalance_twos_row_word :
    leftWord (witnessBalanceComponentCut hk z 0) (rowWord z) ∘
      witnessBalanceTwosPositions hk z =
    witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk ∘
      rowWord (balanceOutputTwoTableau (b+1)) := by
  funext i
  apply Fin.ext
  have he := witnessBalance_twos_positions_cell hk z i
  have hr := congrArg Prod.fst he
  change (z ((witnessBalanceComponentCut hk z 0).symm
    (.inl (witnessBalanceTwosPositions hk z i)))).val.1 =
    (balanceOutputTwoTableau (b+1) i).val.1
  exact hr

theorem witnessBalance_twos_full_column_fiber :
    fiberGroup (fun i => (z ((witnessBalanceComponentCut hk z 0).symm
      (.inl (witnessBalanceTwosPositions hk z i)))).val.2) =
    columnGroup (balanceOutputTwoTableau (b+1)) := by
  ext g
  change (∀ i, (z ((witnessBalanceComponentCut hk z 0).symm
    (.inl (witnessBalanceTwosPositions hk z (g i))))).val.2 =
    (z ((witnessBalanceComponentCut hk z 0).symm
      (.inl (witnessBalanceTwosPositions hk z i)))).val.2) ↔
    (∀ i, (balanceOutputTwoTableau (b+1) (g i)).val.2 =
      (balanceOutputTwoTableau (b+1) i).val.2)
  simp only [witnessBalance_twos_positions_cell hk z,Nat.add_left_cancel_iff]

/-- The component generator is the letter-lifted polytabloid, relabelled along the
component positions. -/
theorem witnessBalance_twos_component_word :
    witnessBalanceComponentWord hk z 0 =
    positionRelabel (witnessBalanceTwosPositions hk z)
      (letterLift (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk)
        (polytabloid (balanceOutputTwoTableau (b+1)))) := by
  funext w
  let E := witnessBalanceTwosPositions hk z
  let c := fun i => (z ((witnessBalanceComponentCut hk z 0).symm (.inl i))).val.2
  let a := leftWord (witnessBalanceComponentCut hk z 0) (rowWord z)
  have he := altWord_fiber_relabel E c a (w ∘ E)
  have hw : (w ∘ E) ∘ E.symm=w := by funext i; simp
  rw [hw] at he
  have hG : fiberGroup (c ∘ E)=
      columnGroup (balanceOutputTwoTableau (b+1)) :=
    witnessBalance_twos_full_column_fiber hk z
  have hA : a ∘ E=witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk ∘
      rowWord (balanceOutputTwoTableau (b+1)) :=
    witnessBalance_twos_row_word hk z
  rw [hG,hA] at he
  change altWord (fiberGroup c) a w =
    letterLift (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk)
      (polytabloid (balanceOutputTwoTableau (b+1))) (w ∘ E)
  rw [polytabloid_eq_altWord,letterLift_altWord]
  exact he

/-- The letter-lift and position-relabel embedding. -/
def witnessBalanceTwosWordMap :=
  (positionRelabelIntertwiner (witnessBalanceTwosPositions hk z)).comp
    (letterLift (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk))

theorem witnessBalanceTwosWordMap_injective :
    Function.Injective (witnessBalanceTwosWordMap hk z) :=
  (positionRelabel (witnessBalanceTwosPositions hk z)).injective.comp
    (letterLift_injective (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk).injective)

theorem witnessBalanceTwosWordMap_generator :
    witnessBalanceTwosWordMap hk z
      (polytabloid (balanceOutputTwoTableau (b+1)))=
        witnessBalanceComponentWord hk z 0 :=
  (witnessBalance_twos_component_word hk z).symm

include hk in
/-- The label-0 selector picks exactly the output value 2. -/
theorem witnessBalance_twos_output_iff (x : ℕ) (hx : 0<x) :
    x≤k ∧ witnessBalanceOutputLabel k delta x=0 ↔ x=2 := by
  constructor
  · rintro ⟨hA,hL⟩
    unfold witnessBalanceOutputLabel at hL
    split_ifs at hL <;> omega
  · rintro rfl
    constructor
    · omega
    · simp [witnessBalanceOutputLabel]

def witnessBalanceTwosPairLetter
    (x : Fin ((witnessAttachment (b+1) 0).colLen 0 *
      (witnessAttachment (b+1) 0).colLen 0)) :
    Fin (witnessBalancePairDim k b delta hk) :=
  finProdFinEquiv
    (witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk
      (finProdFinEquiv.symm x).1,
     witnessBalanceTwosRowLetter (k:=k) (b:=b) (delta:=delta) hk
      (finProdFinEquiv.symm x).2)

theorem witnessBalance_twos_pair_output (x) :
    balancePairOutput (witnessBalanceTwosPairLetter (k:=k) (b:=b) (delta:=delta) hk x)=
      balancePairOutput x := by
  simp only [witnessBalanceTwosPairLetter,balancePairOutput,Equiv.symm_apply_apply]
  rfl

/-- Characterization of the native paired words selected by the local filter,
keeping both letters and the inverse positions. -/
theorem witnessBalance_twos_pair_filter
    (w : Fin (witnessAttachment (b+1) 0).card →
      Fin ((witnessAttachment (b+1) 0).colLen 0 * (witnessAttachment (b+1) 0).colLen 0)) :
    witnessBalanceLocalPairWords hk z 0
      (witnessBalanceTwosPairLetter (k:=k) (b:=b) (delta:=delta) hk ∘ w ∘
        (witnessBalanceTwosPositions hk z).symm) ↔
    balanceInOutputs ({2} : Set ℕ) w := by
  let E := witnessBalanceTwosPositions hk z
  change ((∀ i, balancePairOutput (witnessBalanceTwosPairLetter (k:=k) (b:=b) (delta:=delta) hk (w (E.symm i)))≤k) ∧
    ∀ i, witnessBalanceOutputLabel k delta
      (balancePairOutput (witnessBalanceTwosPairLetter (k:=k) (b:=b) (delta:=delta) hk (w (E.symm i))))=0) ↔
      ∀ i, balancePairOutput (w i)∈({2} : Set ℕ)
  simp only [witnessBalance_twos_pair_output,Set.mem_singleton_iff]
  have hp (i) : 0<balancePairOutput (w i) := by unfold balancePairOutput; omega
  constructor
  · rintro ⟨hA,hL⟩ i
    apply (witnessBalance_twos_output_iff (k:=k) (delta:=delta) hk _ (hp i)).mp
    simpa only [Equiv.symm_apply_apply] using And.intro (hA (E i)) (hL (E i))
  · intro hw
    constructor <;> intro i
    · exact ((witnessBalance_twos_output_iff (k:=k) (delta:=delta) hk _ (hp (E.symm i))).mpr (hw (E.symm i))).1
    · exact ((witnessBalance_twos_output_iff (k:=k) (delta:=delta) hk _ (hp (E.symm i))).mpr (hw (E.symm i))).2

private theorem twos_carrier_mem
    (x : Specht (balanceOutputTwoTableau (b+1))) :
    witnessBalanceTwosWordMap hk z x.val ∈
      (witnessBalanceComponentRows hk z 0).toSubmodule := by
  have hx : x.val ∈ cyclicSpan (wordRep _ _)
      (polytabloid (balanceOutputTwoTableau (b+1))) := x.property
  have he := cyclicSpan_apply_mem (witnessBalanceTwosWordMap hk z)
    (polytabloid (balanceOutputTwoTableau (b+1))) hx
  rw [witnessBalanceTwosWordMap_generator] at he
  rw [cyclicSpan_comp_surjective _ _
    (positionPermHom_bijective (witnessBalanceTwosPositions hk z)).2] at he
  exact he

/-- The native local Specht module maps into the component cyclic space. -/
def witnessBalanceTwosSpechtMap : Representation.IntertwiningMap
    (spechtRep (balanceOutputTwoTableau (b+1)))
    ((witnessBalanceComponentRows hk z 0).toRepresentation.comp
      (positionPermHom (witnessBalanceTwosPositions hk z))) where
  toLinearMap := ((witnessBalanceTwosWordMap hk z).toLinearMap.domRestrict
    (spechtSub (balanceOutputTwoTableau (b+1))).toSubmodule).codRestrict
      (witnessBalanceComponentRows hk z 0).toSubmodule (twos_carrier_mem hk z)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBalanceTwosWordMap hk z).map_action g x.val

theorem witnessBalanceTwosSpechtMap_injective :
    Function.Injective (witnessBalanceTwosSpechtMap hk z) := by
  intro x y h
  apply Subtype.ext
  exact witnessBalanceTwosWordMap_injective hk z (congrArg Subtype.val h)

theorem witnessBalanceTwosSpechtMap_generator :
    (witnessBalanceTwosSpechtMap hk z
      ⟨polytabloid (balanceOutputTwoTableau (b+1)),mem_cyclic _ _⟩).val=
        witnessBalanceComponentWord hk z 0 :=
  witnessBalanceTwosWordMap_generator hk z

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_twos_positions_cell
#print axioms HSTZ.witnessBalance_twos_positions_inverse
#print axioms HSTZ.witnessBalance_twos_rows_bound
#print axioms HSTZ.witnessBalance_twos_row_word
#print axioms HSTZ.witnessBalance_twos_full_column_fiber
#print axioms HSTZ.witnessBalance_twos_component_word
#print axioms HSTZ.witnessBalanceTwosWordMap_injective
#print axioms HSTZ.witnessBalanceTwosWordMap_generator
#print axioms HSTZ.witnessBalance_twos_output_iff
#print axioms HSTZ.witnessBalance_twos_pair_output
#print axioms HSTZ.witnessBalance_twos_pair_filter

#print axioms HSTZ.witnessBalanceTwosSpechtMap
#print axioms HSTZ.witnessBalanceTwosSpechtMap_injective
#print axioms HSTZ.witnessBalanceTwosSpechtMap_generator
