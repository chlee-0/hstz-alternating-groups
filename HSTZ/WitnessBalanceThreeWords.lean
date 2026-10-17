import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalanceThreeCells
import HSTZ.LetterLift

/-! The height-three component (label 2, delta = 1): row-letter casts, the
component generator as a transported word, and an embedding of the native Specht
module into the component cyclic space. Follows the same transport pattern as the
twos component. Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b 1 hk))

theorem witnessBalance_three_rows_bound :
    (oneRowDiagram 3).transpose.colLen 0≤(witnessDiagram k b 1 hk).colLen 0 := by
  have h : (oneRowDiagram 3).transpose.colLen 0≤3 := by
    by_contra hn
    have hm : (3,0)∈(oneRowDiagram 3).transpose :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    rw [YoungDiagram.mem_transpose,mem_oneRowDiagram] at hm
    change (0:ℕ)=0 ∧ (3:ℕ)<3 at hm
    omega
  rw [witnessDiagram_height]
  exact h.trans (by omega)

def witnessBalanceThreeRowLetter :
    Fin ((oneRowDiagram 3).transpose.colLen 0) ↪
      Fin ((witnessDiagram k b 1 hk).colLen 0) where
  toFun i := ⟨i.val,lt_of_lt_of_le i.isLt (witnessBalance_three_rows_bound (k:=k) (b:=b) hk)⟩
  inj' i j h := by
    apply Fin.ext
    exact congrArg (fun t : Fin ((witnessDiagram k b 1 hk).colLen 0) => t.val) h

theorem witnessBalance_three_row_word :
    leftWord (witnessBalanceComponentCut hk z 2) (rowWord z) ∘
      witnessBalanceThreePositions hk z =
    witnessBalanceThreeRowLetter (k:=k) (b:=b) hk ∘
      rowWord (balanceSingletonTableau 3) := by
  funext i
  apply Fin.ext
  have he := witnessBalance_three_positions_cell hk z i
  have hr := congrArg Prod.fst he
  change (z ((witnessBalanceComponentCut hk z 2).symm
    (.inl (witnessBalanceThreePositions hk z i)))).val.1 =
    (balanceSingletonTableau 3 i).val.1
  exact hr

/-- The component generator is the letter-lifted polytabloid, relabelled along the
component positions. -/
theorem witnessBalance_three_component_word :
    witnessBalanceComponentWord hk z 2 =
    positionRelabel (witnessBalanceThreePositions hk z)
      (letterLift (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk)
        (polytabloid (balanceSingletonTableau 3))) := by
  funext w
  let E := witnessBalanceThreePositions hk z
  let c := fun i => (z ((witnessBalanceComponentCut hk z 2).symm (.inl i))).val.2
  let a := leftWord (witnessBalanceComponentCut hk z 2) (rowWord z)
  have he := altWord_fiber_relabel E c a (w ∘ E)
  have hw : (w ∘ E) ∘ E.symm=w := by funext i; simp
  rw [hw] at he
  have hG : fiberGroup (c ∘ E)=
      columnGroup (balanceSingletonTableau 3) :=
    witnessBalance_three_full_column_fiber hk z
  have hA : a ∘ E=witnessBalanceThreeRowLetter (k:=k) (b:=b) hk ∘
      rowWord (balanceSingletonTableau 3) :=
    witnessBalance_three_row_word hk z
  rw [hG,hA] at he
  change altWord (fiberGroup c) a w =
    letterLift (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk)
      (polytabloid (balanceSingletonTableau 3)) (w ∘ E)
  rw [polytabloid_eq_altWord,letterLift_altWord]
  exact he

/-- The letter-lift and position-relabel embedding. -/
def witnessBalanceThreeWordMap :=
  (positionRelabelIntertwiner (witnessBalanceThreePositions hk z)).comp
    (letterLift (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk))

theorem witnessBalanceThreeWordMap_injective :
    Function.Injective (witnessBalanceThreeWordMap hk z) :=
  (positionRelabel (witnessBalanceThreePositions hk z)).injective.comp
    (letterLift_injective (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk)
      (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk).injective)

theorem witnessBalanceThreeWordMap_generator :
    witnessBalanceThreeWordMap hk z
      (polytabloid (balanceSingletonTableau 3))=
        witnessBalanceComponentWord hk z 2 :=
  (witnessBalance_three_component_word hk z).symm

private theorem three_carrier_mem
    (x : Specht (balanceSingletonTableau 3)) :
    witnessBalanceThreeWordMap hk z x.val ∈
      (witnessBalanceComponentRows hk z 2).toSubmodule := by
  have hx : x.val ∈ cyclicSpan (wordRep _ _)
      (polytabloid (balanceSingletonTableau 3)) := x.property
  have he := cyclicSpan_apply_mem (witnessBalanceThreeWordMap hk z)
    (polytabloid (balanceSingletonTableau 3)) hx
  rw [witnessBalanceThreeWordMap_generator] at he
  rw [cyclicSpan_comp_surjective _ _
    (positionPermHom_bijective (witnessBalanceThreePositions hk z)).2] at he
  exact he

/-- The native local Specht module maps into the component cyclic space. -/
def witnessBalanceThreeSpechtMap : Representation.IntertwiningMap
    (spechtRep (balanceSingletonTableau 3))
    ((witnessBalanceComponentRows hk z 2).toRepresentation.comp
      (positionPermHom (witnessBalanceThreePositions hk z))) where
  toLinearMap := ((witnessBalanceThreeWordMap hk z).toLinearMap.domRestrict
    (spechtSub (balanceSingletonTableau 3)).toSubmodule).codRestrict
      (witnessBalanceComponentRows hk z 2).toSubmodule (three_carrier_mem hk z)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBalanceThreeWordMap hk z).map_action g x.val

theorem witnessBalanceThreeSpechtMap_injective :
    Function.Injective (witnessBalanceThreeSpechtMap hk z) := by
  intro x y h
  apply Subtype.ext
  exact witnessBalanceThreeWordMap_injective hk z (congrArg Subtype.val h)

theorem witnessBalanceThreeSpechtMap_generator :
    (witnessBalanceThreeSpechtMap hk z
      ⟨polytabloid (balanceSingletonTableau 3),mem_cyclic _ _⟩).val=
        witnessBalanceComponentWord hk z 2 :=
  witnessBalanceThreeWordMap_generator hk z

include hk in
theorem witnessBalance_three_output_iff (x : ℕ) (hx : 0<x) :
    x≤k ∧ witnessBalanceOutputLabel k 1 x=2 ↔ x=3 := by
  constructor
  · rintro ⟨hA,hL⟩
    unfold witnessBalanceOutputLabel at hL
    split_ifs at hL <;> omega
  · rintro rfl
    constructor
    · omega
    · simp [witnessBalanceOutputLabel]

def witnessBalanceThreePairLetter
    (x : Fin ((oneRowDiagram 3).transpose.colLen 0 * (oneRowDiagram 3).transpose.colLen 0)) :
    Fin (witnessBalancePairDim k b 1 hk) :=
  finProdFinEquiv
    (witnessBalanceThreeRowLetter (k:=k) (b:=b) hk (finProdFinEquiv.symm x).1,
     witnessBalanceThreeRowLetter (k:=k) (b:=b) hk (finProdFinEquiv.symm x).2)

theorem witnessBalance_three_pair_output (x) :
    balancePairOutput (witnessBalanceThreePairLetter (k:=k) (b:=b) hk x)=balancePairOutput x := by
  simp only [witnessBalanceThreePairLetter,balancePairOutput,Equiv.symm_apply_apply]
  rfl

/-- Characterization of the native paired words selected by the local filter,
keeping both letters and the inverse positions `E.symm`. -/
theorem witnessBalance_three_pair_filter
    (w : Fin 3 → Fin ((oneRowDiagram 3).transpose.colLen 0 * (oneRowDiagram 3).transpose.colLen 0)) :
    witnessBalanceLocalPairWords hk z 2
      (witnessBalanceThreePairLetter (k:=k) (b:=b) hk ∘ w ∘
        (witnessBalanceThreePositions hk z).symm) ↔
    balanceInOutputs ({3} : Set ℕ) w := by
  let E := witnessBalanceThreePositions hk z
  change ((∀ i, balancePairOutput (witnessBalanceThreePairLetter (k:=k) (b:=b) hk (w (E.symm i)))≤k) ∧
    ∀ i, witnessBalanceOutputLabel k 1
      (balancePairOutput (witnessBalanceThreePairLetter (k:=k) (b:=b) hk (w (E.symm i))))=2) ↔
      ∀ i, balancePairOutput (w i)∈({3} : Set ℕ)
  simp only [witnessBalance_three_pair_output,Set.mem_singleton_iff]
  have hp (i) : 0<balancePairOutput (w i) := by unfold balancePairOutput; omega
  constructor
  · rintro ⟨hA,hL⟩ i
    apply (witnessBalance_three_output_iff (k:=k) hk _ (hp i)).mp
    simpa only [Equiv.symm_apply_apply] using And.intro (hA (E i)) (hL (E i))
  · intro hw
    constructor <;> intro i
    · exact ((witnessBalance_three_output_iff (k:=k) hk _ (hp (E.symm i))).mpr (hw (E.symm i))).1
    · exact ((witnessBalance_three_output_iff (k:=k) hk _ (hp (E.symm i))).mpr (hw (E.symm i))).2

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_three_rows_bound
#print axioms HSTZ.witnessBalance_three_row_word
#print axioms HSTZ.witnessBalance_three_component_word
#print axioms HSTZ.witnessBalanceThreeWordMap_injective
#print axioms HSTZ.witnessBalanceThreeWordMap_generator
#print axioms HSTZ.witnessBalanceThreeSpechtMap
#print axioms HSTZ.witnessBalanceThreeSpechtMap_injective
#print axioms HSTZ.witnessBalanceThreeSpechtMap_generator

#print axioms HSTZ.witnessBalance_three_output_iff
#print axioms HSTZ.witnessBalance_three_pair_output
#print axioms HSTZ.witnessBalance_three_pair_filter
