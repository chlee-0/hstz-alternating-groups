import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalanceUnmatchedCells
import HSTZ.LetterLift

/-! Unmatched row casts, the component generator and the full Specht map in the
original component C_{3+s}. Reuses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0)
and the existing transport pattern for the twos component. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (s : ℕ) (hd : delta≤1) (hs : k-(2+delta)=2*s+1)

include hk hd hs

theorem witnessBalance_unmatched_rows_bound :
    (oneRowDiagram (k-2*s)).transpose.colLen 0≤(witnessDiagram k b delta hk).colLen 0 := by
  have h : (oneRowDiagram (k-2*s)).transpose.colLen 0≤k-2*s := by
    by_contra hn
    have hm : (k-2*s,0)∈(oneRowDiagram (k-2*s)).transpose :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    rw [YoungDiagram.mem_transpose,mem_oneRowDiagram] at hm
    change (0:ℕ)=0 ∧ (k-2*s:ℕ)<k-2*s at hm
    omega
  rw [witnessDiagram_height]
  exact h.trans (by omega)

def witnessBalanceUnmatchedRowLetter :
    Fin ((oneRowDiagram (k-2*s)).transpose.colLen 0) ↪
      Fin ((witnessDiagram k b delta hk).colLen 0) where
  toFun i := ⟨i.val,lt_of_lt_of_le i.isLt (witnessBalance_unmatched_rows_bound (k:=k) (b:=b) hk s hd hs)⟩
  inj' i j h := by
    apply Fin.ext
    exact congrArg (fun t : Fin ((witnessDiagram k b delta hk).colLen 0) => t.val) h

theorem witnessBalance_unmatched_row_word :
    leftWord (witnessBalanceComponentCut hk z (3+s)) (rowWord z) ∘
      witnessBalanceUnmatchedPositions hk z s hd hs =
    witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs ∘
      rowWord (balanceSingletonTableau (k-2*s)) := by
  funext i
  apply Fin.ext
  have he := witnessBalance_unmatched_positions_cell hk z s hd hs i
  have hr := congrArg Prod.fst he
  change (z ((witnessBalanceComponentCut hk z (3+s)).symm
    (.inl (witnessBalanceUnmatchedPositions hk z s hd hs i)))).val.1 =
    (balanceSingletonTableau (k-2*s) i).val.1
  exact hr

/-- The prescribed component generator, via inverse positional transport and the
row-letter cast. -/
theorem witnessBalance_unmatched_component_word :
    witnessBalanceComponentWord hk z (3+s) =
    positionRelabel (witnessBalanceUnmatchedPositions hk z s hd hs)
      (letterLift (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs)
        (polytabloid (balanceSingletonTableau (k-2*s)))) := by
  funext w
  let E := witnessBalanceUnmatchedPositions hk z s hd hs
  let c := fun i => (z ((witnessBalanceComponentCut hk z (3+s)).symm (.inl i))).val.2
  let a := leftWord (witnessBalanceComponentCut hk z (3+s)) (rowWord z)
  have he := altWord_fiber_relabel E c a (w ∘ E)
  have hw : (w ∘ E) ∘ E.symm=w := by funext i; simp
  rw [hw] at he
  have hG : fiberGroup (c ∘ E)=
      columnGroup (balanceSingletonTableau (k-2*s)) :=
    witnessBalance_unmatched_full_column_fiber hk z s hd hs
  have hA : a ∘ E=witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs ∘
      rowWord (balanceSingletonTableau (k-2*s)) :=
    witnessBalance_unmatched_row_word hk z s hd hs
  rw [hG,hA] at he
  change altWord (fiberGroup c) a w =
    letterLift (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs)
      (polytabloid (balanceSingletonTableau (k-2*s))) (w ∘ E)
  rw [polytabloid_eq_altWord,letterLift_altWord]
  exact he

/-- Letter/position embedding for the full position group, defined directly. -/
def witnessBalanceUnmatchedWordMap :=
  (positionRelabelIntertwiner (witnessBalanceUnmatchedPositions hk z s hd hs)).comp
    (letterLift (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs))

theorem witnessBalanceUnmatchedWordMap_injective :
    Function.Injective (witnessBalanceUnmatchedWordMap hk z s hd hs) :=
  (positionRelabel (witnessBalanceUnmatchedPositions hk z s hd hs)).injective.comp
    (letterLift_injective (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs)
      (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs).injective)

theorem witnessBalanceUnmatchedWordMap_generator :
    witnessBalanceUnmatchedWordMap hk z s hd hs
      (polytabloid (balanceSingletonTableau (k-2*s)))=
        witnessBalanceComponentWord hk z (3+s) :=
  (witnessBalance_unmatched_component_word hk z s hd hs).symm

private theorem unmatched_carrier_mem
    (x : Specht (balanceSingletonTableau (k-2*s))) :
    witnessBalanceUnmatchedWordMap hk z s hd hs x.val ∈
      (witnessBalanceComponentRows hk z (3+s)).toSubmodule := by
  have hx : x.val ∈ cyclicSpan (wordRep _ _)
      (polytabloid (balanceSingletonTableau (k-2*s))) := x.property
  have he := cyclicSpan_apply_mem (witnessBalanceUnmatchedWordMap hk z s hd hs)
    (polytabloid (balanceSingletonTableau (k-2*s))) hx
  rw [witnessBalanceUnmatchedWordMap_generator] at he
  rw [cyclicSpan_comp_surjective _ _
    (positionPermHom_bijective (witnessBalanceUnmatchedPositions hk z s hd hs)).2] at he
  exact he

/-- The full local Specht map into the full component cyclic carrier. -/
def witnessBalanceUnmatchedSpechtMap : Representation.IntertwiningMap
    (spechtRep (balanceSingletonTableau (k-2*s)))
    ((witnessBalanceComponentRows hk z (3+s)).toRepresentation.comp
      (positionPermHom (witnessBalanceUnmatchedPositions hk z s hd hs))) where
  toLinearMap := ((witnessBalanceUnmatchedWordMap hk z s hd hs).toLinearMap.domRestrict
    (spechtSub (balanceSingletonTableau (k-2*s))).toSubmodule).codRestrict
      (witnessBalanceComponentRows hk z (3+s)).toSubmodule (unmatched_carrier_mem hk z s hd hs)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBalanceUnmatchedWordMap hk z s hd hs).map_action g x.val

theorem witnessBalanceUnmatchedSpechtMap_injective :
    Function.Injective (witnessBalanceUnmatchedSpechtMap hk z s hd hs) := by
  intro x y h
  apply Subtype.ext
  exact witnessBalanceUnmatchedWordMap_injective hk z s hd hs (congrArg Subtype.val h)

theorem witnessBalanceUnmatchedSpechtMap_generator :
    (witnessBalanceUnmatchedSpechtMap hk z s hd hs
      ⟨polytabloid (balanceSingletonTableau (k-2*s)),mem_cyclic _ _⟩).val=
        witnessBalanceComponentWord hk z (3+s) :=
  witnessBalanceUnmatchedWordMap_generator hk z s hd hs

include hk hd hs in
theorem witnessBalance_unmatched_output_iff (x : ℕ) (hx : 0<x) :
    x≤k ∧ witnessBalanceOutputLabel k delta x=3+s ↔ x=k-2*s := by
  constructor
  · rintro ⟨hA,hL⟩
    unfold witnessBalanceOutputLabel at hL
    split_ifs at hL <;> omega
  · rintro rfl
    constructor
    · omega
    · have hheight : k-2*s=3+delta := witnessBalance_unmatched_height hk s hd hs
      unfold witnessBalanceOutputLabel
      split_ifs <;> omega

def witnessBalanceUnmatchedPairLetter
    (x : Fin ((oneRowDiagram (k-2*s)).transpose.colLen 0 * (oneRowDiagram (k-2*s)).transpose.colLen 0)) :
    Fin (witnessBalancePairDim k b delta hk) :=
  finProdFinEquiv
    (witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs (finProdFinEquiv.symm x).1,
     witnessBalanceUnmatchedRowLetter (k:=k) (b:=b) hk s hd hs (finProdFinEquiv.symm x).2)

theorem witnessBalance_unmatched_pair_output (x) :
    balancePairOutput (witnessBalanceUnmatchedPairLetter (k:=k) (b:=b) hk s hd hs x)=balancePairOutput x := by
  simp only [witnessBalanceUnmatchedPairLetter,balancePairOutput,Equiv.symm_apply_apply]
  rfl

/-- All paired words, keeping both letters and `E.symm`. -/
theorem witnessBalance_unmatched_pair_filter
    (w : Fin (k-2*s) → Fin ((oneRowDiagram (k-2*s)).transpose.colLen 0 * (oneRowDiagram (k-2*s)).transpose.colLen 0)) :
    witnessBalanceLocalPairWords hk z (3+s)
      (witnessBalanceUnmatchedPairLetter (k:=k) (b:=b) hk s hd hs ∘ w ∘
        (witnessBalanceUnmatchedPositions hk z s hd hs).symm) ↔
    balanceInOutputs ({k-2*s} : Set ℕ) w := by
  let E := witnessBalanceUnmatchedPositions hk z s hd hs
  change ((∀ i, balancePairOutput (witnessBalanceUnmatchedPairLetter (k:=k) (b:=b) hk s hd hs (w (E.symm i)))≤k) ∧
    ∀ i, witnessBalanceOutputLabel k delta
      (balancePairOutput (witnessBalanceUnmatchedPairLetter (k:=k) (b:=b) hk s hd hs (w (E.symm i))))=3+s) ↔
      ∀ i, balancePairOutput (w i)∈({k-2*s} : Set ℕ)
  simp only [witnessBalance_unmatched_pair_output,Set.mem_singleton_iff]
  have hp (i) : 0<balancePairOutput (w i) := by unfold balancePairOutput; omega
  constructor
  · rintro ⟨hA,hL⟩ i
    apply (witnessBalance_unmatched_output_iff (k:=k) hk s hd hs _ (hp i)).mp
    simpa only [Equiv.symm_apply_apply] using And.intro (hA (E i)) (hL (E i))
  · intro hw
    constructor <;> intro i
    · exact ((witnessBalance_unmatched_output_iff (k:=k) hk s hd hs _ (hp (E.symm i))).mpr (hw (E.symm i))).1
    · exact ((witnessBalance_unmatched_output_iff (k:=k) hk s hd hs _ (hp (E.symm i))).mpr (hw (E.symm i))).2

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceUnmatchedWordMap_injective
#print axioms HSTZ.witnessBalanceUnmatchedWordMap_generator
#print axioms HSTZ.witnessBalanceUnmatchedSpechtMap
#print axioms HSTZ.witnessBalanceUnmatchedSpechtMap_injective
#print axioms HSTZ.witnessBalanceUnmatchedSpechtMap_generator

#print axioms HSTZ.witnessBalance_unmatched_rows_bound
#print axioms HSTZ.witnessBalance_unmatched_row_word
#print axioms HSTZ.witnessBalance_unmatched_component_word
#print axioms HSTZ.witnessBalance_unmatched_output_iff
#print axioms HSTZ.witnessBalance_unmatched_pair_output
#print axioms HSTZ.witnessBalance_unmatched_pair_filter
