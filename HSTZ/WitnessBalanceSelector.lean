import HSTZ.WitnessBalanceOrder
import HSTZ.WitnessBalanceProjectedRange

/-! The pair alphabet and equality of the original and ordered selectors,
following the balance-projection route of OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The original component group, carrier and source and both pair letters are kept. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev witnessBalancePairDim (k b delta : ℕ) (hk : 5 ≤ k) :=
  (witnessDiagram k b delta hk).colLen 0 * (witnessDiagram k b delta hk).colLen 0

section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

def witnessBalancePairAllowed (a : Fin (witnessBalancePairDim k b delta hk)) : Prop :=
  balancePairOutput a ≤ k

def witnessBalancePairLabel (a : Fin (witnessBalancePairDim k b delta hk)) : ℕ :=
  witnessBalanceOutputLabel k delta (balancePairOutput a)

def witnessBalancePairOrderedLabel (a : Fin (witnessBalancePairDim k b delta hk)) : ℕ :=
  witnessBalanceOrderedOutputLabel k delta (balancePairOutput a)

def witnessBalanceRetainedWords (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) : Prop :=
  witnessBalanceComponentWords hk z (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk) (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk) w

def witnessBalanceOrderedRetainedWords (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) : Prop :=
  (∀ i, witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk (w i)) ∧
    ∀ i, witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w i) = witnessBalanceOrderedLabel hk z i

theorem witnessBalance_retained_relabel (hd : delta ≤ 1)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalanceOrderedRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w ↔ witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w := by
  constructor
  · rintro ⟨hA,hl⟩
    refine ⟨hA,fun i => ?_⟩
    exact (witnessBalance_output_component_iff k b delta (z i).val.2
      (balancePairOutput (w i)) hk hd (by unfold balancePairOutput; omega) (hA i)).mp (hl i)
  · rintro ⟨hA,hl⟩
    refine ⟨hA,fun i => ?_⟩
    exact (witnessBalance_output_component_iff k b delta (z i).val.2
      (balancePairOutput (w i)) hk hd (by unfold balancePairOutput; omega) (hA i)).mpr (hl i)

theorem witnessBalance_retained_projection_relabel (hd : delta ≤ 1) :
    coordinateProjection (witnessBalanceOrderedRetainedWords (k:=k) (b:=b) (delta:=delta) hk z) =
      coordinateProjection (witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z) := by
  classical
  apply LinearMap.ext
  intro x
  funext w
  simp only [coordinateProjection_apply,witnessBalance_retained_relabel (k:=k) (b:=b) (delta:=delta) hk z hd]

theorem witnessBalance_pair_order (hd : delta ≤ 1)
    (a a' : Fin (witnessBalancePairDim k b delta hk))
    (ha : witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk a) (ha' : witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk a')
    (ho : witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk a < witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk a') :
    balancePairOutput a < balancePairOutput a' :=
  witnessBalance_output_order k delta _ _ hk hd
    (by unfold balancePairOutput; omega) ha (by unfold balancePairOutput; omega) ha' ho

def witnessBalanceOrderedPositions (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => witnessBalanceOrderedLabel hk z i = j)

def witnessBalanceOrderedSum (j : ℕ) : ℤ :=
  ∑ i ∈ witnessBalanceOrderedPositions (k:=k) (b:=b) (delta:=delta) hk z j, (2*((rowWord z i).val : ℤ)+1)

theorem witnessBalance_ordered_position_fiber (hd : delta ≤ 1) (i : Fin n) :
    witnessBalanceOrderedPositions (k:=k) (b:=b) (delta:=delta) hk z (witnessBalanceOrderedLabel hk z i) =
      witnessBalancePositions hk z (witnessBalanceLabel hk z i) := by
  classical
  ext p
  simp only [witnessBalanceOrderedPositions,witnessBalancePositions,Finset.mem_filter,
    Finset.mem_univ,true_and]
  exact witnessBalance_ordered_column_fibers k b delta _ _ hk hd

/-- Ordered sums for all vectors follow from the same original component
carrier. Empty fibers need no representative or origin. -/
theorem witnessBalance_ordered_sums (hd : delta ≤ 1)
    (x : WordSpace n (witnessBalancePairDim k b delta hk))
    (hx : x ∈ witnessBalanceFixedOutputs hk z)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) (hw : x w ≠ 0) (j : ℕ) :
    (∑ i ∈ witnessBalanceOrderedPositions (k:=k) (b:=b) (delta:=delta) hk z j, (balancePairOutput (w i) : ℤ)) =
      witnessBalanceOrderedSum (k:=k) (b:=b) (delta:=delta) hk z j := by
  classical
  by_cases hn : (witnessBalanceOrderedPositions (k:=k) (b:=b) (delta:=delta) hk z j).Nonempty
  · obtain ⟨i,hi⟩ := hn
    have hj : witnessBalanceOrderedLabel hk z i=j := (Finset.mem_filter.mp hi).2
    have he : witnessBalanceOrderedPositions (k:=k) (b:=b) (delta:=delta) hk z j =
        witnessBalancePositions hk z (witnessBalanceLabel hk z i) := by
      rw [←hj]
      exact witnessBalance_ordered_position_fiber (k:=k) (b:=b) (delta:=delta) hk z hd i
    have hs := hx w hw (witnessBalanceLabel hk z i)
    simpa [witnessBalanceOrderedSum,he,witnessBalanceOutputSum,witnessBalanceRowSum,
      Finset.sum_add_distrib,←Finset.mul_sum] using hs
  · have he : witnessBalanceOrderedPositions (k:=k) (b:=b) (delta:=delta) hk z j=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [witnessBalanceOrderedSum,he]

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_retained_relabel
#print axioms HSTZ.witnessBalance_retained_projection_relabel
#print axioms HSTZ.witnessBalance_pair_order
#print axioms HSTZ.witnessBalance_ordered_position_fiber
#print axioms HSTZ.witnessBalance_ordered_sums
