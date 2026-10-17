import HSTZ.WitnessBalanceTensor

/-! The original height-one tail: every supported pair keeps coordinates
`(0,0)`, not just the scalar `output1`. Follows the `BalanceColumns` component-sum
route from OpenAI's `math` repository (commit adc7f1241, Apache-2.0); no component, Pieri or packing
equality is inferred. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

theorem witnessBalance_tail_label {k b delta c : ℕ} (hk : 5 ≤ k) :
    witnessBalanceColumnLabel k b delta c=1 ↔ k-1+b≤c := by
  have hcut : k-(2+delta)≤k-2 := by omega
  have hlast : k-2<k-1+b := by omega
  unfold witnessBalanceColumnLabel
  split_ifs <;> simp_all <;> omega

theorem witnessBalance_tail_row {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (i : Fin n)
    (hi : witnessBalanceLabel hk z i=1) : (rowWord z i).val=0 := by
  have hc : (k-1)+b≤(z i).val.2 := (witnessBalance_tail_label hk).mp hi
  have hm := YoungDiagram.mem_iff_lt_rowLen.mp (z i).property
  change (z i).val.2<(witnessDiagram k b delta hk).rowLen (z i).val.1 at hm
  rw [witnessDiagram_row_length] at hm
  change (z i).val.1=0
  by_contra h0
  by_cases h1 : (z i).val.1=1
  · simp only [witnessRow,if_neg h0,if_pos h1] at hm
    rw [h1] at hm
    omega
  · have hr : 2≤(z i).val.1 := by omega
    have hs : k-(z i).val.1≤k-2 := Nat.sub_le_sub_left hr k
    simp only [witnessRow,if_neg h0,if_neg h1,add_zero] at hm
    omega

theorem witnessBalance_tail_row_sum {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) : witnessBalanceRowSum hk z 1=0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hh : witnessBalanceLabel hk z i=1 := (Finset.mem_filter.mp hi).2
  rw [witnessBalance_tail_row hk z i hh]
  rfl

theorem witnessBalance_tail_output_sum {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    witnessBalanceOutputSum hk z 1=(witnessBalancePositions hk z 1).card := by
  unfold witnessBalanceOutputSum
  rw [witnessBalance_tail_row_sum, mul_zero,zero_add]

/-- Every supported coordinate of every component-carrier vector. -/
theorem witnessBalance_local_tail_zero {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (x : (witnessBalanceLocalRows hk z).toSubmodule)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0)) (hw : x.val w≠0)
    (i : Fin n) (hi : witnessBalanceLabel hk z i=1) : (w i).val=0 := by
  classical
  have hs := witnessBalance_local_sums hk z x w hw 1
  rw [witnessBalance_tail_row_sum] at hs
  have hall : ∀ j∈witnessBalancePositions hk z 1, (0:ℤ)≤((w j).val:ℤ) := by
    intro j hj
    positivity
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hall).mp hs i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  exact_mod_cast hz

/-- Both decoded letters are kept. This is stronger than `output1` and does
not collapse to a scalar letter or assume a label support condition. -/
theorem witnessBalanceTensorMap_tail_pair {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (v : (witnessBalanceLocalRows hk z).toSubmodule ⊗[ℂ]
      (witnessBalanceLocalRows hk z).toSubmodule)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0))
    (hw : witnessBalanceTensorMap hk z v w≠0) (i : Fin n)
    (hi : witnessBalanceLabel hk z i=1) :
    ((splitLeft (d := (witnessDiagram k b delta hk).colLen 0)
      (e := (witnessDiagram k b delta hk).colLen 0) w i).val=0) ∧
    ((splitRight (d := (witnessDiagram k b delta hk).colLen 0)
      (e := (witnessDiagram k b delta hk).colLen 0) w i).val=0) := by
  classical
  have hs := witnessBalanceTensorMap_output_sums hk z v w hw 1
  rw [witnessBalance_tail_output_sum] at hs
  have hall : ∀ j∈witnessBalancePositions hk z 1,
      (0:ℤ)≤(balancePairOutput (w j):ℤ)-1 := by
    intro j hj
    unfold balancePairOutput
    omega
  have hsum : (∑ j∈witnessBalancePositions hk z 1,
      ((balancePairOutput (w j):ℤ)-1))=0 := by
    rw [Finset.sum_sub_distrib,hs]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hall).mp hsum i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  simp only [balancePairOutput,Nat.cast_add,Nat.cast_one] at hz
  change ((finProdFinEquiv.symm (w i)).1.val=0) ∧
    ((finProdFinEquiv.symm (w i)).2.val=0)
  omega

theorem witnessBalanceTensorMap_tail_output {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (v : (witnessBalanceLocalRows hk z).toSubmodule ⊗[ℂ]
      (witnessBalanceLocalRows hk z).toSubmodule)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0))
    (hw : witnessBalanceTensorMap hk z v w≠0) (i : Fin n)
    (hi : witnessBalanceLabel hk z i=1) : balancePairOutput (w i)=1 := by
  obtain ⟨hl,hr⟩ := witnessBalanceTensorMap_tail_pair hk z v w hw i hi
  change (splitLeft (d := (witnessDiagram k b delta hk).colLen 0)
    (e := (witnessDiagram k b delta hk).colLen 0) w i).val+
    (splitRight (d := (witnessDiagram k b delta hk).colLen 0)
    (e := (witnessDiagram k b delta hk).colLen 0) w i).val+1=1
  rw [hl,hr]

end
end HSTZ
#print axioms HSTZ.witnessBalance_tail_label
#print axioms HSTZ.witnessBalance_tail_row_sum
#print axioms HSTZ.witnessBalance_local_tail_zero
#print axioms HSTZ.witnessBalanceTensorMap_tail_pair
#print axioms HSTZ.witnessBalanceTensorMap_tail_output
