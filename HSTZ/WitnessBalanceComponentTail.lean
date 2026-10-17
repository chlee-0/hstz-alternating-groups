import HSTZ.WitnessBalanceComponentCarrier

/-! All columns sharing tail output 1, treated as one component rather than one physical
singleton. Uses the support result for both letters 0 and the two-factor identity for the
original polytabloid. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

theorem witnessBalance_component_word_ne_zero (a : ℕ) :
    witnessBalanceComponentWord hk z a≠0 := by
  intro hz
  apply polytabloid_ne_zero z
  rw [witnessBalance_component_polytabloid hk z a,hz]
  funext w
  simp [positionProduct]

theorem witnessBalance_other_word_ne_zero (a : ℕ) :
    witnessBalanceOtherWord hk z a≠0 := by
  intro hz
  apply polytabloid_ne_zero z
  rw [witnessBalance_component_polytabloid hk z a,hz]
  funext w
  simp [positionProduct]

def witnessBalanceTailZeroWord : Fin (witnessBalanceComponentSize hk z 1) →
    Fin ((witnessDiagram k b delta hk).colLen 0) :=
  fun _ => ⟨0,by rw [witnessDiagram_height]; omega⟩

/-- The same original tail component, with all supported coordinates and an internally
chosen nonzero coordinate of the other factor. -/
theorem witnessBalance_tail_component_word_support
    (w : Fin (witnessBalanceComponentSize hk z 1) → Fin ((witnessDiagram k b delta hk).colLen 0))
    (hw : witnessBalanceComponentWord hk z 1 w≠0) : w=witnessBalanceTailZeroWord hk z := by
  obtain ⟨v,hv⟩ : ∃ v, witnessBalanceOtherWord hk z 1 v≠0 := by
    by_contra hh
    push_neg at hh
    exact witnessBalance_other_word_ne_zero hk z 1 (funext hh)
  let q := joinPositions (witnessBalanceComponentCut hk z 1) w v
  have hq : polytabloid z q≠0 := by
    rw [witnessBalance_component_polytabloid hk z 1]
    change witnessBalanceComponentWord hk z 1 (leftWord _ q)*
      witnessBalanceOtherWord hk z 1 (rightWord _ q)≠0
    simpa only [q,leftWord_join,rightWord_join] using mul_ne_zero hw hv
  funext i
  apply Fin.ext
  have hh := witnessBalance_local_tail_zero hk z ⟨polytabloid z,mem_cyclic _ _⟩ q hq
    ((witnessBalanceComponentCut hk z 1).symm (.inl i))
    (witnessBalanceComponentCut_left hk z 1 i)
  simpa [q,joinPositions,witnessBalanceTailZeroWord] using hh

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_component_word_ne_zero
#print axioms HSTZ.witnessBalance_other_word_ne_zero
#print axioms HSTZ.witnessBalance_tail_component_word_support
