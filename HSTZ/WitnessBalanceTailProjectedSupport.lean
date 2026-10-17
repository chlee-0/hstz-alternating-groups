import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalanceTwosSupport
import HSTZ.WitnessBalanceTailCyclic

/-! The whole tail component (label 1) in its projected factor of the square. Both
generators are kept, at the component degree. The `oneRowEvaluation` argument is
adapted to this projected codomain. Uses declarations from OpenAI's `math` repository
(commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

def witnessBalanceTailCarrierGenerator : (witnessBalanceComponentRows hk z 1).toSubmodule :=
  ⟨witnessBalanceComponentWord hk z 1,generator_mem_cyclicSpan _ _⟩

def witnessBalanceTailPairWord :=
  mergeWords (witnessBalanceTailZeroWord hk z) (witnessBalanceTailZeroWord hk z)

theorem witnessBalance_tail_pair_allowed :
    witnessBalanceLocalPairWords hk z 1 (witnessBalanceTailPairWord hk z) := by
  constructor <;> intro i
  · change balancePairOutput (witnessBalanceTailPairWord hk z i)≤k
    simp only [witnessBalanceTailPairWord,mergeWords,balancePairOutput,
      Equiv.symm_apply_apply,witnessBalanceTailZeroWord]
    omega
  · change witnessBalanceOutputLabel k delta
      (balancePairOutput (witnessBalanceTailPairWord hk z i))=1
    simp [witnessBalanceTailPairWord,mergeWords,balancePairOutput,witnessBalanceTailZeroWord,
      witnessBalanceOutputLabel]

def witnessBalanceTailProjectedVector : (witnessBalanceLocalProjectedFactor hk z 1).toSubmodule :=
  ⟨witnessBalanceLocalProjectedMap hk z 1
    (witnessBalanceTailCarrierGenerator hk z ⊗ₜ[ℂ] witnessBalanceTailCarrierGenerator hk z),
    ⟨witnessBalanceTailCarrierGenerator hk z ⊗ₜ[ℂ] witnessBalanceTailCarrierGenerator hk z,rfl⟩⟩

theorem witnessBalanceTailProjectedVector_fixed
    (g : Equiv.Perm (Fin (witnessBalanceComponentSize hk z 1))) :
    (witnessBalanceLocalProjectedFactor hk z 1).toRepresentation g
      (witnessBalanceTailProjectedVector hk z)=witnessBalanceTailProjectedVector hk z := by
  apply Subtype.ext
  change wordRep _ _ g (witnessBalanceLocalProjectedMap hk z 1
    (witnessBalanceTailCarrierGenerator hk z ⊗ₜ[ℂ] witnessBalanceTailCarrierGenerator hk z))=_
  have he := (witnessBalanceLocalProjectedMap hk z 1).map_action g
    (witnessBalanceTailCarrierGenerator hk z ⊗ₜ[ℂ] witnessBalanceTailCarrierGenerator hk z)
  have hq : ((witnessBalanceComponentRows hk z 1).toRepresentation.tprod
      (witnessBalanceComponentRows hk z 1).toRepresentation) g
      (witnessBalanceTailCarrierGenerator hk z ⊗ₜ[ℂ] witnessBalanceTailCarrierGenerator hk z)=
      witnessBalanceTailCarrierGenerator hk z ⊗ₜ[ℂ] witnessBalanceTailCarrierGenerator hk z := by
    simp only [Representation.tprod_apply,TensorProduct.map_tmul,
      witnessBalance_tail_cyclic_fixed hk z g]
  rw [hq] at he
  exact he.symm

theorem witnessBalanceTailProjectedVector_ne_zero : witnessBalanceTailProjectedVector hk z≠0 := by
  have hc : witnessBalanceComponentWord hk z 1 (witnessBalanceTailZeroWord hk z)≠0 := by
    intro hc
    have he := witnessBalance_tail_generator_single hk z
    rw [hc,zero_smul] at he
    exact witnessBalance_component_word_ne_zero hk z 1 he
  intro hy
  have he := congrArg (fun x : (witnessBalanceLocalProjectedFactor hk z 1).toSubmodule =>
    x.val (witnessBalanceTailPairWord hk z)) hy
  change coordinateProjection (witnessBalanceLocalPairWords hk z 1)
    (wordTensor _ _ _ (witnessBalanceComponentWord hk z 1 ⊗ₜ[ℂ]
      witnessBalanceComponentWord hk z 1)) (witnessBalanceTailPairWord hk z)=0 at he
  change (if witnessBalanceLocalPairWords hk z 1 (witnessBalanceTailPairWord hk z) then
    wordTensor _ _ _ (witnessBalanceComponentWord hk z 1 ⊗ₜ[ℂ]
      witnessBalanceComponentWord hk z 1) (witnessBalanceTailPairWord hk z) else 0)=0 at he
  rw [if_pos (witnessBalance_tail_pair_allowed hk z),wordTensor_tmul] at he
  simp only [witnessBalanceTailPairWord,splitLeft_merge,splitRight_merge] at he
  exact (mul_ne_zero hc hc) he

/-- Projected one-row support for the whole tail, at the component degree. All
physical tail columns and both square factors are kept. -/
theorem witnessBalanceTail_projected_support :
    ∃ J : Representation.IntertwiningMap
      (spechtRep (oneRowTableau (witnessBalanceComponentSize hk z 1)))
      (witnessBalanceLocalProjectedFactor hk z 1).toRepresentation, Function.Injective J := by
  let m := witnessBalanceComponentSize hk z 1
  let u := oneRowTableau m
  let y := witnessBalanceTailProjectedVector hk z
  let J : Representation.IntertwiningMap (spechtRep u)
      (witnessBalanceLocalProjectedFactor hk z 1).toRepresentation :=
    { toLinearMap :=
        { toFun := fun x => oneRowEvaluation u x • y
          map_add' := by intro x v; simp only [map_add,add_smul]
          map_smul' := by intro c x; simp only [map_smul,smul_smul]; rfl }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        change oneRowEvaluation u (spechtRep u g x) • y =
          (witnessBalanceLocalProjectedFactor hk z 1).toRepresentation g (oneRowEvaluation u x • y)
        rw [oneRow_specht_fixed u (oneRowDiagram_rows m),map_smul,
          witnessBalanceTailProjectedVector_fixed hk z g] }
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
#print axioms HSTZ.witnessBalance_tail_pair_allowed
#print axioms HSTZ.witnessBalanceTailProjectedVector_fixed
#print axioms HSTZ.witnessBalanceTailProjectedVector_ne_zero
#print axioms HSTZ.witnessBalanceTail_projected_support
