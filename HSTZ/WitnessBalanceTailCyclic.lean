import HSTZ.WitnessBalanceComponentTail
import HSTZ.BalanceSingletonSupport

/-! The whole original output-1 component: all physical height-one columns together.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The zero-word support supplies the invariant vector and its nonvanishing;
`oneRowEvaluation` and irreducibility are applied to the whole component. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

theorem witnessBalance_tail_generator_single : witnessBalanceComponentWord hk z 1 =
    witnessBalanceComponentWord hk z 1 (witnessBalanceTailZeroWord hk z) •
      (Pi.single (witnessBalanceTailZeroWord hk z) (1:ℂ) :
        WordSpace (witnessBalanceComponentSize hk z 1) ((witnessDiagram k b delta hk).colLen 0)) := by
  funext w
  by_cases hw : w=witnessBalanceTailZeroWord hk z
  · subst w
    simp only [Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one]
  · have hz : witnessBalanceComponentWord hk z 1 w=0 := by
      by_contra hz
      exact hw (witnessBalance_tail_component_word_support hk z w hz)
    simp only [Pi.smul_apply,Pi.single_eq_of_ne hw,smul_zero,hz]

theorem witnessBalance_tail_generator_fixed
    (g : Equiv.Perm (Fin (witnessBalanceComponentSize hk z 1))) :
    wordRep _ _ g (witnessBalanceComponentWord hk z 1)=witnessBalanceComponentWord hk z 1 := by
  rw [witnessBalance_tail_generator_single hk z,map_smul,wordRep_single]
  rfl

/-- Every vector of the full-component cyclic carrier is fixed. -/
theorem witnessBalance_tail_cyclic_fixed
    (g : Equiv.Perm (Fin (witnessBalanceComponentSize hk z 1)))
    (x : (witnessBalanceComponentRows hk z 1).toSubmodule) :
    (witnessBalanceComponentRows hk z 1).toRepresentation g x=x := by
  apply Subtype.ext
  rcases x with ⟨x,hx⟩
  change x∈Submodule.span ℂ (Set.range fun h : Equiv.Perm (Fin (witnessBalanceComponentSize hk z 1)) =>
    wordRep _ _ h (witnessBalanceComponentWord hk z 1)) at hx
  change wordRep _ _ g x=x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h,rfl⟩ := hy
    change wordRep _ _ g (wordRep _ _ h (witnessBalanceComponentWord hk z 1))=
      wordRep _ _ h (witnessBalanceComponentWord hk z 1)
    rw [witnessBalance_tail_generator_fixed hk z h,witnessBalance_tail_generator_fixed hk z g]
  | zero => exact map_zero _
  | add y u hy hu iy iu => rw [map_add,iy,iu]
  | smul c y hy iy => rw [map_smul,iy]

/-- Nonzero one-row source map into the same whole tail component, in all degrees
including the empty one. -/
theorem witnessBalance_tail_oneRow_embedding :
    ∃ J : Representation.IntertwiningMap
      (spechtRep (oneRowTableau (witnessBalanceComponentSize hk z 1)))
      (witnessBalanceComponentRows hk z 1).toRepresentation, Function.Injective J := by
  let m := witnessBalanceComponentSize hk z 1
  let u := oneRowTableau m
  let y : (witnessBalanceComponentRows hk z 1).toSubmodule :=
    ⟨witnessBalanceComponentWord hk z 1,generator_mem_cyclicSpan _ _⟩
  let J : Representation.IntertwiningMap (spechtRep u)
      (witnessBalanceComponentRows hk z 1).toRepresentation :=
    { toLinearMap :=
        { toFun := fun x => oneRowEvaluation u x • y
          map_add' := by intro x v; simp only [map_add,add_smul]
          map_smul' := by intro c x; simp only [map_smul,smul_smul]; rfl }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        change oneRowEvaluation u (spechtRep u g x) • y =
          (witnessBalanceComponentRows hk z 1).toRepresentation g (oneRowEvaluation u x • y)
        rw [oneRow_specht_fixed u (oneRowDiagram_rows m),map_smul,
          witnessBalance_tail_cyclic_fixed hk z g y] }
  have hn : J≠0 := by
    intro hz
    let p : Specht u := ⟨polytabloid u,mem_cyclic _ _⟩
    have he := congrArg (fun F => F p) hz
    change oneRowEvaluation u p • y=0 at he
    have hp : oneRowEvaluation u p=1 := polytabloid_rowWord u
    rw [hp,one_smul] at he
    exact witnessBalance_component_word_ne_zero hk z 1 (congrArg Subtype.val he)
  letI := specht_irreducible u
  exact ⟨J,(Representation.IsIrreducible.injective_or_eq_zero J).resolve_right hn⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_tail_generator_single
#print axioms HSTZ.witnessBalance_tail_generator_fixed
#print axioms HSTZ.witnessBalance_tail_cyclic_fixed
#print axioms HSTZ.witnessBalance_tail_oneRow_embedding
