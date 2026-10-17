import HSTZ.TensorInterfaces
import HSTZ.WitnessBalanceGlobal

/-! Finite count/sum separation and projection equality, adapted from
`BalanceSeparation` and `BalanceProjection` in OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The private finite kernels are adaptations of that source, not original proofs. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

private lemma balance_equal_sets_of_card_sum_gap {X : Type*} [DecidableEq X]
    (A B : Finset X) (z : X → ℤ) (hc : A.card = B.card)
    (hz : ∑ x ∈ A, z x = ∑ x ∈ B, z x)
    (hgap : ∀ x ∈ A \ B, ∀ y ∈ B \ A, z y < z x) : A = B := by
  classical
  have he := Finset.card_sdiff_comm hc
  let e : ↥(A \ B) ≃ ↥(B \ A) := Finset.equivOfCardEq he
  have hsum : ∑ x ∈ A \ B, z x = ∑ x ∈ B \ A, z x := by
    have h₁ := Finset.sum_sdiff_eq_sub (f := z) (Finset.inter_subset_left (s₁ := A) (s₂ := B))
    have h₂ := Finset.sum_sdiff_eq_sub (f := z) (Finset.inter_subset_right (s₁ := A) (s₂ := B))
    simp only [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] at h₁ h₂
    rw [h₁, h₂, hz]
  have hn : A \ B = ∅ := by
    by_contra hn
    have hs : (Finset.univ : Finset ↥(A \ B)).Nonempty := by
      obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      exact ⟨⟨x,hx⟩,Finset.mem_univ _⟩
    have hh : (∑ x : ↥(A \ B), z (e x)) < ∑ x : ↥(A \ B), z x := by
      apply Finset.sum_lt_sum_of_nonempty hs
      intro x hx
      exact hgap x.val x.property (e x).val (e x).property
    rw [Equiv.sum_comp e (fun y : ↥(B \ A) => z y),
      Finset.sum_coe_sort, Finset.sum_coe_sort, hsum] at hh
    exact lt_irrefl _ hh
  exact Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp hn) hc.ge

private theorem balance_ordered_output_fibers_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (a b : X → ℕ) (z : X → ℤ)
    (ho : ∀ x ∈ s, ∀ y ∈ s, b x < b y → z x < z y)
    (hc : ∀ k, (s.filter (fun x => a x = k)).card =
      (s.filter (fun x => b x = k)).card)
    (hz : ∀ k, ∑ x ∈ s.filter (fun x => a x = k), z x =
      ∑ x ∈ s.filter (fun x => b x = k), z x) :
    ∀ k, s.filter (fun x => a x = k) = s.filter (fun x => b x = k) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply balance_equal_sets_of_card_sum_gap _ _ z (hc k) (hz k)
    intro x hx y hy
    obtain ⟨hxA,hxB⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyB,hyA⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hxs,hxa⟩ := Finset.mem_filter.mp hxA
    obtain ⟨hys,hyb⟩ := Finset.mem_filter.mp hyB
    have hxne : b x ≠ k := by
      intro hh
      exact hxB (Finset.mem_filter.mpr ⟨hxs,hh⟩)
    have hxge : k ≤ b x := by
      by_contra hh
      have hh' : b x < k := Nat.lt_of_not_ge hh
      have hi := ih (b x) hh'
      have hx' : x ∈ s.filter (fun w => a w = b x) := by
        rw [hi]
        exact Finset.mem_filter.mpr ⟨hxs,rfl⟩
      have ha := (Finset.mem_filter.mp hx').2
      omega
    exact ho y hys x hxs (by omega)

private lemma balance_ordered_output_labels_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (a b : X → ℕ) (z : X → ℤ)
    (ho : ∀ x ∈ s, ∀ y ∈ s, b x < b y → z x < z y)
    (hc : ∀ k, (s.filter (fun x => a x = k)).card =
      (s.filter (fun x => b x = k)).card)
    (hz : ∀ k, ∑ x ∈ s.filter (fun x => a x = k), z x =
      ∑ x ∈ s.filter (fun x => b x = k), z x) :
    ∀ x ∈ s, a x = b x := by
  intro x hx
  have he := balance_ordered_output_fibers_eq s a b z ho hc hz (b x)
  have hh : x ∈ s.filter (fun w => a w = b x) := by
    rw [he]
    exact Finset.mem_filter.mpr ⟨hx,rfl⟩
  exact (Finset.mem_filter.mp hh).2

section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

/-- On every supported coordinate of the fixed-output space, global counts and
sums force the component selector. -/
theorem witnessBalance_global_iff_retained (hd : delta ≤ 1)
    (x : WordSpace n (witnessBalancePairDim k b delta hk))
    (hx : x ∈ witnessBalanceFixedOutputs hk z)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) (hw : x w ≠ 0) :
    witnessBalanceGlobalWords (k:=k) (b:=b) (delta:=delta) hk z w ↔
      witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w := by
  classical
  constructor
  · rintro ⟨hA,hcs⟩
    apply (witnessBalance_retained_relabel (k:=k) (b:=b) (delta:=delta) hk z hd w).mp
    refine ⟨hA,fun i => ?_⟩
    exact (balance_ordered_output_labels_eq Finset.univ
      (witnessBalanceOrderedLabel hk z)
      (fun p => witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w p))
      (fun p => (balancePairOutput (w p) : ℤ))
      (fun p hp q hq hh => by
        change (balancePairOutput (w p) : ℤ) < (balancePairOutput (w q) : ℤ)
        exact_mod_cast witnessBalance_pair_order (k:=k) (b:=b) (delta:=delta) hk hd
          (w p) (w q) (hA p) (hA q) hh)
      (fun j => (hcs j).1.symm)
      (fun j => (witnessBalance_ordered_sums (k:=k) (b:=b) (delta:=delta) hk z hd x hx w hw j).trans
        (hcs j).2.symm) i (Finset.mem_univ i)).symm
  · intro h
    obtain ⟨hA,hl⟩ :=
      (witnessBalance_retained_relabel (k:=k) (b:=b) (delta:=delta) hk z hd w).mpr h
    refine ⟨hA,fun j => ?_⟩
    simp only [hl]
    exact ⟨rfl,witnessBalance_ordered_sums (k:=k) (b:=b) (delta:=delta) hk z hd x hx w hw j⟩

/-- Global and component projections agree on the entire space, not just one
repeated generator. The component projection is not claimed to be square-stable. -/
theorem witnessBalance_global_projection_eq (hd : delta ≤ 1)
    (x : WordSpace n (witnessBalancePairDim k b delta hk))
    (hx : x ∈ witnessBalanceFixedOutputs hk z) :
    witnessBalanceGlobalProjection (k:=k) (b:=b) (delta:=delta) hk z x =
      coordinateProjection (witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z) x := by
  classical
  funext w
  change (if witnessBalanceGlobalWords (k:=k) (b:=b) (delta:=delta) hk z w then x w else 0) =
    (if witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z w then x w else 0)
  by_cases hw : x w = 0
  · simp only [hw,ite_self]
  · simp only [witnessBalance_global_iff_retained (k:=k) (b:=b) (delta:=delta) hk z hd x hx w hw]

/-- Version for the whole independent tensor carrier, with no sum or generator
hypothesis. -/
theorem witnessBalance_tensor_global_projection (hd : delta ≤ 1)
    (v : (witnessBalanceLocalRows hk z).toSubmodule ⊗[ℂ]
      (witnessBalanceLocalRows hk z).toSubmodule) :
    witnessBalanceGlobalProjection (k:=k) (b:=b) (delta:=delta) hk z
      (witnessBalanceTensorMap hk z v) =
    coordinateProjection (witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z)
      (witnessBalanceTensorMap hk z v) :=
  witnessBalance_global_projection_eq (k:=k) (b:=b) (delta:=delta) hk z hd _
    (witnessBalanceTensorMap_output_sums hk z v)

/-- Conditional on the target map `f`: the fully equivariant global projection
has exactly `f` as its raw image. -/
theorem witnessBalance_actual_raw_lift (hd : delta ≤ 1) {nu : YoungDiagram}
    (target : Tableau n nu)
    (f : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      (witnessBalanceProjectedRange hk z
        (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
        (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk)).toRepresentation)
    (hf : f ≠ 0) :
    ∃ L : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      ((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype),
      (∀ x, witnessBalanceGlobalProjection (k:=k) (b:=b) (delta:=delta) hk z (L x) = (f x).val) ∧
      (∀ x, L x ∈ witnessBalanceFixedOutputs hk z) ∧
      (∀ x, ∃ q : Specht z ⊗[ℂ] Specht z,
        ((wordTensorIntertwiner n _ _).comp (spechtTensorInclusion z z)) q = L x) ∧
      (coordinateProjection (witnessBalanceRetainedWords (k:=k) (b:=b) (delta:=delta) hk z)).comp L.toLinearMap ≠ 0 := by
  obtain ⟨L,he,hs,hm,hn⟩ := witnessBalance_projected_target_lift (k:=k) (b:=b) (delta:=delta) hk z target
    (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
    (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk) f hf
  refine ⟨L,?_,hs,hm,hn⟩
  intro x
  rw [witnessBalance_global_projection_eq (k:=k) (b:=b) (delta:=delta) hk z hd _ (hs x)]
  exact he x

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_global_iff_retained
#print axioms HSTZ.witnessBalance_global_projection_eq
#print axioms HSTZ.witnessBalance_tensor_global_projection
#print axioms HSTZ.witnessBalance_actual_raw_lift
