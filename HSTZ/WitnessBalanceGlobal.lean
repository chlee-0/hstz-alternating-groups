import HSTZ.WitnessBalanceSelector

/-! The global balance filter, its invariance under the full group, and the
projection. Adapts `BalanceProjection` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0),
keeping the original source, components and pair letters. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))

/-- Full-group balance filter on output counts and sums; the original positions
and statistics are internal constants, not hypotheses. -/
def witnessBalanceGlobalWords (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) : Prop :=
  (∀ i, witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk (w i)) ∧ ∀ j,
    (Finset.univ.filter (fun i =>
      witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w i)=j)).card =
      (witnessBalanceOrderedPositions (k:=k) (b:=b) (delta:=delta) hk z j).card ∧
    (∑ i ∈ Finset.univ.filter (fun i =>
      witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w i)=j),
      (balancePairOutput (w i) : ℤ)) =
        witnessBalanceOrderedSum (k:=k) (b:=b) (delta:=delta) hk z j

/-- Permutation invariance, adapted from OpenAI's `BalanceProjection`;
cardinalities use `sum_boole` and sums use `Equiv.sum_comp`. -/
theorem witnessBalanceGlobalWords_invariant (g : Equiv.Perm (Fin n))
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalanceGlobalWords (k:=k) (b:=b) (delta:=delta) hk z (w ∘ g) ↔ witnessBalanceGlobalWords (k:=k) (b:=b) (delta:=delta) hk z w := by
  classical
  have hc (j) :
      (Finset.univ.filter (fun i => witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w (g i))=j)).card =
      (Finset.univ.filter (fun i => witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w i)=j)).card := by
    simpa only [Finset.sum_boole,Nat.cast_id] using
      Equiv.sum_comp g (fun i => if witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w i)=j then (1:ℕ) else 0)
  have hs (j) :
      (∑ i ∈ Finset.univ.filter (fun i => witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w (g i))=j),
        (balancePairOutput (w (g i)) : ℤ)) =
      (∑ i ∈ Finset.univ.filter (fun i => witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w i)=j),
        (balancePairOutput (w i) : ℤ)) := by
    simpa only [Finset.sum_filter] using
      Equiv.sum_comp g (fun i => if witnessBalancePairOrderedLabel (k:=k) (b:=b) (delta:=delta) hk (w i)=j
        then (balancePairOutput (w i) : ℤ) else 0)
  unfold witnessBalanceGlobalWords
  simp only [Function.comp_apply,hc,hs]
  constructor
  · rintro ⟨h,hcs⟩
    exact ⟨fun i => by simpa using h (g.symm i),hcs⟩
  · rintro ⟨h,hcs⟩
    exact ⟨fun i => h (g i),hcs⟩

def witnessBalanceGlobalProjection :
    Representation.IntertwiningMap (wordRep n (witnessBalancePairDim k b delta hk))
      (wordRep n (witnessBalancePairDim k b delta hk)) where
  toLinearMap := coordinateProjection (witnessBalanceGlobalWords (k:=k) (b:=b) (delta:=delta) hk z)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    classical
    funext w
    change (if witnessBalanceGlobalWords (k:=k) (b:=b) (delta:=delta) hk z w then x (w ∘ g) else 0) =
      (if witnessBalanceGlobalWords (k:=k) (b:=b) (delta:=delta) hk z (w ∘ g) then x (w ∘ g) else 0)
    rw [witnessBalanceGlobalWords_invariant (k:=k) (b:=b) (delta:=delta) hk z g w]

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceGlobalWords_invariant
#print axioms HSTZ.witnessBalanceGlobalProjection
