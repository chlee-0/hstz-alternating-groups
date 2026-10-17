import HSTZ.WitnessDiagram
import HSTZ.BalanceNeighboringPositions

/-! Witness column components and row sums over all vectors.
Adapts `Balance/BalanceColumns` and the filter-sum identity in `BalanceProjection` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Component labels replace
compatibility and sum hypotheses. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- Tall neighboring column pairs, an optional height-3 piece, twos and ones.
Labels keep the original column order; their packing interpretation is separate. -/
def witnessBalanceColumnLabel (k b delta c : ℕ) : ℕ :=
  if c<k-(2+delta) then 3+c/2
  else if c<k-2 then 2
  else if c<k-1+b then 0 else 1

def witnessBalanceLabel {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) : ℕ :=
  witnessBalanceColumnLabel k b delta (z i).val.2

def witnessBalanceGroup {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) := fiberGroup (witnessBalanceLabel hk z)

theorem witnessBalance_column_mem {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (g : columnGroup z) :
    g.val∈witnessBalanceGroup hk z := by
  intro i
  change witnessBalanceColumnLabel k b delta (z (g.val i)).val.2=
    witnessBalanceColumnLabel k b delta (z i).val.2
  rw [g.property i]

theorem witnessBalance_neighbor_labels (k b delta r : ℕ)
    (hr : 2*r+1<k-(2+delta)) :
    witnessBalanceColumnLabel k b delta (2*r)=3+r ∧
      witnessBalanceColumnLabel k b delta (2*r+1)=3+r := by
  unfold witnessBalanceColumnLabel
  rw [if_pos (by omega),if_pos hr]
  constructor <;> omega

def witnessBalancePositions {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (label : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => witnessBalanceLabel hk z i=label)

def witnessBalanceRowSum {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (label : ℕ) : ℤ :=
  ∑ i ∈ witnessBalancePositions hk z label, ((rowWord z i).val : ℤ)

def witnessBalanceFixedRows {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    Submodule ℂ (WordSpace n ((witnessDiagram k b delta hk).colLen 0)) where
  carrier := {x | ∀ w, x w≠0 → ∀ label,
    (∑ i ∈ witnessBalancePositions hk z label, ((w i).val : ℤ))=
      witnessBalanceRowSum hk z label}
  zero_mem' := by intro w h; exact False.elim (h rfl)
  add_mem' := by
    intro x y hx hy w hw label
    by_cases hh : x w=0
    · exact hy w (by intro hz; apply hw; simp [hh,hz]) label
    · exact hx w hh label
  smul_mem' := by
    intro a x hx w hw label
    exact hx w (by intro hz; apply hw; simp [hz]) label

private theorem witnessBalance_sum_perm {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (g : witnessBalanceGroup hk z)
    (f : Fin n → ℤ) (label : ℕ) :
    ∑ i ∈ witnessBalancePositions hk z label, f (g.val i)=
      ∑ i ∈ witnessBalancePositions hk z label, f i := by
  classical
  have hg : ∀ i, witnessBalanceLabel hk z (g.val i)=witnessBalanceLabel hk z i := g.property
  simpa only [witnessBalancePositions,Finset.sum_filter,hg] using
    Equiv.sum_comp g.val (fun i => if witnessBalanceLabel hk z i=label then f i else 0)

private theorem witnessBalance_fixed_invariant {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (g : witnessBalanceGroup hk z)
    (x : WordSpace n ((witnessDiagram k b delta hk).colLen 0))
    (hx : x∈witnessBalanceFixedRows hk z) :
    wordRep n _ g.val x∈witnessBalanceFixedRows hk z := by
  intro w hw label
  have hh := hx (w ∘ g.val) hw label
  exact (witnessBalance_sum_perm hk z g (fun i => ((w i).val : ℤ)) label).symm.trans hh

theorem witnessBalance_polytabloid_sums {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    polytabloid z∈witnessBalanceFixedRows hk z := by
  classical
  have hbase : (Pi.single (rowWord z) (1:ℂ))∈witnessBalanceFixedRows hk z := by
    intro w hw label
    have he : w=rowWord z := by
      by_contra hn
      exact hw (Pi.single_eq_of_ne hn _)
    subst w
    rfl
  unfold polytabloid
  apply Submodule.sum_mem
  intro g hg
  apply Submodule.smul_mem
  exact witnessBalance_fixed_invariant hk z
    ⟨g.val,witnessBalance_column_mem hk z g⟩ _ hbase

def witnessBalanceLocalRows {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) :=
  cyclic ((wordRep n ((witnessDiagram k b delta hk).colLen 0)).comp
    (witnessBalanceGroup hk z).subtype) (polytabloid z)

theorem witnessBalance_local_mem_specht {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (x : (witnessBalanceLocalRows hk z).toSubmodule) : x.val∈spechtSub z := by
  rcases x with ⟨x,hx⟩
  change x∈Submodule.span ℂ (Set.range fun g : witnessBalanceGroup hk z =>
    wordRep n _ g.val (polytabloid z)) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g,rfl⟩ := hy
    exact (spechtSub z).apply_mem_toSubmodule g.val (mem_cyclic _ _)
  | zero => exact Submodule.zero_mem _
  | add y v hy hv iy iv => exact Submodule.add_mem _ iy iv
  | smul a y hy iy => exact Submodule.smul_mem _ a iy

theorem witnessBalance_local_sums {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (x : (witnessBalanceLocalRows hk z).toSubmodule) :
    x.val∈witnessBalanceFixedRows hk z := by
  rcases x with ⟨x,hx⟩
  change x∈Submodule.span ℂ (Set.range fun g : witnessBalanceGroup hk z =>
    wordRep n _ g.val (polytabloid z)) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g,rfl⟩ := hy
    exact witnessBalance_fixed_invariant hk z g _ (witnessBalance_polytabloid_sums hk z)
  | zero => exact Submodule.zero_mem _
  | add y v hy hv iy iv => exact Submodule.add_mem _ iy iv
  | smul a y hy iy => exact Submodule.smul_mem _ a iy

end
end HSTZ
#print axioms HSTZ.witnessBalance_column_mem
#print axioms HSTZ.witnessBalance_neighbor_labels
#print axioms HSTZ.witnessBalance_polytabloid_sums
#print axioms HSTZ.witnessBalance_local_mem_specht
#print axioms HSTZ.witnessBalance_local_sums
