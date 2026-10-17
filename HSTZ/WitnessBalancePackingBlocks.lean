import HSTZ.WitnessBalancePieriTableaux
import HSTZ.BalancePacking

/-! The original unsorted packing as concrete ordered blocks of original labels.
Uses interfaces and geometry adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Joint blocks are unions of two labels, not full permutation groups replacing `H`. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

inductive WitnessBalancePackingKind where
  | joint
  | tail
  | early (s : ℕ)
  deriving DecidableEq

def witnessBalancePackingLabels (delta : ℕ) : WitnessBalancePackingKind → List ℕ
  | .joint => [0,if delta=0 then 1 else 2]
  | .tail => [1]
  | .early s => [3+s]

/-- Original-column progression, with increasing label indices and decreasing heights. -/
def witnessBalanceEarlyPackingBlocks (k delta s : ℕ) : List WitnessBalancePackingKind :=
  if k-2*s<3+delta then [] else if k-2*s=3+delta then [.early s]
  else .early s :: witnessBalanceEarlyPackingBlocks k delta (s+1)
termination_by k-2*s
decreasing_by omega

def witnessBalancePackingBlocks (k delta : ℕ) : List WitnessBalancePackingKind :=
  [.joint] ++ (if delta=1 then [.tail] else []) ++ witnessBalanceEarlyPackingBlocks k delta 0

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- Sum of the component cardinalities, keeping both joint labels. -/
def witnessBalancePackingDegree (q : WitnessBalancePackingKind) : ℕ :=
  ((witnessBalancePackingLabels delta q).map (witnessBalanceComponentSize hk z)).sum

def witnessBalancePackingParts (q : WitnessBalancePackingKind) : List ℕ :=
  match q with
  | .joint => balancedPack 2 (witnessBalancePackingDegree hk z q)
  | .tail => [witnessBalancePackingDegree hk z q]
  | .early s => if k-2*s=3+delta then [witnessBalancePackingDegree hk z q]
    else balancedPack 4 (witnessBalancePackingDegree hk z q)

theorem witnessBalance_packing_tail_degree :
    witnessBalancePackingDegree hk z .tail=1+delta := by
  simp only [witnessBalancePackingDegree,witnessBalancePackingLabels,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  exact witnessBalance_tail_positions_card hk z

theorem witnessBalance_packing_joint_degree (hd : delta≤1) :
    witnessBalancePackingDegree hk z .joint=2*b+3+2*delta := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl
  · change witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1=2*b+3+2*0
    rw [witnessBalance_twos_positions_card,witnessAttachment_card,
      witnessBalance_tail_positions_card]
    omega
  · change witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2=2*b+3+2*1
    rw [witnessBalance_twos_positions_card,witnessAttachment_card,
      witnessBalance_three_positions_card]
    omega

theorem witnessBalance_packing_early_guard (s : ℕ) (hd : delta≤1)
    (he : 3+delta≤k-2*s) :
    (k-2*s=3+delta → k-(2+delta)=2*s+1) ∧
    (k-2*s≠3+delta → 2*s+1<k-(2+delta)) := by omega

theorem witnessBalance_packing_early_parts (s : ℕ) (hd : delta≤1)
    (he : 3+delta≤k-2*s) :
    witnessBalancePackingParts hk z (.early s)=
      if k-2*s=3+delta then [k-2*s] else balancedPack 4 (2*(k-2*s)-1) := by
  by_cases hs : k-2*s=3+delta
  · have hc : k-(2+delta)=2*s+1 := by omega
    simp only [witnessBalancePackingParts,if_pos hs]
    change [witnessBalanceComponentSize hk z (3+s)]=[k-2*s]
    rw [witnessBalance_unmatched_positions_card hk z s hd hc]
  · have hc : 2*s+1<k-(2+delta) := by omega
    simp only [witnessBalancePackingParts,if_neg hs]
    change balancedPack 4 (witnessBalanceComponentSize hk z (3+s))=
      balancedPack 4 (2*(k-2*s)-1)
    rw [witnessBalance_neighbor_positions_card hk z s hc]
    congr 1
    unfold witnessBalanceNeighborSize
    omega

private theorem early_parts_eq_aux (hd : delta≤1) (h : ℕ) :
    ∀ s, k-2*s=h →
      (witnessBalanceEarlyPackingBlocks k delta s).flatMap (witnessBalancePackingParts hk z)=
        staircasePairs (3+delta) h := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro s hh
    by_cases hlt : h<3+delta
    · rw [witnessBalanceEarlyPackingBlocks,hh,if_pos hlt,staircasePairs,if_pos hlt]
      rfl
    · by_cases heq : h=3+delta
      · rw [witnessBalanceEarlyPackingBlocks,hh,if_neg hlt,if_pos heq,
          List.flatMap_cons,List.flatMap_nil,List.append_nil,
          witnessBalance_packing_early_parts hk z s hd (by omega),hh,if_pos heq]
        conv_rhs => rw [staircasePairs,if_neg hlt,if_pos heq]
        exact congrArg (fun v => [v]) heq
      · have hn : k-2*(s+1)=h-2 := by omega
        have hi := ih (h-2) (by omega) (s+1) hn
        rw [witnessBalanceEarlyPackingBlocks,hh,if_neg hlt,if_neg heq,
          List.flatMap_cons,witnessBalance_packing_early_parts hk z s hd (by omega),hh,if_neg heq,hi]
        conv_rhs => rw [staircasePairs,if_neg hlt,if_neg heq]

theorem witnessBalance_packing_early_flatten (hd : delta≤1) :
    (witnessBalanceEarlyPackingBlocks k delta 0).flatMap (witnessBalancePackingParts hk z)=
      staircasePairs (3+delta) k :=
  early_parts_eq_aux hk z hd k 0 (by simp)

/-- The literal original unsorted list; no sorting is involved. -/
theorem witnessBalance_packing_blocks_flatten (hd : delta≤1) :
    (witnessBalancePackingBlocks k delta).flatMap (witnessBalancePackingParts hk z)=
      balancePacking k b delta := by
  rw [witnessBalancePackingBlocks,List.flatMap_append,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,
    witnessBalance_packing_early_flatten hk z hd]
  simp only [witnessBalancePackingParts,witnessBalance_packing_joint_degree hk z hd]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl
  · simp [balancePacking]
  · simp [balancePacking,witnessBalancePackingParts,witnessBalance_packing_tail_degree hk z]

end
end
end HSTZ
#print axioms HSTZ.WitnessBalancePackingKind
#print axioms HSTZ.witnessBalanceEarlyPackingBlocks
#print axioms HSTZ.witnessBalancePackingBlocks
#print axioms HSTZ.witnessBalancePackingDegree
#print axioms HSTZ.witnessBalance_packing_tail_degree
#print axioms HSTZ.witnessBalance_packing_joint_degree
#print axioms HSTZ.witnessBalance_packing_early_guard
#print axioms HSTZ.witnessBalance_packing_early_parts
#print axioms HSTZ.witnessBalance_packing_early_flatten
#print axioms HSTZ.witnessBalance_packing_blocks_flatten
