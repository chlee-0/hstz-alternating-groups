import HSTZ.WitnessBalanceTailSupport

/-! Explicit relabelling of the physical column components of the witness by
their output bands, as needed for the ordered transfer in the balance argument.
The balance packing is not sorted, and letters, positions and carriers are not
replaced. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def witnessBalanceOrderedColumnLabel (k b delta c : ℕ) : ℕ :=
  if c < k-(2+delta) then k-2*(c/2)
  else if c < k-2 then 3
  else if c < k-1+b then 2 else 1

/-- Literal fiber equality, including absent components and arbitrary columns.
The small delta bound is essential to distinguish the optional height-3 piece. -/
theorem witnessBalance_ordered_column_fibers (k b delta c c' : ℕ)
    (hk : 5 ≤ k) (hd : delta ≤ 1) :
    witnessBalanceOrderedColumnLabel k b delta c =
      witnessBalanceOrderedColumnLabel k b delta c' ↔
    witnessBalanceColumnLabel k b delta c = witnessBalanceColumnLabel k b delta c' := by
  have hcut : k-(2+delta)+(2+delta)=k := by omega
  have htwo : k-2+2=k := by omega
  have hone : k-1+1=k := by omega
  unfold witnessBalanceOrderedColumnLabel witnessBalanceColumnLabel
  split_ifs <;> (try simp only [Nat.reduceEqDiff]) <;> omega

def witnessBalanceOrderedLabel {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) : ℕ :=
  witnessBalanceOrderedColumnLabel k b delta (z i).val.2

theorem witnessBalance_ordered_group {k b delta n : ℕ} (hk : 5 ≤ k) (hd : delta ≤ 1)
    (z : Tableau n (witnessDiagram k b delta hk)) :
    fiberGroup (witnessBalanceOrderedLabel hk z) = witnessBalanceGroup hk z := by
  ext g
  constructor <;> intro h i
  · exact (witnessBalance_ordered_column_fibers k b delta _ _ hk hd).mp (h i)
  · exact (witnessBalance_ordered_column_fibers k b delta _ _ hk hd).mpr (h i)

theorem witnessBalance_ordered_neighbor (k b delta r : ℕ)
    (hr : 2*r+1 < k-(2+delta)) :
    witnessBalanceOrderedColumnLabel k b delta (2*r) = k-2*r ∧
      witnessBalanceOrderedColumnLabel k b delta (2*r+1) = k-2*r := by
  unfold witnessBalanceOrderedColumnLabel
  rw [if_pos (by omega),if_pos hr]
  constructor <;> omega

theorem witnessBalance_ordered_low (k b delta c : ℕ) :
    (k-2 ≤ c ∧ c < k-1+b → witnessBalanceOrderedColumnLabel k b delta c = 2) ∧
    (k-1+b ≤ c → witnessBalanceOrderedColumnLabel k b delta c = 1) := by
  unfold witnessBalanceOrderedColumnLabel
  constructor <;> intro h <;> split_ifs <;> omega

/-- Label the output bands, keeping the encoded pair alphabet intact. -/
def witnessBalanceOutputLabel (k delta x : ℕ) : ℕ :=
  if x = 1 then 1 else if x = 2 then 0
  else if x = 3 ∧ delta = 1 then 2 else 3+(k-x)/2

def witnessBalanceOrderedOutputLabel (k delta x : ℕ) : ℕ :=
  if x ≤ 2 then x else if x = 3 ∧ delta = 1 then 3 else k-2*((k-x)/2)

/-- A concrete original column representing the output band. -/
def witnessBalanceOutputColumn (k b x : ℕ) : ℕ :=
  if x = 1 then k-1+b else if x = 2 then k-2 else k-x

theorem witnessBalance_output_column (k b delta x : ℕ)
    (hk : 5 ≤ k) (hd : delta ≤ 1) (hx : 1 ≤ x) (hxk : x ≤ k) :
    witnessBalanceColumnLabel k b delta (witnessBalanceOutputColumn k b x) =
      witnessBalanceOutputLabel k delta x ∧
    witnessBalanceOrderedColumnLabel k b delta (witnessBalanceOutputColumn k b x) =
      witnessBalanceOrderedOutputLabel k delta x := by
  by_cases h1 : x=1
  · subst x
    have ht : k-(2+delta) ≤ k-1+b := by omega
    have h3 : k-2 ≤ k-1+b := by omega
    simp [witnessBalanceOutputColumn,witnessBalanceColumnLabel,
      witnessBalanceOrderedColumnLabel,witnessBalanceOutputLabel,
      witnessBalanceOrderedOutputLabel,not_lt.mpr ht,not_lt.mpr h3]
  by_cases h2 : x=2
  · subst x
    have ht : k-(2+delta) ≤ k-2 := by omega
    have h3 : k-2 < k-1+b := by omega
    simp [witnessBalanceOutputColumn,witnessBalanceColumnLabel,
      witnessBalanceOrderedColumnLabel,witnessBalanceOutputLabel,
      witnessBalanceOrderedOutputLabel,not_lt.mpr ht,h3]
  have hx3 : 3 ≤ x := by omega
  by_cases h3 : x=3 ∧ delta=1
  · obtain ⟨rfl,rfl⟩ := h3
    have hc : k-3 < k-2 := by omega
    simp [witnessBalanceOutputColumn,witnessBalanceColumnLabel,
      witnessBalanceOrderedColumnLabel,witnessBalanceOutputLabel,
      witnessBalanceOrderedOutputLabel,hc]
  · have hc : k-x < k-(2+delta) := by omega
    simp [witnessBalanceOutputColumn,witnessBalanceColumnLabel,
      witnessBalanceOrderedColumnLabel,witnessBalanceOutputLabel,
      witnessBalanceOrderedOutputLabel,h1,h2,h3,hc,show ¬x≤2 by omega]

theorem witnessBalance_output_component_iff (k b delta c x : ℕ)
    (hk : 5 ≤ k) (hd : delta ≤ 1) (hx : 1 ≤ x) (hxk : x ≤ k) :
    witnessBalanceOrderedOutputLabel k delta x = witnessBalanceOrderedColumnLabel k b delta c ↔
      witnessBalanceOutputLabel k delta x = witnessBalanceColumnLabel k b delta c := by
  obtain ⟨ho,hn⟩ := witnessBalance_output_column k b delta x hk hd hx hxk
  rw [←ho,←hn]
  exact witnessBalance_ordered_column_fibers k b delta _ c hk hd

/-- The ordered keys satisfy the strict order needed by balance transfer.
This supplies order only, not the target-specific projected-range map. -/
theorem witnessBalance_output_order (k delta x y : ℕ)
    (hk : 5 ≤ k) (hd : delta ≤ 1) (hx : 1 ≤ x) (hxk : x ≤ k)
    (hy : 1 ≤ y) (hyk : y ≤ k)
    (ho : witnessBalanceOrderedOutputLabel k delta x <
      witnessBalanceOrderedOutputLabel k delta y) : x < y := by
  unfold witnessBalanceOrderedOutputLabel at ho
  split_ifs at ho <;> omega

end
end HSTZ
#print axioms HSTZ.witnessBalance_ordered_column_fibers
#print axioms HSTZ.witnessBalance_ordered_group
#print axioms HSTZ.witnessBalance_ordered_neighbor
#print axioms HSTZ.witnessBalance_ordered_low
#print axioms HSTZ.witnessBalance_output_order
#print axioms HSTZ.witnessBalance_output_column
#print axioms HSTZ.witnessBalance_output_component_iff
