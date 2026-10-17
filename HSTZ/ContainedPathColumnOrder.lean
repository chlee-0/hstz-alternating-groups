import HSTZ.ContainedFactorLetters

/-! Compares the prefix/tail path order with the chosen column enumeration.
Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped BigOperators

private theorem enumerate_index (rs : List ℕ) (x : Columns.Cells rs) :
    ((Columns.enumerate rs).symm x).val=
      (rs.take (Columns.col x)).sum+Columns.row x := by
  induction rs with
  | nil => exact isEmptyElim x
  | cons r rs ih =>
    cases x with
    | inl x =>
      change x.val=(List.take 0 (r::rs)).sum+x.val
      simp
    | inr x =>
      change r+((Columns.enumerate rs).symm x).val=
        ((r::rs).take (Columns.col x+1)).sum+Columns.row x
      rw [ih]
      simp [List.take_succ_cons,Nat.add_assoc]

private theorem column_prefix (mu : YoungDiagram) (c : ℕ) (hc : c ≤ mu.rowLen 0) :
    (mu.transpose.rowLens.take c).sum=prefixSum mu.colLen c := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hl : c < mu.transpose.rowLens.length := by simpa using hc
    rw [List.sum_take_succ _ c hl,YoungDiagram.get_rowLens,
      YoungDiagram.rowLen_transpose,ih (by omega),prefix_succ]

private theorem column_index (mu : YoungDiagram) (x : mu.cells) :
    ((Columns.columnTableau mu).symm x).val=prefixSum mu.colLen x.val.2+x.val.1 := by
  let y := (Columns.toYoung mu).symm x
  have hy : (Columns.row y,Columns.col y)=x.val := by
    change (Columns.toYoung mu y).val=x.val
    rw [Equiv.apply_symm_apply]
  have hc : x.val.2 ≤ mu.rowLen 0 := Nat.le_of_lt
    (YoungDiagram.mem_iff_lt_rowLen.mp (mu.up_left_mem (Nat.zero_le _) le_rfl x.property))
  change ((Columns.enumerate mu.transpose.rowLens).symm y).val=_
  rw [enumerate_index,show Columns.col y=x.val.2 from congrArg Prod.snd hy,
    show Columns.row y=x.val.1 from congrArg Prod.fst hy,column_prefix mu _ hc]

private theorem column_prefix_fromColumns (f : ℕ → ℕ) (hf : Antitone f)
    (m c : ℕ) (hc : c ≤ m) :
    prefixSum (fromColumns f hf m).colLen c=prefixSum f c := by
  apply Finset.sum_congr rfl
  intro j hj
  exact fromColumns_colLen f hf ((Finset.mem_range.mp hj).trans_le hc)

section Order
variable {h e : ℕ → ℕ} (hh : Antitone h) {d K m t : ℕ}
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m)
local notation "T" => containedPathPrefixOrder hh htm hroom hclear hcapacity
local notation "pi" => containedPath h hh d K m

/-- The original column tableau, with the degree congruence derived from the tableaux. -/
def containedPathColumnOrder : Tableau K pi :=
  (finCongr (by simpa only [Fintype.card_fin] using
    Fintype.card_congr ((T).trans (Columns.columnTableau pi).symm))).trans
      (Columns.columnTableau pi)

theorem containedPathColumnOrder_index (x : (pi).cells) :
    ((containedPathColumnOrder hh htm hroom hclear hcapacity).symm x).val=
      prefixSum (greedy h d K) x.val.2+x.val.1 := by
  have hc := ((mem_fromColumns _ _ _ _ _).mp x.property).1
  simp only [containedPathColumnOrder,Equiv.symm_trans_apply,finCongr_symm,
    finCongr_apply,Fin.val_cast]
  rw [column_index,column_prefix_fromColumns _ _ m _ (Nat.le_of_lt hc)]

include hroom hclear in
private theorem reserved_prefix : prefixSum (greedy h d K) t=t*d := by
  unfold prefixSum
  have heq : (∑ j ∈ Finset.range t,greedy h d K j)=∑ j ∈ Finset.range t,d := by
    apply Finset.sum_congr rfl
    intro j hj
    exact greedy_eq_depth hroom (by omega) (Finset.mem_range.mp hj)
  rw [heq]
  simp [Nat.mul_comm]

include hroom hclear in
private theorem shifted_prefix (c : ℕ) :
    prefixSum (greedy h d K) (t+c)=t*d+prefixSum (fun j=>greedy h d K (t+j)) c := by
  rw [prefixSum,Finset.sum_range_add]
  change prefixSum (greedy h d K) t+prefixSum (fun j=>greedy h d K (t+j)) c=_
  rw [reserved_prefix hroom hclear]

 theorem containedPathPrefixOrder_tail (x : (containedPathTail h hh d K m t).cells) :
    ((T).symm (containedTailCell h hh d K m t x)).val=
      t*d+((containedPathTailTableau h hh d K m t).symm x).val := by
  have hx : (containedPathPrefixSplit hh htm hroom hclear).symm
      (containedTailCell h hh d K m t x)=.inr x :=
    (containedPathPrefixSplit hh htm hroom hclear).symm_apply_apply (.inr x)
  simp only [containedPathPrefixOrder,Equiv.symm_trans_apply,Equiv.symm_symm,hx,
    Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inr,finCongr_symm,
    finCongr_apply,Fin.val_cast,finSumFinEquiv_apply_right,Fin.val_natAdd]

 theorem containedPath_orders_equal : T=containedPathColumnOrder hh htm hroom hclear hcapacity := by
  suffices hi : (T).symm=(containedPathColumnOrder hh htm hroom hclear hcapacity).symm by
    simpa using congrArg Equiv.symm hi
  apply Equiv.ext
  intro x
  apply Fin.ext
  obtain ⟨y,rfl⟩ := (containedPathPrefixSplit hh htm hroom hclear).surjective x
  cases y with
  | inl p =>
    change ((T).symm (containedReservedCell hh htm hroom hclear p)).val=
      ((containedPathColumnOrder hh htm hroom hclear hcapacity).symm
        (containedReservedCell hh htm hroom hclear p)).val
    rw [containedPathPrefixOrder_reserved,containedPathColumnOrder_index]
    change p.1.val*d+p.2.val=prefixSum (greedy h d K) p.1.val+p.2.val
    congr 1
    unfold prefixSum
    have heq : (∑ j ∈ Finset.range p.1.val,greedy h d K j)=
        ∑ j ∈ Finset.range p.1.val,d := by
      apply Finset.sum_congr rfl
      intro j hj
      exact greedy_eq_depth hroom (by omega) ((Finset.mem_range.mp hj).trans p.1.isLt)
    rw [heq]
    simp [Nat.mul_comm]
  | inr x =>
    change ((T).symm (containedTailCell h hh d K m t x)).val=
      ((containedPathColumnOrder hh htm hroom hclear hcapacity).symm
        (containedTailCell h hh d K m t x)).val
    rw [containedPathPrefixOrder_tail,containedPathColumnOrder_index]
    simp only [containedPathTailTableau,Equiv.symm_trans_apply,finCongr_symm,
      finCongr_apply,Fin.val_cast]
    rw [column_index]
    have hc := ((mem_fromColumns _ _ _ _ _).mp x.property).1
    unfold containedPathTail
    erw [column_prefix_fromColumns _ _ (m-t) x.val.2 (Nat.le_of_lt hc)]
    change t*d+(prefixSum (fun j=>greedy h d K (t+j)) x.val.2+x.val.1)=
      prefixSum (greedy h d K) (t+x.val.2)+x.val.1
    rw [shifted_prefix hroom hclear]
    omega
end Order
end
end HSTZ
#print axioms HSTZ.containedPathColumnOrder
#print axioms HSTZ.containedPathColumnOrder_index
#print axioms HSTZ.containedPathPrefixOrder_tail
#print axioms HSTZ.containedPath_orders_equal
