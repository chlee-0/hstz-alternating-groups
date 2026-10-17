import HSTZ.WitnessBalancePackingBlocks

/-! Finite ordered packing blocks and physical position fibers.
Builds on APIs from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). The first joint block
coarsens two labels geometrically; H still preserves each label. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical

private theorem early_mem_aux (k delta h : ℕ) :
    ∀ s, k-2*s=h → ∀ q : WitnessBalancePackingKind,
      q∈witnessBalanceEarlyPackingBlocks k delta s ↔
        ∃ t, q=.early t ∧ s≤t ∧ 3+delta≤k-2*t := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro s hh q
    by_cases hlt : h<3+delta
    · rw [witnessBalanceEarlyPackingBlocks,hh,if_pos hlt]
      constructor
      · simp
      · rintro ⟨t,_,hst,ht⟩
        omega
    · by_cases heq : h=3+delta
      · rw [witnessBalanceEarlyPackingBlocks,hh,if_neg hlt,if_pos heq,List.mem_singleton]
        constructor
        · intro hq; exact ⟨s,hq,le_refl _,by omega⟩
        · rintro ⟨t,hq,hst,ht⟩
          have hs : t=s := by omega
          simpa only [hs] using hq
      · have hn : k-2*(s+1)=h-2 := by omega
        rw [witnessBalanceEarlyPackingBlocks,hh,if_neg hlt,if_neg heq,List.mem_cons,
          ih (h-2) (by omega) (s+1) hn q]
        constructor
        · rintro (hq | ⟨t,hq,hst,ht⟩)
          · exact ⟨s,hq,le_refl _,by omega⟩
          · exact ⟨t,hq,by omega,ht⟩
        · rintro ⟨t,hq,hst,ht⟩
          by_cases hs : t=s
          · exact Or.inl (by simpa only [hs] using hq)
          · exact Or.inr ⟨t,hq,by omega,ht⟩

theorem witnessBalance_early_blocks_mem (k delta s : ℕ) (q : WitnessBalancePackingKind) :
    q∈witnessBalanceEarlyPackingBlocks k delta s ↔
      ∃ t, q=.early t ∧ s≤t ∧ 3+delta≤k-2*t :=
  early_mem_aux k delta (k-2*s) s rfl q

theorem witnessBalance_packing_blocks_mem (k delta : ℕ) (q : WitnessBalancePackingKind) :
    q∈witnessBalancePackingBlocks k delta ↔
      q=.joint ∨ (delta=1 ∧ q=.tail) ∨ ∃ s, q=.early s ∧ 3+delta≤k-2*s := by
  by_cases hd : delta=1 <;>
    simp [witnessBalancePackingBlocks,hd,witnessBalance_early_blocks_mem,or_assoc]

private theorem early_nodup_aux (k delta h : ℕ) :
    ∀ s, k-2*s=h → (witnessBalanceEarlyPackingBlocks k delta s).Nodup := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro s hh
    by_cases hlt : h<3+delta
    · rw [witnessBalanceEarlyPackingBlocks,hh,if_pos hlt]
      exact List.nodup_nil
    · by_cases heq : h=3+delta
      · rw [witnessBalanceEarlyPackingBlocks,hh,if_neg hlt,if_pos heq]
        exact List.nodup_singleton _
      · rw [witnessBalanceEarlyPackingBlocks,hh,if_neg hlt,if_neg heq,List.nodup_cons]
        refine ⟨?_,ih (h-2) (by omega) (s+1) (by omega)⟩
        intro hm
        obtain ⟨t,ht,hst,_⟩ := (witnessBalance_early_blocks_mem k delta (s+1) (.early s)).mp hm
        have he : s=t := WitnessBalancePackingKind.early.inj ht
        omega

theorem witnessBalance_packing_early_nodup (k delta s : ℕ) :
    (witnessBalanceEarlyPackingBlocks k delta s).Nodup :=
  early_nodup_aux k delta (k-2*s) s rfl

theorem witnessBalance_packing_blocks_nodup (k delta : ℕ) :
    (witnessBalancePackingBlocks k delta).Nodup := by
  by_cases hd : delta=1 <;>
    simp [witnessBalancePackingBlocks,hd,witnessBalance_packing_early_nodup,
      witnessBalance_early_blocks_mem]

def witnessBalancePackingColumnKind (k b delta c : ℕ) : WitnessBalancePackingKind :=
  if c<k-(2+delta) then .early (c/2)
  else if k-1+b≤c ∧ delta=1 then .tail else .joint

theorem witnessBalance_packing_column_mem (k b delta c : ℕ) (hk : 5 ≤ k) (hd : delta≤1) :
    witnessBalancePackingColumnKind k b delta c∈witnessBalancePackingBlocks k delta := by
  rw [witnessBalance_packing_blocks_mem]
  unfold witnessBalancePackingColumnKind
  split_ifs with hc ht
  · exact Or.inr (Or.inr ⟨c/2,rfl,by omega⟩)
  · exact Or.inr (Or.inl ⟨ht.2,rfl⟩)
  · exact Or.inl rfl

/-- The geometric block is exactly the union of its labels; H actions are not
merged. -/
theorem witnessBalance_packing_column_iff (k b delta c : ℕ) (hk : 5 ≤ k) (hd : delta≤1)
    (q : WitnessBalancePackingKind) (hq : q∈witnessBalancePackingBlocks k delta) :
    witnessBalanceColumnLabel k b delta c∈witnessBalancePackingLabels delta q ↔
      witnessBalancePackingColumnKind k b delta c=q := by
  have hm := (witnessBalance_packing_blocks_mem k delta q).mp hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl <;> cases q
  all_goals simp only [witnessBalanceColumnLabel,witnessBalancePackingLabels,
    witnessBalancePackingColumnKind,List.mem_cons,List.mem_singleton,
    WitnessBalancePackingKind.early.injEq] at *
  all_goals split_ifs at * <;> simp_all <;> omega

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- The physical cell column, before any `Fin` enumeration of blocks. -/
def witnessBalancePackingPositionKind (i : Fin n) : WitnessBalancePackingKind :=
  witnessBalancePackingColumnKind k b delta (z i).val.2

theorem witnessBalance_packing_position_mem (hd : delta≤1) (i : Fin n) :
    witnessBalancePackingPositionKind hk z i∈witnessBalancePackingBlocks k delta :=
  witnessBalance_packing_column_mem k b delta _ hk hd

theorem witnessBalance_packing_position_iff (hd : delta≤1)
    (q : WitnessBalancePackingKind) (hq : q∈witnessBalancePackingBlocks k delta) (i : Fin n) :
    witnessBalanceLabel hk z i∈witnessBalancePackingLabels delta q ↔
      witnessBalancePackingPositionKind hk z i=q :=
  witnessBalance_packing_column_iff k b delta _ hk hd q hq

abbrev witnessBalancePackingIndex (k delta : ℕ) :=
  {q : WitnessBalancePackingKind // q∈witnessBalancePackingBlocks k delta}

instance (k delta : ℕ) : Fintype (witnessBalancePackingIndex k delta) :=
  Fintype.subtype (witnessBalancePackingBlocks k delta).toFinset (by intro q; simp)

/-- Each original position goes to its finite block and its block fiber. -/
def witnessBalancePackingCut (hd : delta≤1) : Fin n ≃
    (Σ q : witnessBalancePackingIndex k delta,
      {i : Fin n // witnessBalancePackingPositionKind hk z i=q.val}) where
  toFun i := ⟨⟨witnessBalancePackingPositionKind hk z i,witnessBalance_packing_position_mem hk z hd i⟩,⟨i,rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨q,hq⟩,⟨i,hi⟩⟩
    dsimp at hi
    subst q
    rfl

theorem witnessBalancePackingCut_position (hd : delta≤1) (i : Fin n) :
    (witnessBalancePackingCut hk z hd i).2.val=i := rfl

theorem witnessBalance_packing_H_invariant (hd : delta≤1)
    (g : witnessBalanceGroup hk z) (i : Fin n) :
    witnessBalancePackingPositionKind hk z (g.val i)=witnessBalancePackingPositionKind hk z i := by
  let q := witnessBalancePackingPositionKind hk z i
  have hq := witnessBalance_packing_position_mem hk z hd i
  have hi := (witnessBalance_packing_position_iff hk z hd q hq i).mpr rfl
  rw [← g.property i] at hi
  exact (witnessBalance_packing_position_iff hk z hd q hq (g.val i)).mp hi

/-- Cardinality of the physical fiber of each block, including the joint union. -/
theorem witnessBalance_packing_block_card (hd : delta≤1)
    (q : WitnessBalancePackingKind) (hq : q∈witnessBalancePackingBlocks k delta) :
    witnessBalancePackingDegree hk z q=
      Fintype.card {i : Fin n // witnessBalancePackingPositionKind hk z i=q} := by
  have hc : Fintype.card {i : Fin n // witnessBalancePackingPositionKind hk z i=q}=
      Fintype.card {i : Fin n // witnessBalanceLabel hk z i∈witnessBalancePackingLabels delta q} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i =>
      (witnessBalance_packing_position_iff hk z hd q hq i).symm)
  rw [hc]
  cases q with
  | tail => simp only [witnessBalancePackingDegree,witnessBalancePackingLabels,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,List.mem_singleton,
      witnessBalanceComponentSize]
  | early s => simp only [witnessBalancePackingDegree,witnessBalancePackingLabels,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,List.mem_singleton,
      witnessBalanceComponentSize]
  | joint =>
    let p : ℕ := if delta=0 then 1 else 2
    have hp : p≠0 := by by_cases h0 : delta=0 <;> simp [p,h0]
    simp only [witnessBalancePackingDegree,witnessBalancePackingLabels,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,witnessBalanceComponentSize,
      Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    erw [Fintype.card_subtype]
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    change (if witnessBalanceLabel hk z i=0 then 1 else 0)+
      (if witnessBalanceLabel hk z i=p then 1 else 0)=
      if witnessBalanceLabel hk z i∈[0,p] then 1 else 0
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    split_ifs <;> omega

end
end
end HSTZ
#print axioms HSTZ.witnessBalance_early_blocks_mem
#print axioms HSTZ.witnessBalance_packing_blocks_mem
#print axioms HSTZ.witnessBalancePackingColumnKind
#print axioms HSTZ.witnessBalance_packing_column_mem
#print axioms HSTZ.witnessBalance_packing_column_iff
#print axioms HSTZ.witnessBalancePackingPositionKind
#print axioms HSTZ.witnessBalance_packing_position_mem
#print axioms HSTZ.witnessBalance_packing_position_iff
#print axioms HSTZ.witnessBalancePackingCut
#print axioms HSTZ.witnessBalancePackingCut_position
#print axioms HSTZ.witnessBalance_packing_H_invariant
#print axioms HSTZ.witnessBalance_packing_block_card

#print axioms HSTZ.witnessBalance_packing_early_nodup
#print axioms HSTZ.witnessBalance_packing_blocks_nodup
