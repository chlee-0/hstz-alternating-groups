import HSTZ.TauCetiFinite.Agreement

/-!
Executable enumeration of canonical partitions for the finite character sums.
Soundness and completeness of the enumeration and the sum bijection are proved, so a
generated class list never has to be assumed complete.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

/-- Positive decreasing lists of the required sum, with explicit recursion fuel. -/
def partitionShapes : ℕ → ℕ → ℕ → Finset Shape
  | 0, n, _ => if n = 0 then {[]} else ∅
  | fuel + 1, n, bound =>
    if n = 0 then {[]} else
      (Finset.Icc 1 (min n bound)).biUnion fun a =>
        (partitionShapes fuel (n-a) a).image (List.cons a)

theorem isShape_sum_zero {xs : Shape} (hx : IsShape xs) (hs : xs.sum = 0) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    have ha := hx.2 a (by simp)
    simp only [List.sum_cons] at hs
    omega

theorem isShape_length_le_sum {xs : Shape} (hx : IsShape xs) : xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ht : IsShape xs := ⟨(List.pairwise_cons.mp hx.1).2,
      fun b hb => hx.2 b (List.mem_cons_of_mem a hb)⟩
    have hlen := ih ht
    have ha := hx.2 a (by simp)
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Soundness and completeness of the enumeration, including degree zero and bound zero. -/
theorem mem_partitionShapes (fuel n bound : ℕ) (xs : Shape) :
    xs ∈ partitionShapes fuel n bound ↔
      IsShape xs ∧ xs.sum = n ∧ xs.length ≤ fuel ∧ ∀ a ∈ xs, a ≤ bound := by
  induction fuel generalizing n bound xs with
  | zero =>
    by_cases hn : n = 0
    · subst n
      change xs ∈ ({[]} : Finset Shape) ↔ _
      rw [Finset.mem_singleton]
      constructor
      · rintro rfl; simp [IsShape]
      · intro h; exact isShape_sum_zero h.1 h.2.1
    · simp only [partitionShapes, if_neg hn, Finset.notMem_empty, false_iff]
      intro h
      have he : xs = [] := by simpa using Nat.eq_zero_of_le_zero h.2.2.1
      subst xs
      simp only [List.sum_nil] at h
      exact hn h.2.1.symm
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst n
      change xs ∈ ({[]} : Finset Shape) ↔ _
      rw [Finset.mem_singleton]
      constructor
      · rintro rfl; simp [IsShape]
      · intro h; exact isShape_sum_zero h.1 h.2.1
    · cases xs with
      | nil =>
        simp only [partitionShapes, if_neg hn, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨a, ha, ys, hy, he⟩; cases he
        · intro h; exact False.elim (hn h.2.1.symm)
      | cons a xs =>
        rw [partitionShapes, if_neg hn]
        constructor
        · intro h
          obtain ⟨j, hj, hy⟩ := Finset.mem_biUnion.mp h
          obtain ⟨zs, hz, he⟩ := Finset.mem_image.mp hy
          obtain ⟨hja, hzs⟩ := List.cons.inj he
          subst j
          subst zs
          have ht := (ih (n-a) a xs).mp hz
          have hj' := Finset.mem_Icc.mp hj
          have hjn : a ≤ n := (le_min_iff.mp hj'.2).1
          have hjb : a ≤ bound := (le_min_iff.mp hj'.2).2
          refine ⟨⟨List.pairwise_cons.mpr ⟨ht.2.2.2, ht.1.1⟩, ?_⟩, ?_, ?_, ?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · omega
            · exact ht.1.2 b hb
          · simp only [List.sum_cons]; omega
          · simp only [List.length_cons]; omega
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hjb
            · exact le_trans (ht.2.2.2 b hb) hjb
        · intro h
          have ha : 0 < a := h.1.2 a (by simp)
          have hsum : a + xs.sum = n := h.2.1
          have han : a ≤ n := by omega
          have hab : a ≤ bound := h.2.2.2 a (by simp)
          apply Finset.mem_biUnion.mpr
          refine ⟨a, Finset.mem_Icc.mpr ⟨ha, le_min han hab⟩, ?_⟩
          apply Finset.mem_image.mpr
          refine ⟨xs, (ih (n-a) a xs).mpr ?_, rfl⟩
          refine ⟨⟨(List.pairwise_cons.mp h.1.1).2,
            fun b hb => h.1.2 b (List.mem_cons_of_mem a hb)⟩, ?_, ?_,
            (List.pairwise_cons.mp h.1.1).1⟩
          · simp only [List.sum_cons] at h; omega
          · simp only [List.length_cons] at h; omega

/-- Every partition occurs, including its fixed-point parts. -/
theorem partitionRows_mem_partitionShapes {n : ℕ} (p : Nat.Partition n) :
    partitionRows p ∈ partitionShapes n n n := by
  apply (mem_partitionShapes n n n _).mpr
  refine ⟨partitionRows_isShape p, partitionRows_sum p, ?_, ?_⟩
  · simpa only [partitionRows_sum] using isShape_length_le_sum (partitionRows_isShape p)
  · intro a ha
    apply p.le_of_mem_parts
    rw [← partitionRows_parts p]
    exact ha

/-- Summing over the enumeration is the same as summing over all partitions of `n`. -/
theorem sum_partitionShapes (n : ℕ) (f : Shape → ℤ) :
    (∑ xs ∈ partitionShapes n n n, f xs) = ∑ p : Nat.Partition n, f (partitionRows p) := by
  classical
  symm
  apply Finset.sum_bij (fun p _ => partitionRows p)
  · intro p hp; exact partitionRows_mem_partitionShapes p
  · intro p hp q hq he; exact partitionRows_injective he
  · intro xs hxs
    have h := (mem_partitionShapes n n n xs).mp hxs
    exact ⟨rowsPartition xs h.1 h.2.1, Finset.mem_univ _, rowsPartition_rows _ _ _⟩
  · intro p hp; rfl

/-- Scalar count; avoids reducing large nested finite-set unions. -/
def partitionCount : ℕ → ℕ → ℕ → ℕ
  | 0, n, _ => if n = 0 then 1 else 0
  | fuel+1, n, bound => if n = 0 then 1 else
      ∑ a ∈ Finset.Icc 1 (min n bound), partitionCount fuel (n-a) a

theorem card_partitionShapes (fuel n bound : ℕ) :
    (partitionShapes fuel n bound).card = partitionCount fuel n bound := by
  induction fuel generalizing n bound with
  | zero => by_cases hn : n = 0 <;> simp [partitionShapes, partitionCount, hn]
  | succ fuel ih =>
    by_cases hn : n = 0
    · simp [partitionShapes, partitionCount, hn]
    · have hd : ((Finset.Icc 1 (min n bound) : Finset ℕ) : Set ℕ).PairwiseDisjoint
          (fun a => (partitionShapes fuel (n-a) a).image (List.cons a)) := by
        intro a ha b hb hne
        apply Finset.disjoint_left.mpr
        intro xs hax hbx
        obtain ⟨ys, hy, he⟩ := Finset.mem_image.mp hax
        obtain ⟨zs, hz, hf⟩ := Finset.mem_image.mp hbx
        exact hne (List.cons.inj (he.trans hf.symm)).1
      simp only [partitionShapes, partitionCount, if_neg hn]
      rw [Finset.card_biUnion hd]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.card_image_of_injective _ (fun xs ys he => (List.cons.inj he).2), ih]

/-- There are 672 partitions of degrees five to fifteen, counted without reduction by
transposition. -/
theorem finite_target_count :
    (∑ n ∈ Finset.Icc 5 15, Fintype.card (Nat.Partition n)) = 672 := by
  classical
  have hc : (∑ n ∈ Finset.Icc 5 15, (partitionShapes n n n).card) = 672 := by
    simp_rw [card_partitionShapes]
    decide
  have he (n : ℕ) : (partitionShapes n n n).card = Fintype.card (Nat.Partition n) := by
    have hh := sum_partitionShapes n (fun _ => 1)
    have hh' : ((partitionShapes n n n).card : ℤ) =
        (Fintype.card (Nat.Partition n) : ℤ) := by simpa using hh
    exact_mod_cast hh'
  calc
    _ = ∑ n ∈ Finset.Icc 5 15, (partitionShapes n n n).card := by simp_rw [he]
    _ = 672 := hc

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.mem_partitionShapes
#print axioms HSTZ.TauCetiFinite.partitionRows_mem_partitionShapes
#print axioms HSTZ.TauCetiFinite.sum_partitionShapes
#print axioms HSTZ.TauCetiFinite.card_partitionShapes
#print axioms HSTZ.TauCetiFinite.finite_target_count
