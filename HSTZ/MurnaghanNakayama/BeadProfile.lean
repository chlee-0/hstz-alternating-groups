import HSTZ.MurnaghanNakayama.BeadInterval

/-!
# Indexed changed rows and the leg

The interval endpoints are the bead cuts from `BeadInterval`. This file identifies
exactly which default-zero rows lose cells, gives the adjacent row equation, and
counts the occupied rows of the removed cells. Connectivity, the no-2-by-2
condition and the converse enumeration are proved in later files.
-/
namespace HSTZ.MurnaghanNakayama

abbrev rowAt (xs : Shape) (i : ℕ) : ℕ := (xs[i]?).getD 0

/-- Pointwise profile, retaining the final changed row and zero-trimmed tails. -/
def RowInterval (xs ys : Shape) (p q : ℕ) : Prop :=
  (∀ i, rowAt ys i < rowAt xs i ↔ p ≤ i ∧ i ≤ q) ∧
  (∀ i, i < p ∨ q < i → rowAt ys i = rowAt xs i) ∧
  (∀ i, p ≤ i → i < q → rowAt ys i + 1 = rowAt xs (i + 1))

private theorem rowInterval_cons (xs ys : Shape) (c p q : ℕ)
    (h : RowInterval xs ys p q) : RowInterval (c :: xs) (c :: ys) (p + 1) (q + 1) := by
  obtain ⟨hl, he, hs⟩ := h
  constructor
  · intro i
    cases i with
    | zero => simp [rowAt]
    | succ i => simpa [rowAt] using hl i
  constructor
  · intro i hi
    cases i with
    | zero => rfl
    | succ i =>
        have hh : i < p ∨ q < i := by omega
        simpa [rowAt] using he i hh
  · intro i hp hq
    cases i with
    | zero => omega
    | succ i =>
        have hp' : p ≤ i := by omega
        have hq' : i < q := by omega
        simpa [rowAt, Nat.add_assoc] using hs i hp' hq'

/-- Insertion beneath a removed leading bead, in indexed coordinates. The
positivity hypothesis is on the original decoded rows, not on the output. -/
theorem insertion_rowInterval (bs : List ℕ) (a b : ℕ) :
    (a :: bs).Pairwise (fun x y => y < x) →
    (∀ x ∈ decodeRows (a :: bs), 0 < x) → b < a →
      RowInterval (decodeRows (a :: bs)) (decodeRows (insertDesc b bs)) 0
        (bs.takeWhile (fun c => decide (b < c))).length := by
  induction bs generalizing a with
  | nil =>
      intro h hp hb
      constructor
      · intro i
        cases i <;> simp [rowAt, decodeRows, insertDesc, List.takeWhile, hb]
      constructor
      · intro i hi
        cases i <;> simp_all [rowAt, decodeRows, insertDesc, List.takeWhile]
      · intro i hi hj
        simp [List.takeWhile] at hj
  | cons c bs ih =>
      intro h hp hb
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      have hphead : 0 < a - (c :: bs).length := hp _ (by simp [decodeRows_cons])
      have hptail : ∀ x ∈ decodeRows (c :: bs), 0 < x := by
        intro x hx
        apply hp x
        rw [decodeRows_cons]
        exact List.mem_cons_of_mem _ hx
      by_cases hc : c ≤ b
      · have hn : ¬ b < c := by omega
        have hhead : b - (bs.length + 1) < a - (bs.length + 1) := by
          simp only [List.length_cons] at hphead
          omega
        have hcut : ((c :: bs).takeWhile (fun d => decide (b < d))).length = 0 := by
          simp [List.takeWhile, hn]
        rw [hcut]
        simp only [insertDesc, if_pos hc, decodeRows_cons]
        constructor
        · intro i
          cases i <;> simp [rowAt, hhead]
        constructor
        · intro i hi
          cases i <;> simp_all [rowAt]
        · intro i hi hj
          omega
      · have hbc : b < c := by omega
        obtain ⟨hl, he, hs⟩ := ih c ht hptail hbc
        have hcpos : 0 < c - bs.length := hptail _ (by simp [decodeRows_cons])
        have hac : c < a := ha c (by simp)
        have hhead : c - (bs.length + 1) < a - (bs.length + 1) := by
          simp only [List.length_cons] at hphead
          omega
        have hstep : c - (bs.length + 1) + 1 = c - bs.length := by omega
        have hcut : ((c :: bs).takeWhile (fun d => decide (b < d))).length =
            (bs.takeWhile (fun d => decide (b < d))).length + 1 := by
          simp [List.takeWhile, hbc]
        rw [hcut]
        simp only [insertDesc, if_neg hc, decodeRows_cons, insertDesc_length,
          List.length_cons]
        constructor
        · intro i
          cases i with
          | zero => simp [rowAt, hhead]
          | succ i => simpa [rowAt] using hl i
        constructor
        · intro i hi
          cases i with
          | zero => omega
          | succ i =>
              have hh : (bs.takeWhile (fun d => decide (b < d))).length < i := by
                omega
              simpa [rowAt] using he i (Or.inr hh)
        · intro i hi hj
          cases i with
          | zero => simpa [rowAt] using hstep
          | succ i =>
              have hh : i < (bs.takeWhile (fun d => decide (b < d))).length := by
                omega
              simpa [rowAt, Nat.add_assoc] using hs i (Nat.zero_le _) hh

/-- The arbitrary-source pointwise profile. Positivity of the original decoded
rows prevents Nat subtraction from concealing a changed row at zero. -/
theorem replacement_rowInterval (bs : List ℕ) (a b : ℕ) :
    bs.Pairwise (fun x y => y < x) → a ∈ bs →
    (∀ x ∈ decodeRows bs, 0 < x) → b < a →
      RowInterval (decodeRows bs) (decodeRows (sortDesc (b :: bs.erase a)))
        (bs.takeWhile (fun c => decide (a < c))).length
        ((bs.erase a).takeWhile (fun c => decide (b < c))).length := by
  induction bs with
  | nil => intro h ha; simp at ha
  | cons c bs ih =>
      intro h ha hp hb
      have hw := h.imp (fun hh => hh.le)
      obtain ⟨hc, ht⟩ := List.pairwise_cons.mp h
      by_cases hac : a = c
      · subst c
        rw [sorted_replacement _ hw, List.erase_cons_head]
        simpa [List.takeWhile] using insertion_rowInterval bs a b h hp hb
      · have hat : a ∈ bs := (List.mem_cons.mp ha).resolve_left hac
        have hac' : a < c := hc a hat
        have hbc : b < c := hb.trans hac'
        have hptail : ∀ x ∈ decodeRows bs, 0 < x := by
          intro x hx
          apply hp x
          rw [decodeRows_cons]
          exact List.mem_cons_of_mem _ hx
        have hh := ih ht hat hptail hb
        have he : (c :: bs).erase a = c :: bs.erase a := by
          simp [List.erase, beq_false_of_ne (Ne.symm hac)]
        have hlen := (restore_erase_perm bs a hat).length_eq
        simp only [List.length_cons] at hlen
        have hpcut : ((c :: bs).takeWhile (fun d => decide (a < d))).length =
            (bs.takeWhile (fun d => decide (a < d))).length + 1 := by
          simp [List.takeWhile, hac']
        have hqcut : ((c :: bs.erase a).takeWhile (fun d => decide (b < d))).length =
            ((bs.erase a).takeWhile (fun d => decide (b < d))).length + 1 := by
          simp [List.takeWhile, hbc]
        rw [sorted_replacement _ hw, he, hpcut, hqcut]
        simp only [insertDesc, if_neg (show ¬ c ≤ b by omega), decodeRows_cons,
          insertDesc_length, hlen]
        rw [sorted_replacement _ (ht.imp (fun h => h.le))] at hh
        exact rowInterval_cons _ _ _ _ _ hh

/-- Indexed row profile of a bead move, with the leg as computed by `moveBead`. -/
theorem moveBead_rowInterval (lam : Shape) (hlam : IsShape lam) (r a : ℕ)
    (ha : a ∈ beta lam) (m : Move) (hm : moveBead (beta lam) r a = some m) :
    RowInterval lam m.shape
      ((beta lam).takeWhile (fun c => decide (a < c))).length
      (((beta lam).takeWhile (fun c => decide (a < c))).length + m.leg) := by
  by_cases h : 0 < r ∧ r ≤ a ∧ a - r ∉ beta lam
  · have hpos : ∀ x ∈ decodeRows (beta lam), 0 < x := by
      rw [decodeRows_beta]
      exact hlam.2
    have hh := replacement_rowInterval (beta lam) a (a - r)
      (beta_pairwise lam hlam.1) ha hpos (show a - r < a by omega)
    rw [decodeRows_beta, moveBead_leg_cuts lam hlam r a ha m hm] at hh
    have hnd := replacement_nodup _ a (a - r) (beta_nodup lam hlam.1) ha h.2.2
    have ho := decodeRows_pairwise _ (sortDesc_strict hnd)
    have hrow (i : ℕ) : rowAt m.shape i =
        rowAt (decodeRows (sortDesc ((a - r) :: (beta lam).erase a))) i := by
      have hm' := hm
      simp only [moveBead, if_pos h, Option.some.injEq] at hm'
      rw [← hm']
      exact filter_positive_getD _ ho i
    obtain ⟨hl, he, hs⟩ := hh
    exact ⟨fun i => by rw [hrow]; exact hl i,
      fun i hi => by rw [hrow]; exact he i hi,
      fun i hp hq => by rw [hrow]; exact hs i hp hq⟩
  · simp [moveBead, h] at hm

/-- A row contains removed cells exactly when its default-zero length strictly
decreases. -/
theorem mem_removed_rows_iff (lam mu : Shape) (i : ℕ) :
    i ∈ (cellSet lam \ cellSet mu).image Prod.fst ↔ rowAt mu i < rowAt lam i := by
  constructor
  · intro hi
    obtain ⟨⟨j, k⟩, hc, he⟩ := Finset.mem_image.mp hi
    change j = i at he
    subst j
    obtain ⟨hl, hm⟩ := Finset.mem_sdiff.mp hc
    have h₁ := (mem_cellSet_iff lam i k).mp hl
    have h₂ : ¬ k < rowAt mu i := by
      intro hk
      exact hm ((mem_cellSet_iff mu i k).mpr hk)
    exact (Nat.le_of_not_gt h₂).trans_lt h₁
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨(i, rowAt mu i), Finset.mem_sdiff.mpr ⟨?_, ?_⟩, rfl⟩
    · exact (mem_cellSet_iff lam i _).mpr hi
    · intro hc
      exact (Nat.lt_irrefl _) ((mem_cellSet_iff mu i _).mp hc)

/-- The set of rows containing removed cells is the inclusive interval between the
two bead cuts. -/
theorem moveBead_removed_rows (lam : Shape) (hlam : IsShape lam) (r a : ℕ)
    (ha : a ∈ beta lam) (m : Move) (hm : moveBead (beta lam) r a = some m) :
    (cellSet lam \ cellSet m.shape).image Prod.fst =
      (Finset.range (m.leg + 1)).image
        (fun t => ((beta lam).takeWhile (fun c => decide (a < c))).length + t) := by
  have hp := (moveBead_rowInterval lam hlam r a ha m hm).1
  ext i
  rw [mem_removed_rows_iff, hp i]
  constructor
  · intro hi
    refine Finset.mem_image.mpr ⟨i - ((beta lam).takeWhile (fun c => decide (a < c))).length,
      Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro hi
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
    have hh := Finset.mem_range.mp ht
    omega

/-- The leg clause of `IsRimRemoval`, for every enumerated move. -/
theorem mem_moves_leg_card (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) :
    ((cellSet lam \ cellSet m.shape).image Prod.fst).card = m.leg + 1 := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hm
  rw [moveBead_removed_rows lam hlam r a ha m hm,
    Finset.card_image_of_injective _ (fun x y h => by omega), Finset.card_range]

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.insertion_rowInterval
#print axioms HSTZ.MurnaghanNakayama.replacement_rowInterval
#print axioms HSTZ.MurnaghanNakayama.moveBead_rowInterval
#print axioms HSTZ.MurnaghanNakayama.mem_removed_rows_iff
#print axioms HSTZ.MurnaghanNakayama.moveBead_removed_rows
#print axioms HSTZ.MurnaghanNakayama.mem_moves_leg_card
