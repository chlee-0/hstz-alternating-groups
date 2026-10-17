import HSTZ.MurnaghanNakayama.BeadRows

/-!
# Changed-row interval and the leg counter

Deleting a bead increases the preceding padded rows by one. Reinsertion below the
deleted bead cancels those increases, decreases the crossed tail rows by one,
and leaves a suffix unchanged. The difference of the two cut lengths is exactly
the intervening-bead count that `moveBead` uses as the leg. Connectedness, the
no-2-by-2 condition, occupied-row counts and completeness are proved in later files.
-/
namespace HSTZ.MurnaghanNakayama

private theorem take_prefix_add (xs ys : List ℕ) (k : ℕ) :
    (xs ++ ys).take (xs.length + k) = xs ++ ys.take k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have h : (a :: xs).length + k = (xs.length + k) + 1 := by
        simp only [List.length_cons]
        omega
      rw [h]
      change a :: (xs ++ ys).take (xs.length + k) = a :: (xs ++ ys.take k)
      exact congrArg (List.cons a) ih

private theorem drop_prefix_add (xs ys : List ℕ) (k : ℕ) :
    (xs ++ ys).drop (xs.length + k) = ys.drop k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have h : (a :: xs).length + k = (xs.length + k) + 1 := by
        simp only [List.length_cons]
        omega
      rw [h]
      change (xs ++ ys).drop (xs.length + k) = ys.drop k
      exact ih

private theorem cut_length_le (bs : List ℕ) (a : ℕ) :
    (bs.takeWhile (fun c => decide (a < c))).length ≤ bs.length := by
  induction bs with
  | nil => simp
  | cons c bs ih =>
      by_cases h : a < c <;> simp [List.takeWhile, h, ih]

/-- Decoder identity for erasing a bead; strictness supplies the natural-number
lower bounds. -/
theorem decodeRows_erase (bs : List ℕ) (a : ℕ) :
    bs.Pairwise (fun x y => y < x) → a ∈ bs →
      decodeRows (bs.erase a) =
        ((decodeRows bs).take (bs.takeWhile (fun c => decide (a < c))).length).map
          (fun x => x + 1) ++
        (decodeRows bs).drop ((bs.takeWhile (fun c => decide (a < c))).length + 1) := by
  induction bs with
  | nil => intro h ha; simp at ha
  | cons c bs ih =>
      intro h ha
      obtain ⟨hc, ht⟩ := List.pairwise_cons.mp h
      by_cases hac : a = c
      · subst c
        simp [decodeRows_cons, List.takeWhile]
      · have hat : a ∈ bs := (List.mem_cons.mp ha).resolve_left hac
        have hlt := hc a hat
        have hbound := strict_head_bound c bs (List.pairwise_cons.mpr ⟨hc, ht⟩)
        have hlen := (restore_erase_perm bs a hat).length_eq
        simp only [List.length_cons] at hlen
        have hrow : c - (bs.erase a).length = (c - bs.length) + 1 := by omega
        have he : (c :: bs).erase a = c :: bs.erase a := by
          simp [List.erase, beq_false_of_ne (Ne.symm hac)]
        rw [he, decodeRows_cons, hrow, ih ht hat]
        simp [decodeRows_cons, List.takeWhile, hlt, Nat.add_assoc]

private theorem filter_gt_nil (bs : List ℕ) (b : ℕ) :
    (∀ c ∈ bs, c ≤ b) → bs.filter (fun c => decide (b < c)) = [] := by
  induction bs with
  | nil => intro h; rfl
  | cons c bs ih =>
      intro h
      have hc := h c (by simp)
      have ht : ∀ d ∈ bs, d ≤ b := by intro d hd; exact h d (by simp [hd])
      simp [List.filter, Nat.not_lt.mpr hc, ih ht]

theorem filter_gt_eq_takeWhile (bs : List ℕ) (b : ℕ) :
    bs.Pairwise (fun x y => y ≤ x) →
      bs.filter (fun c => decide (b < c)) = bs.takeWhile (fun c => decide (b < c)) := by
  induction bs with
  | nil => intro h; rfl
  | cons c bs ih =>
      intro h
      obtain ⟨hc, ht⟩ := List.pairwise_cons.mp h
      by_cases hb : b < c
      · simp [List.filter, List.takeWhile, hb, ih ht]
      · have hall : ∀ d ∈ bs, d ≤ b := by
          intro d hd
          exact (hc d hd).trans (Nat.le_of_not_gt hb)
        simp [List.filter, List.takeWhile, hb, filter_gt_nil bs b hall]

private theorem filter_between_of_lt (bs : List ℕ) (a b : ℕ) :
    (∀ c ∈ bs, c < a) →
      bs.filter (fun c => decide (b < c ∧ c < a)) =
        bs.filter (fun c => decide (b < c)) := by
  induction bs with
  | nil => intro h; rfl
  | cons c bs ih =>
      intro h
      have hc := h c (by simp)
      have ht : ∀ d ∈ bs, d < a := by intro d hd; exact h d (by simp [hd])
      have hh := ih ht
      have hdec (d : ℕ) : decide (b < d ∧ d < a) =
          (decide (b < d) && decide (d < a)) := by
        by_cases h₁ : b < d <;> by_cases h₂ : d < a <;> simp [h₁, h₂]
      simp only [hdec] at hh
      simp [List.filter, hc, hh]

/-- Destination cut = source cut + the original intervening-bead count. -/
theorem replacement_cut_length (bs : List ℕ) (a b : ℕ) :
    bs.Pairwise (fun x y => y < x) → a ∈ bs → b < a →
      ((bs.erase a).takeWhile (fun c => decide (b < c))).length =
        (bs.takeWhile (fun c => decide (a < c))).length +
          (bs.filter (fun c => decide (b < c ∧ c < a))).length := by
  induction bs with
  | nil => intro h ha; simp at ha
  | cons c bs ih =>
      intro h ha hba
      obtain ⟨hc, ht⟩ := List.pairwise_cons.mp h
      by_cases hac : a = c
      · subst c
        have hw : bs.Pairwise (fun x y => y ≤ x) := ht.imp (fun h => h.le)
        rw [List.erase_cons_head]
        have hz : (a :: bs).takeWhile (fun c => decide (a < c)) = [] := by
          simp [List.takeWhile]
        have hf : (a :: bs).filter (fun c => decide (b < c ∧ c < a)) =
            bs.filter (fun c => decide (b < c ∧ c < a)) := by simp [List.filter]
        rw [hz, hf]
        simp only [List.length_nil, Nat.zero_add]
        rw [filter_between_of_lt bs a b hc, filter_gt_eq_takeWhile bs b hw]
      · have hat : a ∈ bs := (List.mem_cons.mp ha).resolve_left hac
        have hac' := hc a hat
        have hbc : b < c := hba.trans hac'
        have he : (c :: bs).erase a = c :: bs.erase a := by
          simp [List.erase, beq_false_of_ne (Ne.symm hac)]
        have hh := ih ht hat hba
        simp [he, List.takeWhile, List.filter, hac', hbc,
          Nat.not_lt.mpr hac'.le, hh, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem replacement_interval_bound (bs : List ℕ) (a b : ℕ)
    (h : bs.Pairwise (fun x y => y < x)) (ha : a ∈ bs) (hb : b < a) :
    (bs.takeWhile (fun c => decide (a < c))).length +
      (bs.filter (fun c => decide (b < c ∧ c < a))).length < bs.length := by
  have hcut := cut_length_le (bs.erase a) b
  have heq := replacement_cut_length bs a b h ha hb
  have hlen := (restore_erase_perm bs a ha).length_eq
  simp only [List.length_cons] at hlen
  omega

/-- Arbitrary-source replacement rows: prefix, crossed rows minus one,
inserted row and unchanged suffix, all before positivity filtering. -/
theorem decodeRows_replacement_interval (bs : List ℕ) (a b : ℕ)
    (h : bs.Pairwise (fun x y => y < x)) (ha : a ∈ bs) (hb : b < a) :
    let p := (bs.takeWhile (fun c => decide (a < c))).length
    let k := (bs.filter (fun c => decide (b < c ∧ c < a))).length
    decodeRows (sortDesc (b :: bs.erase a)) =
      (decodeRows bs).take p ++
        (((decodeRows bs).drop (p + 1)).take k).map (fun x => x - 1) ++
        (b - ((bs.erase a).dropWhile (fun c => decide (b < c))).length) ::
          ((decodeRows bs).drop (p + 1)).drop k := by
  dsimp only
  let p := (bs.takeWhile (fun c => decide (a < c))).length
  let k := (bs.filter (fun c => decide (b < c ∧ c < a))).length
  let pre := (decodeRows bs).take p
  let tail := (decodeRows bs).drop (p + 1)
  have hp : p ≤ (decodeRows bs).length := by
    rw [decodeRows_length]
    exact cut_length_le bs a
  have hlen : pre.length = p := by
    change ((decodeRows bs).take p).length = p
    rw [List.length_take, Nat.min_eq_left hp]
  have ht := take_prefix_add (pre.map (fun x => x + 1)) tail k
  have hd := drop_prefix_add (pre.map (fun x => x + 1)) tail k
  simp only [List.length_map, hlen] at ht hd
  have hcancel : (pre.map (fun x => x + 1)).map (fun x => x - 1) = pre := by
    simp [Function.comp_def]
  have hw : bs.Pairwise (fun x y => y ≤ x) := h.imp (fun h => h.le)
  rw [sorted_replacement bs hw a b, decodeRows_insertDesc,
    replacement_cut_length bs a b h ha hb]
  simp only [decodeRows_erase bs a h ha]
  change ((pre.map (fun x => x + 1) ++ tail).take (p + k)).map (fun x => x - 1) ++
    (b - ((bs.erase a).dropWhile (fun c => decide (b < c))).length) ::
      (pre.map (fun x => x + 1) ++ tail).drop (p + k) = _
  rw [ht, hd, List.map_append, hcancel]

theorem moveBead_leg_cuts (lam : Shape) (hlam : IsShape lam) (r a : ℕ)
    (ha : a ∈ beta lam) (m : Move) (hm : moveBead (beta lam) r a = some m) :
    (((beta lam).erase a).takeWhile (fun c => decide (a - r < c))).length =
      ((beta lam).takeWhile (fun c => decide (a < c))).length + m.leg := by
  by_cases h : 0 < r ∧ r ≤ a ∧ a - r ∉ beta lam
  · have hb : a - r < a := by omega
    simp only [moveBead, if_pos h, Option.some.injEq] at hm
    rw [← hm]
    exact replacement_cut_length (beta lam) a (a - r) (beta_pairwise lam hlam.1) ha hb
  · simp [moveBead, h] at hm

theorem moveBead_interval_bound (lam : Shape) (hlam : IsShape lam) (r a : ℕ)
    (ha : a ∈ beta lam) (m : Move) (hm : moveBead (beta lam) r a = some m) :
    ((beta lam).takeWhile (fun c => decide (a < c))).length + m.leg < lam.length := by
  have hcut := moveBead_leg_cuts lam hlam r a ha m hm
  have hle := cut_length_le ((beta lam).erase a) (a - r)
  have hlen := (restore_erase_perm (beta lam) a ha).length_eq
  simp only [List.length_cons, beta_length] at hlen
  omega

/-- Shape of the output of a bead move, with the leg as computed by `moveBead`. -/
theorem moveBead_shape_interval (lam : Shape) (hlam : IsShape lam) (r a : ℕ)
    (ha : a ∈ beta lam) (m : Move) (hm : moveBead (beta lam) r a = some m) :
    let p := ((beta lam).takeWhile (fun c => decide (a < c))).length
    m.shape =
      (lam.take p ++ ((lam.drop (p + 1)).take m.leg).map (fun x => x - 1) ++
        (a - r - (((beta lam).erase a).dropWhile (fun c => decide (a - r < c))).length) ::
          (lam.drop (p + 1)).drop m.leg).filter (fun x => decide (0 < x)) := by
  dsimp only
  by_cases h : 0 < r ∧ r ≤ a ∧ a - r ∉ beta lam
  · have hb : a - r < a := by omega
    simp only [moveBead, if_pos h, Option.some.injEq] at hm
    rw [← hm]
    change (decodeRows (sortDesc ((a - r) :: (beta lam).erase a))).filter _ = _
    have hh := decodeRows_replacement_interval (beta lam) a (a - r)
      (beta_pairwise lam hlam.1) ha hb
    dsimp only at hh
    rw [decodeRows_beta] at hh
    rw [hh]
  · simp [moveBead, h] at hm

theorem mem_moves_leg_cuts (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) :
    ∃ a ∈ beta lam, moveBead (beta lam) r a = some m ∧
      (((beta lam).erase a).takeWhile (fun c => decide (a - r < c))).length =
        ((beta lam).takeWhile (fun c => decide (a < c))).length + m.leg := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hm
  exact ⟨a, ha, hm, moveBead_leg_cuts lam hlam r a ha m hm⟩

theorem mem_moves_interval_witness (lam : Shape) (hlam : IsShape lam) (r : ℕ)
    (m : Move) (hm : m ∈ moves lam r) :
    ∃ a ∈ beta lam, moveBead (beta lam) r a = some m ∧
      (((beta lam).erase a).takeWhile (fun c => decide (a - r < c))).length =
        ((beta lam).takeWhile (fun c => decide (a < c))).length + m.leg ∧
      ((beta lam).takeWhile (fun c => decide (a < c))).length + m.leg < lam.length := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hm
  exact ⟨a, ha, hm, moveBead_leg_cuts lam hlam r a ha m hm,
    moveBead_interval_bound lam hlam r a ha m hm⟩

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.decodeRows_erase
#print axioms HSTZ.MurnaghanNakayama.filter_gt_eq_takeWhile
#print axioms HSTZ.MurnaghanNakayama.replacement_cut_length
#print axioms HSTZ.MurnaghanNakayama.replacement_interval_bound
#print axioms HSTZ.MurnaghanNakayama.decodeRows_replacement_interval
#print axioms HSTZ.MurnaghanNakayama.moveBead_leg_cuts
#print axioms HSTZ.MurnaghanNakayama.moveBead_interval_bound
#print axioms HSTZ.MurnaghanNakayama.moveBead_shape_interval
#print axioms HSTZ.MurnaghanNakayama.mem_moves_leg_cuts
#print axioms HSTZ.MurnaghanNakayama.mem_moves_interval_witness
