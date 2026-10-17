import HSTZ.MurnaghanNakayama.RimConverse
import HSTZ.MurnaghanNakayama.MoveUniqueness

/-!
# Reconstructing the bead move

An unchanged leading row is stripped off. In a leading changed interval, strip
one crossed row at a time; its new height is fixed by the adjacent row equation.
At the final changed row the lowered bead is its new height plus the remaining
length. This proves that every geometric rim-hook removal is produced by the
enumerator.
-/
namespace HSTZ.MurnaghanNakayama

private theorem isShape_tail (xs : Shape) (h : IsShape xs) : IsShape xs.tail := by
  cases xs with
  | nil => simpa using h
  | cons a xs =>
      exact ⟨(List.pairwise_cons.mp h.1).2, fun b hb => h.2 b (List.mem_cons_of_mem a hb)⟩

private theorem rowAt_tail (xs : Shape) (i : ℕ) : rowAt xs.tail i = rowAt xs (i + 1) := by
  cases xs <;> simp [rowAt]

private theorem rowInterval_tail (lam mu : Shape) (p q : ℕ)
    (h : RowInterval lam mu p (q + 1)) : RowInterval lam.tail mu.tail (p - 1) q := by
  constructor
  · intro i
    simp only [rowAt_tail]
    constructor
    · intro hi
      have hh := (h.1 (i + 1)).mp hi
      omega
    · intro hi
      exact (h.1 (i + 1)).mpr ⟨by omega, by omega⟩
  constructor
  · intro i hi
    simp only [rowAt_tail]
    exact h.2.1 (i + 1) (by omega)
  · intro i hp hq
    simp only [rowAt_tail]
    exact h.2.2 (i + 1) (by omega) (by omega)

private theorem decodeBeta_cons (a : ℕ) (bs : List ℕ) :
    decodeBeta (a :: bs) =
      if 0 < a - bs.length then (a - bs.length) :: decodeBeta bs else decodeBeta bs := by
  change ((decodeRows (a :: bs)).filter (fun x => decide (0 < x))) = _
  rw [decodeRows_cons]
  by_cases h : 0 < a - bs.length <;> simp [List.filter, h] <;> rfl

private theorem shape_cons_tail (mu : Shape) (hmu : IsShape mu) :
    (if 0 < rowAt mu 0 then rowAt mu 0 :: mu.tail else mu.tail) = mu := by
  cases mu with
  | nil => simp [rowAt]
  | cons a mu =>
      have hp := hmu.2 a (by simp)
      simp [rowAt, hp]

/-- Recover a lowered bead when the first changed row is the first row. -/
theorem leading_profile_reconstruction (lam : Shape) :
    ∀ mu, IsShape lam → IsShape mu → ∀ q, q < lam.length →
      RowInterval lam mu 0 q →
      ∃ b, b < (beta lam).headD 0 ∧ b ∉ beta lam ∧
        decodeBeta (sortDesc (b :: (beta lam).tail)) = mu := by
  induction lam with
  | nil => intro mu hl hm q hq; simp at hq
  | cons a xs ih =>
      intro mu hlam hmu q hq hp
      have hxs : IsShape xs := isShape_tail (a :: xs) hlam
      have hmTail : IsShape mu.tail := isShape_tail mu hmu
      have hapos := hlam.2 a (by simp)
      rw [beta_cons]
      change ∃ b, b < a + xs.length ∧ b ∉ (a + xs.length) :: beta xs ∧
        decodeBeta (sortDesc (b :: beta xs)) = mu
      cases q with
      | zero =>
          have htail : mu.tail = xs := shape_eq_of_rowAt_eq _ _ hmTail.2 hxs.2 (by
            intro i
            rw [rowAt_tail]
            simpa [rowAt] using hp.2.1 (i + 1) (Or.inr (by omega)))
          have hbound : ∀ x ∈ xs, x ≤ rowAt mu 0 := by
            rw [← htail]
            cases mu with
            | nil => simp
            | cons u us => exact (List.pairwise_cons.mp hmu.1).1
          have hsmall := beta_lt_of_le (rowAt mu 0) xs hbound
          let b := rowAt mu 0 + xs.length
          have hloss : rowAt mu 0 < a := (hp.1 0).mpr ⟨by omega, by omega⟩
          have hb : b < a + xs.length := by dsimp [b]; omega
          refine ⟨b, hb, ?_, ?_⟩
          · intro hh
            rcases List.mem_cons.mp hh with he | he
            · omega
            · have hh := hsmall b he
              change b < b at hh
              omega
          · have hs : sortDesc (b :: beta xs) = b :: beta xs :=
              sortDesc_eq_self _ (List.pairwise_cons.mpr
                ⟨fun c hc => (hsmall c hc).le,
                  (beta_pairwise xs hxs.1).imp (fun h => h.le)⟩)
            rw [hs, decodeBeta_cons, beta_length, decodeBeta_beta_of_pos xs hxs.2]
            have hbrow : b - xs.length = rowAt mu 0 := by dsimp [b]; omega
            rw [hbrow, ← htail]
            exact shape_cons_tail mu hmu
      | succ q =>
          cases xs with
          | nil => simp at hq
          | cons c cs =>
              have htail := rowInterval_tail (a :: c :: cs) mu 0 q hp
              obtain ⟨b, hb, hnb, hdec⟩ := ih mu.tail hxs hmTail q
                (by simp only [List.length_cons] at hq ⊢; omega) (by simpa using htail)
              rw [beta_cons] at hb hnb hdec
              change b < c + cs.length at hb
              change decodeBeta (sortDesc (b :: beta cs)) = mu.tail at hdec
              have hca : c ≤ a := (List.pairwise_cons.mp hlam.1).1 c (by simp)
              have hbfull : b < a + (c :: cs).length := by
                simp only [List.length_cons]
                omega
              refine ⟨b, hbfull, ?_, ?_⟩
              · intro hh
                rcases List.mem_cons.mp hh with he | he
                · omega
                · exact hnb (by simpa only [beta_cons] using he)
              · have hwxs := (beta_pairwise (c :: cs) hxs.1).imp (fun h => h.le)
                have hwcs := (beta_pairwise cs (isShape_tail (c :: cs) hxs).1).imp
                  (fun h => h.le)
                have hs : sortDesc (b :: beta (c :: cs)) =
                    (c + cs.length) :: sortDesc (b :: beta cs) := by
                  change insertDesc b (sortDesc (beta (c :: cs))) =
                    (c + cs.length) :: insertDesc b (sortDesc (beta cs))
                  rw [sortDesc_eq_self _ hwxs, sortDesc_eq_self _ hwcs, beta_cons]
                  simp only [insertDesc, if_neg (show ¬ c + cs.length ≤ b by omega)]
                have hlen : (sortDesc (b :: beta cs)).length = cs.length + 1 := by
                  simp [sortDesc_length]
                have hstep := hp.2.2 0 (by omega) (by omega)
                change rowAt mu 0 + 1 = c at hstep
                have hrow : c + cs.length - (cs.length + 1) = rowAt mu 0 := by omega
                rw [hs, decodeBeta_cons, hlen, hrow, hdec]
                exact shape_cons_tail mu hmu

/-- Reconstruct the source and absent destination from an indexed rim profile. -/
theorem profile_replacement_exists (lam : Shape) :
    ∀ mu, IsShape lam → IsShape mu → ∀ p q, p ≤ q → q < lam.length →
      RowInterval lam mu p q →
      ∃ a ∈ beta lam, ∃ b, b < a ∧ b ∉ beta lam ∧
        decodeBeta (sortDesc (b :: (beta lam).erase a)) = mu := by
  induction lam with
  | nil => intro mu hl hm p q hpq hq; simp at hq
  | cons x xs ih =>
      intro mu hlam hmu p q hpq hq hp
      have hxs := isShape_tail (x :: xs) hlam
      have hx := hlam.2 x (by simp)
      cases p with
      | zero =>
          obtain ⟨b, hb, hnb, hdec⟩ := leading_profile_reconstruction (x :: xs)
            mu hlam hmu q hq hp
          rw [beta_cons] at hb hnb hdec
          change b < x + xs.length at hb
          change decodeBeta (sortDesc (b :: beta xs)) = mu at hdec
          refine ⟨x + xs.length, by simp [beta_cons], b, hb, ?_, ?_⟩
          · simpa only [beta_cons] using hnb
          · simpa only [beta_cons, List.erase_cons_head] using hdec
      | succ p =>
          cases q with
          | zero => omega
          | succ q =>
              have hhead := hp.2.1 0 (Or.inl (by omega))
              cases mu with
              | nil =>
                  change 0 = x at hhead
                  omega
              | cons u us =>
                  change u = x at hhead
                  subst u
                  have ht := rowInterval_tail (x :: xs) (x :: us) (p + 1) q hp
                  obtain ⟨a, ha, b, hb, hnb, hdec⟩ := ih us hxs
                    (isShape_tail (x :: us) hmu) p q (by omega)
                    (by simp only [List.length_cons] at hq; omega) (by simpa using ht)
                  have hsmall := beta_lt_of_le x xs (List.pairwise_cons.mp hlam.1).1 a ha
                  have hbfull : b < x + xs.length := hb.trans hsmall
                  rw [beta_cons]
                  refine ⟨a, List.mem_cons_of_mem _ ha, b, hb, ?_, ?_⟩
                  · intro hh
                    rcases List.mem_cons.mp hh with he | he
                    · omega
                    · exact hnb he
                  · have he : ((x + xs.length) :: beta xs).erase a =
                        (x + xs.length) :: (beta xs).erase a := by
                      simp [List.erase, beq_false_of_ne (show x + xs.length ≠ a by omega)]
                    have hw := (beta_pairwise (x :: xs) hlam.1).imp (fun h => h.le)
                    have hwt := (beta_pairwise xs hxs.1).imp (fun h => h.le)
                    have hs := sorted_replacement (beta (x :: xs)) hw a b
                    rw [beta_cons, he] at hs
                    rw [he, hs]
                    simp only [insertDesc, if_neg (show ¬ x + xs.length ≤ b by omega)]
                    rw [← sorted_replacement (beta xs) hwt a b, decodeBeta_cons]
                    have hlen : (sortDesc (b :: (beta xs).erase a)).length = xs.length := by
                      have hh := (restore_erase_perm (beta xs) a ha).length_eq
                      simp only [List.length_cons, beta_length] at hh
                      simpa [sortDesc_length] using hh
                    rw [hlen, hdec]
                    simp [hx]

/-- Every geometric rim-hook removal occurs in the enumerator `moves`. -/
theorem isRimRemoval_mem_moves (lam mu : Shape) (r leg : ℕ)
    (h : IsRimRemoval lam mu r leg) : ({ shape := mu, leg := leg } : Move) ∈ moves lam r := by
  obtain ⟨p, q, hpq, hq, hp⟩ := isRimRemoval_rowInterval lam mu r leg h
  obtain ⟨hlam, hmu, hsub, hr, hcard, hconn, hno, hleg⟩ := h
  obtain ⟨a, ha, b, hb, hnb, hdec⟩ := profile_replacement_exists lam mu hlam hmu p q hpq hq hp
  let r' := a - b
  have hab : a - r' = b := by dsimp [r']; omega
  have hguard : 0 < r' ∧ r' ≤ a ∧ a - r' ∉ beta lam :=
    ⟨by dsimp [r']; omega, Nat.sub_le .., by rwa [hab]⟩
  let m : Move := Move.mk mu
    (((beta lam).filter (fun c => decide (b < c ∧ c < a))).length)
  have hm : moveBead (beta lam) r' a = some m := by
    rw [moveBead, if_pos hguard, hab, hdec]
  have hmem : m ∈ moves lam r' := List.mem_filterMap.mpr ⟨a, ha, hm⟩
  have hsize := mem_moves_removed_card lam hlam r' m hmem
  change (cellSet lam \ cellSet mu).card = r' at hsize
  have hrr : r' = r := by omega
  have hactual := mem_moves_leg_card lam hlam r' m hmem
  have hle : m.leg = leg := by
    change ((cellSet lam \ cellSet mu).image Prod.fst).card = m.leg + 1 at hactual
    omega
  have he : m = { shape := mu, leg := leg } := congrArg (Move.mk mu) hle
  rw [hrr, he] at hmem
  exact hmem

/-- The enumerator `moves` lists every rim-hook removal exactly once, with the
correct leg length. -/
theorem moveEnumerationCorrect : MoveEnumerationCorrect := by
  intro lam hlam r hr
  refine ⟨moves_nodup lam hlam r, ?_⟩
  intro m
  exact ⟨mem_moves_isRimRemoval lam hlam r m,
    fun h => isRimRemoval_mem_moves lam m.shape r m.leg h⟩

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.leading_profile_reconstruction
#print axioms HSTZ.MurnaghanNakayama.profile_replacement_exists
#print axioms HSTZ.MurnaghanNakayama.isRimRemoval_mem_moves
#print axioms HSTZ.MurnaghanNakayama.moveEnumerationCorrect
