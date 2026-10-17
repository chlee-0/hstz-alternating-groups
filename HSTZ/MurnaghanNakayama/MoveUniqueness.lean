import HSTZ.MurnaghanNakayama.RimValidity

/-!
# Uniqueness of enumerated bead moves

The first strictly changed row determines the source cut. Strict beta order
then determines the source bead, so the enumerator `moves` has no duplicate
summands.
-/
namespace HSTZ.MurnaghanNakayama

theorem bead_cut_injective (bs : List ℕ) :
    bs.Pairwise (fun x y => y < x) → ∀ a ∈ bs, ∀ b ∈ bs,
      (bs.takeWhile (fun c => decide (a < c))).length =
        (bs.takeWhile (fun c => decide (b < c))).length → a = b := by
  induction bs with
  | nil => intro h a ha; simp at ha
  | cons c bs ih =>
      intro h a ha b hb he
      obtain ⟨hc, ht⟩ := List.pairwise_cons.mp h
      by_cases hac : a = c
      · subst a
        by_cases hbc : b = c
        · exact hbc.symm
        · have hbt : b ∈ bs := (List.mem_cons.mp hb).resolve_left hbc
          have hlt := hc b hbt
          simp [List.takeWhile, hlt] at he
      · have hat : a ∈ bs := (List.mem_cons.mp ha).resolve_left hac
        have halt := hc a hat
        by_cases hbc : b = c
        · subst b
          simp [List.takeWhile, halt] at he
        · have hbt : b ∈ bs := (List.mem_cons.mp hb).resolve_left hbc
          have hblt := hc b hbt
          apply ih ht a hat b hbt
          simpa [List.takeWhile, halt, hblt] using he

/-- Equal output shapes determine the source bead. -/
theorem moveBead_source_eq_of_shape_eq (lam : Shape) (hlam : IsShape lam) (r a b : ℕ)
    (ha : a ∈ beta lam) (hb : b ∈ beta lam) (m n : Move)
    (hm : moveBead (beta lam) r a = some m)
    (hn : moveBead (beta lam) r b = some n) (he : m.shape = n.shape) : a = b := by
  let p := ((beta lam).takeWhile (fun c => decide (a < c))).length
  let q := ((beta lam).takeWhile (fun c => decide (b < c))).length
  have hp := moveBead_rowInterval lam hlam r a ha m hm
  have hq := moveBead_rowInterval lam hlam r b hb n hn
  rw [he] at hp
  change RowInterval lam n.shape p (p + m.leg) at hp
  change RowInterval lam n.shape q (q + n.leg) at hq
  have hp' := (hp.1 p).mpr ⟨by omega, by omega⟩
  have hq' := (hq.1 q).mpr ⟨by omega, by omega⟩
  have hpq := ((hp.1 q).mp hq').1
  have hqp := ((hq.1 p).mp hp').1
  apply bead_cut_injective (beta lam) (beta_pairwise lam hlam.1) a ha b hb
  change p = q
  omega

private theorem filterMap_nodup_of_source_eq (bs : List ℕ) (f : ℕ → Option Move) :
    bs.Nodup →
    (∀ a ∈ bs, ∀ b ∈ bs, ∀ m, f a = some m → f b = some m → a = b) →
      (bs.filterMap f).Nodup := by
  induction bs with
  | nil => intro h hi; simp
  | cons a bs ih =>
      intro h hi
      obtain ⟨hna, ht⟩ := List.nodup_cons.mp h
      have hrec := ih ht (by
        intro b hb c hc m hbm hcm
        exact hi b (by simp [hb]) c (by simp [hc]) m hbm hcm)
      cases hf : f a with
      | none => simpa [List.filterMap, hf] using hrec
      | some m =>
          simp only [List.filterMap_cons, hf]
          apply List.nodup_cons.mpr
          refine ⟨?_, hrec⟩
          intro hm
          obtain ⟨b, hb, hfb⟩ := List.mem_filterMap.mp hm
          have he := hi a (by simp) b (by simp [hb]) m hf hfb
          exact hna (by simpa only [he] using hb)

/-- No duplicate summands for any requested removal length, including zero. -/
theorem moves_nodup (lam : Shape) (hlam : IsShape lam) (r : ℕ) :
    (moves lam r).Nodup := by
  apply filterMap_nodup_of_source_eq (beta lam) (moveBead (beta lam) r)
    (beta_nodup lam hlam.1)
  intro a ha b hb m hm hn
  exact moveBead_source_eq_of_shape_eq lam hlam r a b ha hb m m hm hn rfl

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.bead_cut_injective
#print axioms HSTZ.MurnaghanNakayama.moveBead_source_eq_of_shape_eq
#print axioms HSTZ.MurnaghanNakayama.moves_nodup
