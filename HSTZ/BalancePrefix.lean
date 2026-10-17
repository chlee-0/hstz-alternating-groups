import HSTZ.YoungDiagramCompat
import HSTZ.BoundaryBand

/-! Numeric Young-prefix inequalities for an unsorted positive part list.
This proves dominance arithmetic only, not representation support for the
balance step. -/
namespace HSTZ

/-- An antitone nonnegative sequence has decreasing prefix averages. -/
theorem prefix_average_bound {h : ℕ → ℕ} (hh : Antitone h) {a t : ℕ}
    (hat : a ≤ t) : a * prefixSum h t ≤ t * prefixSum h a := by
  have hstep : ∀ i, a ≤ i → a*h i ≤ prefixSum h a := by
    intro i hi
    calc
      a*h i = ∑ j ∈ Finset.range a, h i := by simp
      _ ≤ prefixSum h a := Finset.sum_le_sum (fun j hj =>
        hh (le_trans (Nat.le_of_lt (Finset.mem_range.mp hj)) hi))
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hat
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show a+(s+1) = (a+s)+1 by omega, prefix_succ]
    have hs := hstep (a+s) (by omega)
    have hi := ih (by omega)
    nlinarith

private theorem prefix_zero_tail {h : ℕ → ℕ} (hh : Antitone h) {a : ℕ}
    (hz : h a = 0) (t : ℕ) : prefixSum h t ≤ prefixSum h a := by
  induction t with
  | zero => simp
  | succ t ih =>
    by_cases ht : t < a
    · exact prefix_mono h (by omega)
    · have hz' : h t = 0 := by have := hh (show a ≤ t by omega); omega
      rw [prefix_succ,hz',Nat.add_zero]
      exact ih

@[simp] theorem youngPrefix_one (A : List ℕ) (hp : ∀ a ∈ A, 0 < a) :
    youngPrefix A 1 = A.length := by
  induction A with
  | nil => simp [youngPrefix]
  | cons a A ih =>
    have ha := hp a (by simp)
    have hA : ∀ x ∈ A, 0 < x := fun x hx => hp x (by simp [hx])
    simp only [youngPrefix,List.map_cons,List.sum_cons,List.length_cons]
    change min 1 a+youngPrefix A 1 = A.length+1
    rw [Nat.min_eq_left (show 1 ≤ a by omega), ih hA]
    omega

theorem youngPrefix_mono (A : List ℕ) : Monotone (youngPrefix A) := by
  intro s t hst
  induction A with
  | nil => simp [youngPrefix]
  | cons a A ih =>
    simp only [youngPrefix,List.map_cons,List.sum_cons] at *
    have := min_le_min_right a hst
    omega

theorem youngPrefix_eq_sum (A : List ℕ) {t : ℕ} (ht : ∀ a ∈ A, a ≤ t) :
    youngPrefix A t = A.sum := by
  induction A with
  | nil => simp [youngPrefix]
  | cons a A ih =>
    have ha := ht a (by simp)
    have hA : ∀ x ∈ A, x ≤ t := fun x hx => ht x (by simp [hx])
    simpa [youngPrefix,Nat.min_eq_right ha] using ih hA

private theorem youngPrefix_extra (A : List ℕ) (hp : ∀ a ∈ A, 0 < a)
    (he : ∃ a ∈ A, 2 ≤ a) {t : ℕ} (ht : 2 ≤ t) :
    A.length+1 ≤ youngPrefix A t := by
  induction A with
  | nil => simp at he
  | cons a A ih =>
    have ha := hp a (by simp)
    have hA : ∀ x ∈ A, 0 < x := fun x hx => hp x (by simp [hx])
    have hlow := youngPrefix_mono A (show 1 ≤ t by omega)
    rw [youngPrefix_one A hA] at hlow
    by_cases ha2 : 2 ≤ a
    · have hmin : 2 ≤ min t a := le_min ht ha2
      simp only [youngPrefix,List.map_cons,List.sum_cons,List.length_cons]
      change A.length+1+1 ≤ min t a+youngPrefix A t
      omega
    · have heA : ∃ x ∈ A, 2 ≤ x := by
        obtain ⟨x,hx,hx2⟩ := he
        rcases List.mem_cons.mp hx with hx | hx
        · subst x; omega
        · exact ⟨x,hx,hx2⟩
      have hi := ih hA heA
      have hmin : 1 ≤ min t a := le_min (by omega) (by omega)
      simp only [youngPrefix,List.map_cons,List.sum_cons,List.length_cons]
      change A.length+1+1 ≤ min t a+youngPrefix A t
      omega

/-- Multiplied cap estimate; no maximum or sorted list is required. -/
theorem youngPrefix_cap_bound (A : List ℕ) {B t : ℕ}
    (hcap : ∀ a ∈ A, 2*a ≤ B) (ht : 2*t ≤ B) :
    2*t*A.sum ≤ B*youngPrefix A t := by
  induction A with
  | nil => simp [youngPrefix]
  | cons a A ih =>
    have ha := hcap a (by simp)
    have hA : ∀ x ∈ A, 2*x ≤ B := fun x hx => hcap x (by simp [hx])
    have hi := ih hA
    have hpart : 2*t*a ≤ B*min t a := by
      by_cases hat : a ≤ t
      · rw [Nat.min_eq_right hat]
        exact Nat.mul_le_mul_right a ht
      · rw [Nat.min_eq_left (by omega : t ≤ a)]
        nlinarith [Nat.mul_le_mul_left t ha]
    simp only [youngPrefix,List.map_cons,List.sum_cons] at *
    nlinarith

/-- Generic balance dominance at the witness degree, including all short
prefixes and the all-singleton list. Only numerical hypotheses occur. -/
theorem balance_young_prefix (nu : YoungDiagram) (A : List ℕ) {k r : ℕ}
    (hk : 3 ≤ k) (hr : 0 < r)
    (hn : 2*nu.card = k*(k+1)+2*r)
    (hsum : A.sum = nu.card) (hp : ∀ a ∈ A, 0 < a)
    (hlen : 2*k-4 ≤ A.length) (hcap : ∀ a ∈ A, 2*a ≤ k+7)
    (hfour : prefixSum nu.colLen 4 ≤ 2*k-2) (t : ℕ) :
    prefixSum nu.colLen t ≤ youngPrefix A t := by
  have hsub : 2*k-2+2 = 2*k := by omega
  have hdegree : 2*k-2 < nu.card := by nlinarith
  have hpos4 : 0 < nu.colLen 4 := by
    by_contra hz
    have hzero : nu.colLen 4 = 0 := by omega
    have hb := prefix_zero_tail nu.colLen_antitone hzero (nu.rowLen 0)
    have hc : prefixSum nu.colLen (nu.rowLen 0) = nu.card := by
      rw [← fromColumns_card nu.colLen nu.colLen_antitone (nu.rowLen 0),fromColumns_target]
    omega
  have hpos3 := nu.colLen_anti 3 4 (by omega)
  have hpos2 := nu.colLen_anti 2 4 (by omega)
  have hpos1 := nu.colLen_anti 1 4 (by omega)
  have hshort := hfour
  simp only [prefixSum,Finset.sum_range_succ,Finset.sum_range_zero] at hshort
  by_cases ht0 : t=0
  · subst t; simp [youngPrefix]
  by_cases he : ∃ a ∈ A, 2 ≤ a
  · by_cases ht4 : t < 4
    · have h1 := youngPrefix_one A hp
      have h2 := youngPrefix_extra A hp he (le_refl 2)
      have h3 := youngPrefix_extra A hp he (by omega : 2 ≤ 3)
      interval_cases t <;> simp only [prefixSum,Finset.sum_range_succ,Finset.sum_range_zero] <;> omega
    · by_cases hall : ∀ a ∈ A, a ≤ t
      · rw [youngPrefix_eq_sum A hall,hsum]
        exact column_prefix_le_card nu t
      · have htcap : 2*t ≤ k+7 := by
          push_neg at hall
          obtain ⟨a,ha,hat⟩ := hall
          have := hcap a ha
          omega
        have hlist := youngPrefix_cap_bound A hcap htcap
        rw [hsum] at hlist
        have hcols := prefix_average_bound nu.colLen_antitone (show 4 ≤ t by omega)
        have hbound := Nat.mul_le_mul_left t hfour
        have hkbound : 2*k-2 = 2*(k-1) := by omega
        rw [hkbound] at hbound
        have hmargin : (k-1)*(k+7) < 4*nu.card := by
          have hksub : k-1+1=k := by omega
          nlinarith [sq_nonneg (k-2 : ℤ)]
        have htpos : 0 < t := by omega
        have hB : 0 < k+7 := by omega
        have hcross := Nat.mul_le_mul_left (k+7) (hcols.trans hbound)
        have hcross2 := Nat.mul_le_mul_left 2 hlist
        have hstrict := Nat.mul_lt_mul_of_pos_left hmargin htpos
        nlinarith
  · have hall : ∀ a ∈ A, a ≤ t := by
      intro a ha
      have ha1 : a < 2 := by by_contra h; exact he ⟨a,ha,by omega⟩
      omega
    rw [youngPrefix_eq_sum A hall,hsum]
    exact column_prefix_le_card nu t

/-- The complete numeric large-degree split. The balance list's four numeric
properties are explicit inputs; no representation support is asserted. -/
theorem large_degree_numeric_coverage (nu : YoungDiagram) (A : List ℕ) {k r delta : ℕ}
    (hk : 7 ≤ k) (hr : 0 < r) (hrmax : r ≤ k+1) (hpar : r%2=delta)
    (hn : 2*nu.card = k*(k+1)+2*r)
    (hsum : A.sum = nu.card) (hp : ∀ a ∈ A, 0 < a)
    (hlen : 2*k-4 ≤ A.length) (hcap : ∀ a ∈ A, 2*a ≤ k+7) :
    (∀ t, prefixSum nu.colLen t ≤ youngPrefix A t) ∨
    (∀ t, prefixSum nu.transpose.colLen t ≤ youngPrefix A t) ∨
    BandGeometry nu (2*k-1) r delta ∨ BandGeometry nu.transpose (2*k-1) r delta ∨
    (nu = squareSix ∧ k=7 ∧ r=8 ∧
      ∀ t, prefixSum nu.colLen t ≤ youngPrefix squareBalanceParts t) := by
  by_cases hc : prefixSum nu.colLen 4 ≤ 2*k-2
  · exact Or.inl (balance_young_prefix nu A (by omega) hr hn hsum hp hlen hcap hc)
  by_cases hrow : prefixSum nu.rowLen 4 ≤ 2*k-2
  · apply Or.inr ∘ Or.inl
    have hcard : nu.transpose.card = nu.card := by
      simp [YoungDiagram.card,YoungDiagram.transpose]
    apply balance_young_prefix nu.transpose A (by omega) hr
      (by rw [hcard]; exact hn) (by rw [hcard]; exact hsum) hp hlen hcap
    simpa only [prefixSum,YoungDiagram.colLen_transpose] using hrow
  · apply Or.inr ∘ Or.inr
    rcases large_degree_band_or_square nu hk hr hrmax hpar hn (by omega) (by omega) with hb | hb | hs
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · rcases hs with ⟨hs,hk7,hr8⟩
      exact Or.inr (Or.inr ⟨hs,hk7,hr8,by rw [hs]; exact squareSix_young_prefix⟩)

end HSTZ
#print axioms HSTZ.prefix_average_bound
#print axioms HSTZ.youngPrefix_cap_bound
#print axioms HSTZ.balance_young_prefix
#print axioms HSTZ.large_degree_numeric_coverage
