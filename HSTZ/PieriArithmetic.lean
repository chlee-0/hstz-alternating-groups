import HSTZ.BalancePacking

/-! Arithmetic of even precursors, including the two-singleton alternative
packing. This file contains arithmetic only; no Pieri or support theorem is proved
here. Natural subtraction is truncated. -/
namespace HSTZ

/-- An even element of the interval [max(0,beta-x), min(beta,c-beta)], in
naturals. -/
def EvenPrecursor (c x beta : ℕ) : Prop :=
  ∃ y, y%2=0 ∧ beta-x ≤ y ∧ y ≤ min beta (c-beta)

private theorem even_in_interval {l u : ℕ} (h : l < u) :
    ∃ y, y%2=0 ∧ l ≤ y ∧ y ≤ u := by
  by_cases hl : l%2=0
  · exact ⟨l,hl,le_refl _,by omega⟩
  · exact ⟨l+1,by omega,by omega,by omega⟩

/-- The interval is precisely an ordered, even-row, size-c precursor with
horizontal-strip interlacing. The beta<=c guard prevents false zero-tail
solutions caused by natural subtraction. -/
theorem even_precursor_iff_interlacing {c x alpha beta : ℕ}
    (hc : c%2=0) (hn : alpha+beta=c+x) (hb : beta ≤ c) :
    EvenPrecursor c x beta ↔
    ∃ gamma y, gamma+y=c ∧ gamma%2=0 ∧ y%2=0 ∧ y ≤ gamma ∧
      y ≤ beta ∧ beta ≤ gamma ∧ gamma ≤ alpha := by
  constructor
  · rintro ⟨y,hy,hl,hu⟩
    refine ⟨c-y,y,?_,?_,hy,?_,?_,?_,?_⟩ <;> omega
  · rintro ⟨gamma,y,hn',hg,hy,hgy,hyb,hbg,hga⟩
    exact ⟨y,hy,by omega,by omega⟩

/-- Any legal odd added size has an even precursor; the application uses x = 1
or 3. The arithmetic holds for all odd x, but no local support is claimed for other
values. -/
theorem even_precursor_odd {c x beta : ℕ} (hc : c%2=0) (hx : x%2=1)
    (hlegal : x ≤ c+1) (hshape : 2*beta ≤ c+x) : EvenPrecursor c x beta := by
  have hb : beta ≤ c := by omega
  by_cases hsmall : beta ≤ x
  · exact ⟨0,by omega,by omega,by omega⟩
  · exact even_in_interval (l:=beta-x) (u:=min beta (c-beta)) (by omega)

/-- Feasibility for two singletons, including the single balanced endpoint. -/
theorem even_precursor_two_iff (b beta : ℕ) (hb : beta ≤ b+2) :
    EvenPrecursor (2*b+2) 2 beta ↔ beta ≤ b+1 ∨ b%2=0 := by
  by_cases hsmall : beta ≤ b+1
  · have he : EvenPrecursor (2*b+2) 2 beta := by
      by_cases hb2 : beta ≤ 2
      · exact ⟨0,by omega,by omega,by omega⟩
      · exact even_in_interval (l:=beta-2) (u:=min beta (2*b+2-beta)) (by omega)
    exact iff_of_true he (Or.inl hsmall)
  · have hbeta : beta=b+2 := by omega
    constructor
    · rintro ⟨y,hy,hl,hu⟩
      right
      omega
    · rintro (h | h)
      · omega
      · exact ⟨b,h,by omega,by omega⟩

theorem even_precursor_two_endpoint (b y : ℕ) :
    (b+2-2 ≤ y ∧ y ≤ min (b+2) (2*b+2-(b+2))) ↔ y=b := by omega

/-- The two-singleton packing before sorting. -/
def alternativePair (b : ℕ) : List ℕ :=
  if (b+2)%2=0 then [b+2,b+2] else [b+3,b+1]

theorem alternativePair_properties (b : ℕ) :
    (alternativePair b).sum = 2*b+4 ∧ (alternativePair b).length = 2 ∧
    (∀ a ∈ alternativePair b, 0 < a ∧ a ≤ b+3) := by
  unfold alternativePair
  split_ifs
  · refine ⟨?_,by simp,?_⟩
    · simp only [List.sum_cons,List.sum_nil]; omega
    · intro a ha
      simp only [List.mem_cons,List.not_mem_nil] at ha
      rcases ha with rfl | rfl | hf
      · omega
      · omega
      · exact hf.elim
  · refine ⟨?_,by simp,?_⟩
    · simp only [List.sum_cons,List.sum_nil]; omega
    · intro a ha
      simp only [List.mem_cons,List.not_mem_nil] at ha
      rcases ha with rfl | rfl | hf
      · omega
      · omega
      · exact hf.elim

/-- Precursor feasibility agrees exactly with the local two-part row bound:
beta<=s for s even, beta<=s-1 for s odd, where s=b+2. -/
theorem alternativePair_precursor_iff (b beta : ℕ) (hb : beta ≤ b+2) :
    EvenPrecursor (2*b+2) 2 beta ↔
      beta ≤ (if (b+2)%2=0 then b+2 else b+1) := by
  rw [even_precursor_two_iff b beta hb]
  split_ifs <;> omega

/-- The alternative packing as an unsorted list: the main packing when delta=0,
and the two-singleton pair followed by the pairs k,...,3 when delta=1. -/
def alternativePacking (k b delta : ℕ) : List ℕ :=
  if delta=1 then alternativePair b ++ staircasePairs 3 k else balancePacking k b delta

/-- The alternative list also satisfies the four generic balance hypotheses.
Its representation-theoretic support is not proved here. -/
theorem alternativePacking_properties {k b delta r n : ℕ} (hk : 3 ≤ k)
    (hd : delta ≤ 1) (hr : r=2*b+delta) (hrmax : r ≤ k+1)
    (hn : 2*n=k*(k+1)+2*r) :
    (alternativePacking k b delta).sum = n ∧
    (∀ a ∈ alternativePacking k b delta, 0 < a) ∧
    2*k-4 ≤ (alternativePacking k b delta).length ∧
    (∀ a ∈ alternativePacking k b delta, 2*a ≤ k+7) := by
  by_cases hdelta : delta=1
  · rcases alternativePair_properties b with ⟨hps,hpl,hpb⟩
    rcases staircasePairs_properties (low:=3) (k:=k) (by omega) (by omega) (by omega) with
      ⟨hcs,hcl,hcb⟩
    norm_num at hcs hcl
    simp only [alternativePacking,if_pos hdelta,List.sum_append,List.length_append,hps,hpl]
    refine ⟨by nlinarith,?_,by omega,?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact (hpb a ha).1
      · exact (hcb a ha).1
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · have := (hpb a ha).2; omega
      · exact (hcb a ha).2
  · simpa only [alternativePacking,if_neg hdelta] using balancePacking_properties hk hd hr hrmax hn

/-- The alternative list also satisfies the Young-prefix bound. -/
theorem alternativePacking_young_prefix (nu : YoungDiagram) {k b delta r : ℕ}
    (hk : 3 ≤ k) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hpar : r%2=delta) (hb : r=2*b+delta)
    (hn : 2*nu.card=k*(k+1)+2*r)
    (hfour : prefixSum nu.colLen 4 ≤ 2*k-2) (t : ℕ) :
    prefixSum nu.colLen t ≤ youngPrefix (alternativePacking k b delta) t := by
  have hd : delta ≤ 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
  obtain ⟨hs,hpos,hlen,hcap⟩ := alternativePacking_properties hk hd hb hrmax hn
  exact balance_young_prefix nu _ hk hr hn hs hpos hlen hcap hfour t

end HSTZ
#print axioms HSTZ.even_precursor_iff_interlacing
#print axioms HSTZ.even_precursor_odd
#print axioms HSTZ.even_precursor_two_iff
#print axioms HSTZ.even_precursor_two_endpoint
#print axioms HSTZ.alternativePair_precursor_iff
#print axioms HSTZ.alternativePacking_properties
#print axioms HSTZ.alternativePacking_young_prefix
