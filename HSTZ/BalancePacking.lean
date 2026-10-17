import HSTZ.BalancePrefix

/-! The unsorted balance packing and its numeric properties. The
representation-theoretic constituents that justify these numeric blocks are
separate statements and are not formalized in this file. -/
namespace HSTZ

/-- Balanced d-part list; all applications below have s>=d, hence no zeros. -/
def balancedPack (d s : ℕ) : List ℕ :=
  List.replicate (s%d) (s/d+1) ++ List.replicate (d-s%d) (s/d)

theorem balancedPack_length {d s : ℕ} (hd : 0 < d) :
    (balancedPack d s).length = d := by
  have hm := Nat.mod_lt s hd
  simp [balancedPack]
  omega

theorem balancedPack_sum {d s : ℕ} (hd : 0 < d) :
    (balancedPack d s).sum = s := by
  have hm := Nat.mod_lt s hd
  have he := Nat.mod_add_div s d
  have hs : d-s%d+s%d=d := by omega
  simp only [balancedPack,List.sum_append,List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
  nlinarith

theorem balancedPack_bounds {d s a : ℕ} (hd : 0 < d) (hs : d ≤ s)
    (ha : a ∈ balancedPack d s) : 0 < a ∧ d*a ≤ s+d := by
  have hq : 0 < s/d := Nat.div_pos hs hd
  have hm := Nat.mod_add_div s d
  have hbound : a ≤ s/d+1 := by
    rcases List.mem_append.mp ha with ha | ha
    · have := List.eq_of_mem_replicate ha; omega
    · have := List.eq_of_mem_replicate ha; omega
  have hpos : 0 < a := by
    rcases List.mem_append.mp ha with ha | ha <;>
      have := List.eq_of_mem_replicate ha <;> omega
  refine ⟨hpos,?_⟩
  calc
    d*a ≤ d*(s/d+1) := Nat.mul_le_mul_left d hbound
    _ = d*(s/d)+d := by ring
    _ ≤ s+d := by omega

/-- Pair k,k-1 downward to the cutoff low. Retain an unmatched low column. -/
def staircasePairs (low k : ℕ) : List ℕ :=
  if k < low then [] else if k=low then [low]
  else balancedPack 4 (2*k-1) ++ staircasePairs low (k-2)
termination_by k

theorem staircasePairs_properties {low k : ℕ} (hlow : 3 ≤ low)
    (hlow4 : low ≤ 4) (hk : low ≤ k+1) :
    2*(staircasePairs low k).sum+(low-1)*low = k*(k+1) ∧
    2*k ≤ (staircasePairs low k).length+2*low-1 ∧
    (∀ a ∈ staircasePairs low k, 0 < a ∧ 2*a ≤ k+7) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hlt : k < low
    · have he : k+1=low := by omega
      have he' : low-1=k := by omega
      have heList : staircasePairs low k = [] := by
        rw [staircasePairs]; simp only [if_pos hlt]
      simp only [heList,List.sum_nil,List.length_nil,List.not_mem_nil]
      exact ⟨by rw [he',he]; simp,by omega,by simp⟩
    · by_cases heq : k=low
      · subst k
        have heList : staircasePairs low low = [low] := by
          rw [staircasePairs]; simp
        simp only [heList,List.sum_cons,List.sum_nil,
          Nat.add_zero,List.length_cons,List.length_nil,List.mem_singleton]
        have hs : low-1+1=low := by omega
        exact ⟨by nlinarith,by omega,by intro a ha; subst a; omega⟩
      · have hkbig : low+1 ≤ k := by omega
        have hk2 : k-2+2=k := by omega
        have hi := ih (k-2) (by omega) (by omega : low ≤ k-2+1)
        rcases hi with ⟨hiSum,hiLen,hiBounds⟩
        have hpSum := balancedPack_sum (s:=2*k-1) (by omega : 0 < 4)
        have hpLen := balancedPack_length (s:=2*k-1) (by omega : 0 < 4)
        have hs : 2*k-1+1=2*k := by omega
        have heList : staircasePairs low k = balancedPack 4 (2*k-1) ++ staircasePairs low (k-2) := by
          rw [staircasePairs]; simp only [if_neg hlt,if_neg heq]
        simp only [heList,List.sum_append,List.length_append]
        refine ⟨?_,?_,?_⟩
        · rw [hpSum]
          nlinarith
        · rw [hpLen]
          omega
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · have hb := balancedPack_bounds (by omega : 0 < 4) (by omega : 4 ≤ 2*k-1) ha
            exact ⟨hb.1,by omega⟩
          · have hb := hiBounds a ha
            exact ⟨hb.1,by omega⟩

/-- The packing list, with block order retained and no final sorting. -/
def balancePacking (k b delta : ℕ) : List ℕ :=
  balancedPack 2 (2*b+3+2*delta) ++ (if delta=1 then [2] else []) ++
    staircasePairs (3+delta) k

/-- The packing list satisfies all four assumptions of the generic balance
arithmetic. These are numeric properties, not representation-support statements. -/
theorem balancePacking_properties {k b delta r n : ℕ} (hk : 3 ≤ k)
    (hdelta : delta ≤ 1) (hr : r=2*b+delta) (hrmax : r ≤ k+1)
    (hn : 2*n=k*(k+1)+2*r) :
    (balancePacking k b delta).sum = n ∧
    (∀ a ∈ balancePacking k b delta, 0 < a) ∧
    2*k-4 ≤ (balancePacking k b delta).length ∧
    (∀ a ∈ balancePacking k b delta, 2*a ≤ k+7) := by
  have hi := staircasePairs_properties (k:=k) (low:=3+delta) (by omega) (by omega) (by omega)
  rcases hi with ⟨hiSum,hiLen,hiBounds⟩
  have hpSum := balancedPack_sum (s:=2*b+3+2*delta) (by omega : 0 < 2)
  have hpLen := balancedPack_length (s:=2*b+3+2*delta) (by omega : 0 < 2)
  have hpBounds : ∀ a ∈ balancedPack 2 (2*b+3+2*delta), 0 < a ∧ 2*a ≤ k+7 := by
    intro a ha
    have hb := balancedPack_bounds (by omega : 0 < 2) (by omega : 2 ≤ 2*b+3+2*delta) ha
    exact ⟨hb.1,by omega⟩
  have hsum : (balancePacking k b delta).sum = n := by
    simp only [balancePacking,List.sum_append,hpSum]
    interval_cases delta <;> norm_num at * <;> nlinarith
  refine ⟨hsum,?_,?_,?_⟩
  · intro a ha
    simp only [balancePacking,List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact (hpBounds a ha).1
    · split_ifs at ha with hd
      · simp only [List.mem_singleton] at ha; omega
      · simp at ha
    · exact (hiBounds a ha).1
  · simp only [balancePacking,List.length_append,hpLen]
    interval_cases delta <;> norm_num at * <;> omega
  · intro a ha
    simp only [balancePacking,List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact (hpBounds a ha).2
    · split_ifs at ha with hd
      · simp only [List.mem_singleton] at ha; omega
      · simp at ha
    · exact (hiBounds a ha).2

/-- The unsorted square packing has the same prefix function as the displayed
list, so no sorted-list machinery is needed. -/
theorem square_balancePacking_prefix (t : ℕ) :
    youngPrefix (balancePacking 7 4 0) t = youngPrefix squareBalanceParts t := by
  have h3 : staircasePairs 3 3 = [3] := by rw [staircasePairs]; norm_num
  have h5 : staircasePairs 3 5 = [3,2,2,2,3] := by
    rw [staircasePairs]; norm_num [balancedPack,h3,List.replicate_succ,List.replicate_zero]
  have h7 : staircasePairs 3 7 = [4,3,3,3,3,2,2,2,3] := by
    rw [staircasePairs]; norm_num [balancedPack,h5,List.replicate_succ,List.replicate_zero]
  have hlist : balancePacking 7 4 0 = [6,5,4,3,3,3,3,2,2,2,3] := by
    norm_num [balancePacking,balancedPack,h7,List.replicate_succ,List.replicate_zero]
  rw [hlist]
  simp only [youngPrefix,squareBalanceParts,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- The packing list in the generic prefix implication. -/
theorem balancePacking_young_prefix (nu : YoungDiagram) {k b delta r : ℕ}
    (hk : 3 ≤ k) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hpar : r%2=delta) (hb : r=2*b+delta)
    (hn : 2*nu.card=k*(k+1)+2*r)
    (hfour : prefixSum nu.colLen 4 ≤ 2*k-2) (t : ℕ) :
    prefixSum nu.colLen t ≤ youngPrefix (balancePacking k b delta) t := by
  have hd : delta ≤ 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
  obtain ⟨hs,hpos,hlen,hcap⟩ := balancePacking_properties hk hd hb hrmax hn
  exact balance_young_prefix nu _ hk hr hn hs hpos hlen hcap hfour t

/-- Numeric coverage at every witness degree for the packing list. The square
case is handled by its explicit prefix identity. This is numeric only;
representation support is a separate statement. -/
theorem balancePacking_numeric_coverage (nu : YoungDiagram) {k b delta r : ℕ}
    (hk : 7 ≤ k) (hr : 0 < r) (hrmax : r ≤ k+1)
    (hpar : r%2=delta) (hb : r=2*b+delta)
    (hn : 2*nu.card=k*(k+1)+2*r) :
    (∀ t, prefixSum nu.colLen t ≤ youngPrefix (balancePacking k b delta) t) ∨
    (∀ t, prefixSum nu.transpose.colLen t ≤ youngPrefix (balancePacking k b delta) t) ∨
    BandGeometry nu (2*k-1) r delta ∨ BandGeometry nu.transpose (2*k-1) r delta := by
  have hd : delta ≤ 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
  obtain ⟨hs,hpos,hlen,hcap⟩ := balancePacking_properties (by omega : 3 ≤ k) hd hb hrmax hn
  rcases large_degree_numeric_coverage nu _ hk hr hrmax hpar hn hs hpos hlen hcap with
    hy | hy | hgeom | hgeom | hsq
  · exact Or.inl hy
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr (Or.inl hgeom))
  · exact Or.inr (Or.inr (Or.inr hgeom))
  · rcases hsq with ⟨hsq,hk7,hr8,_⟩
    have hd0 : delta=0 := by rw [hr8] at hpar; omega
    have hb4 : b=4 := by omega
    apply Or.inl
    intro t
    rw [hsq,hk7,hb4,hd0,square_balancePacking_prefix]
    exact squareSix_young_prefix t

end HSTZ
#print axioms HSTZ.balancedPack_sum
#print axioms HSTZ.staircasePairs_properties
#print axioms HSTZ.balancePacking_properties
#print axioms HSTZ.square_balancePacking_prefix
#print axioms HSTZ.balancePacking_young_prefix
#print axioms HSTZ.balancePacking_numeric_coverage
