import HSTZ.YoungDiagramCompat
import HSTZ.WitnessCapacityKronecker
import HSTZ.BoundaryBand
import HSTZ.BalancePacking
import HSTZ.SmallKCoverage

/-! Ordered band selection discharges the original capacity guards.
Uses APIs from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No local balance or alternating-group conclusion is asserted. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem actualPath_height_le (h : ℕ → ℕ) (hh : Antitone h) (d K m : ℕ) :
    (containedPath h hh d K m).colLen 0 ≤ d := by
  by_contra hn
  have hx : (d,0) ∈ containedPath h hh d K m :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hr := ((mem_fromColumns _ _ _ _ _).mp hx).2
  have hd := greedy_le_depth h d K 0
  omega

private theorem actualAttachment_width_le {e : ℕ → ℕ} (he : Antitone e) {m t : ℕ}
    (hzero : ∀ i, t ≤ i → e i = 0) :
    (containedAttachment e he m).rowLen 0 ≤ t := by
  by_contra hn
  have hx : (0,t) ∈ containedAttachment e he m :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have hr := ((mem_fromColumns _ _ _ _ _).mp hx).2
  rw [hzero t (le_refl t)] at hr
  omega

private theorem actualAttachment_columns {e : ℕ → ℕ} (he : Antitone e) {m t : ℕ}
    (htm : t ≤ m) (hzero : ∀ i, t ≤ i → e i = 0) :
    (containedAttachment e he m).colLen = e := by
  funext i
  by_cases hi : i < m
  · exact fromColumns_colLen e he hi
  · have hc : (containedAttachment e he m).colLen i = 0 := by
      by_contra hn
      have hx : (0,i) ∈ containedAttachment e he m :=
        YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      have hm := ((mem_fromColumns _ _ _ _ _).mp hx).1
      omega
    rw [hc,hzero i (by omega)]

/-- With the same greedy diagrams, band feasibility supplies all factor guards. -/
theorem paperWitness_band_feasible_pos (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} {nu : YoungDiagram} (target : Tableau n nu)
    (hb : BandFeasible nu (witnessPathSize k) (2*b+delta) delta)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    0 < kronecker z z (transposeTableau target) := by
  obtain ⟨d,q,_,hd,_,hq,hrows,hclear,hbound⟩ := hb
  have hr : 0 < 2*b+delta := hp.positive_remainder
  have hpar : (2*b+delta)%2=delta := by have hh := hp.parity; omega
  obtain ⟨e,t,he,hc,_,htq,htm,hroom,hzero,hsize,_⟩ :=
    band_contained_target nu hr hpar hbound hrows hclear
  have hcapacity := hrows
  rw [row_prefix_eq_capped_columns] at hcapacity
  have hclear' : t*d+4 ≤ witnessPathSize k := by
    have hh := Nat.mul_le_mul_right d htq
    rw [Nat.mul_comm d q] at hclear
    omega
  have hpi := (actualPath_height_le nu.colLen nu.colLen_antitone d
    (witnessPathSize k) (nu.rowLen 0)).trans hd
  have hE := (actualAttachment_width_le he (m:=nu.rowLen 0) hzero).trans (htq.trans hq)
  have hc' : ColumnParity (containedAttachment e he (nu.rowLen 0)).colLen delta := by
    rw [actualAttachment_columns he htm hzero]
    exact hc
  exact containedWitness_capacity_kronecker_pos he k b delta hp target htm
    (fun c hh => (hroom c hh).2) hclear' hcapacity hsize hzero hpi hc' hE z

/-- Capacity is recovered from the geometry output itself, not from a greedy
identity for its existential `pi`/`theta`. -/
private theorem actualGeometry_capacity (nu pi theta : YoungDiagram) {e : ℕ → ℕ}
    {d K r : ℕ} (hs : prefixSum e (nu.rowLen 0) = r)
    (hcard : theta.card = K+r) (hle : theta ≤ nu)
    (hcols : ∀ i < nu.rowLen 0, pi.colLen i ≤ d ∧ theta.colLen i = pi.colLen i+e i) :
    K ≤ prefixSum (capacity nu.colLen d) (nu.rowLen 0) := by
  have htheta : fromColumns theta.colLen theta.colLen_antitone (nu.rowLen 0) = theta := by
    apply SetLike.ext
    rintro ⟨i,j⟩
    rw [mem_fromColumns]
    constructor
    · rintro ⟨_,hi⟩
      exact YoungDiagram.mem_iff_lt_colLen.mpr hi
    · intro hx
      have hp := hle hx
      have ht := nu.up_left_mem (Nat.zero_le i) (le_refl j) hp
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mp ht,YoungDiagram.mem_iff_lt_colLen.mp hx⟩
  have hsum : prefixSum theta.colLen (nu.rowLen 0) = K+r := by
    rw [← fromColumns_card theta.colLen theta.colLen_antitone (nu.rowLen 0),htheta,hcard]
  have hsplit : prefixSum theta.colLen (nu.rowLen 0) =
      prefixSum pi.colLen (nu.rowLen 0)+prefixSum e (nu.rowLen 0) := by
    unfold prefixSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hcols i (Finset.mem_range.mp hi)).2
  have hpi : prefixSum pi.colLen (nu.rowLen 0) = K := by omega
  rw [← hpi]
  apply Finset.sum_le_sum
  intro i hi
  have hic := Finset.mem_range.mp hi
  have hh : theta.colLen i ≤ nu.colLen i := by
    by_contra hn
    have hx : (nu.colLen i,i) ∈ theta :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hv := YoungDiagram.mem_iff_lt_colLen.mp (hle hx)
    omega
  have hp := hcols i hic
  exact Nat.le_min.mpr ⟨hp.1,by omega⟩

private theorem actualGeometry_guards (nu : YoungDiagram) {K r delta : ℕ}
    (hb : BandGeometry nu K r delta) :
    ∃ e, ∃ he : Antitone e, ∃ d t,
      t ≤ nu.rowLen 0 ∧ (∀ c < t, d+e c ≤ nu.colLen c) ∧
      t*d+4 ≤ K ∧ K ≤ prefixSum (capacity nu.colLen d) (nu.rowLen 0) ∧
      prefixSum e (nu.rowLen 0) = r ∧ (∀ c, t ≤ c → e c = 0) ∧
      (containedPath nu.colLen nu.colLen_antitone d K (nu.rowLen 0)).colLen 0 ≤ 4 ∧
      ColumnParity (containedAttachment e he (nu.rowLen 0)).colLen delta ∧
      (containedAttachment e he (nu.rowLen 0)).rowLen 0 ≤ 4 := by
  obtain ⟨d,q,_,hd,_,hq,hclear,e,t,he,hc,_,htq,htm,hroom,hzero,hsize,pi,theta,
    _,hcard,hle,_,hcols⟩ := hb
  have hcapacity := actualGeometry_capacity nu pi theta hsize hcard hle hcols
  have hclear' : t*d+4 ≤ K := by
    have hh := Nat.mul_le_mul_right d htq
    rw [Nat.mul_comm d q] at hclear
    omega
  refine ⟨e,he,d,t,htm,(fun c hh => (hroom c hh).2),hclear',hcapacity,hsize,hzero,
    (actualPath_height_le _ _ _ _ _).trans hd,?_,
    (actualAttachment_width_le he hzero).trans (htq.trans hq)⟩
  rw [actualAttachment_columns he htm hzero]
  exact hc

/-- `BandGeometry` also suffices, with capacity and all guards recovered from
its contained output. -/
theorem paperWitness_band_geometry_pos (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} {nu : YoungDiagram} (target : Tableau n nu)
    (hb : BandGeometry nu (witnessPathSize k) (2*b+delta) delta)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    0 < kronecker z z (transposeTableau target) := by
  obtain ⟨e,he,d,t,htm,hroom,hclear,hcapacity,hsize,hzero,hpi,hc,hE⟩ :=
    actualGeometry_guards nu hb
  exact containedWitness_capacity_kronecker_pos he k b delta hp target htm hroom
    hclear hcapacity hsize hzero hpi hc hE z

/-- The transposed numeric band gives the original target, keeping its sign map
and avoiding a double-transpose tableau replacement. -/
theorem paperWitness_transposed_band_geometry_pos (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu)
    (hb : BandGeometry nu.transpose (witnessPathSize k) (2*b+delta) delta)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    0 < kronecker z z target := by
  obtain ⟨e,he,d,t,htm,hroom,hclear,hcapacity,hsize,hzero,hpi,hc,hE⟩ :=
    actualGeometry_guards nu.transpose hb
  obtain ⟨J,hJ⟩ := containedWitness_target_capacity_canonical_embedding he k b delta hp
    (transposeTableau target) htm hroom hclear hcapacity hsize hzero hpi hc hE z
  exact witnessMixed_transposed_target_pos k b delta hp target z J hJ

/-- Both numeric band orientations give positivity for the same witness square. -/
theorem paperWitness_oriented_band_pos (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} {nu : YoungDiagram} (target : Tableau n nu)
    (hb : BandGeometry nu (witnessPathSize k) (2*b+delta) delta ∨
      BandGeometry nu.transpose (witnessPathSize k) (2*b+delta) delta)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    0 < kronecker z z target + kronecker z z (transposeTableau target) := by
  rcases hb with hb | hb
  · have hh := paperWitness_band_geometry_pos k b delta hp target hb z
    omega
  · have hh := paperWitness_transposed_band_geometry_pos k b delta hp target hb z
    omega

/-- Numeric coverage leaves only the two local-balance Young-prefix cases; all
band cases give oriented positivity. -/
theorem paperWitness_numeric_support_frontier (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu) (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    (∀ t, prefixSum nu.colLen t ≤ youngPrefix (balancePacking k b delta) t) ∨
    (∀ t, prefixSum nu.transpose.colLen t ≤ youngPrefix (balancePacking k b delta) t) ∨
    0 < kronecker z z target + kronecker z z (transposeTableau target) := by
  have hz : (witnessDiagram k b delta hp.staircase_bound).card = n := by
    simpa using (Fintype.card_congr z).symm
  rw [witnessDiagram_card] at hz
  have ht : nu.card = n := by simpa using (Fintype.card_congr target).symm
  have hdiv := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one k)
  have hn : 2*nu.card = k*(k+1)+2*(2*b+delta) := by omega
  have hr : 0 < 2*b+delta := hp.positive_remainder
  have hpar : (2*b+delta)%2=delta := by have hh := hp.parity; omega
  rcases balancePacking_numeric_coverage_ge5 nu hp.staircase_bound hr hp.remainder_bound hpar
    rfl hn with hy | hy | hb | hb
  · exact Or.inl hy
  · exact Or.inr (Or.inl hy)
  · apply Or.inr ∘ Or.inr
    apply paperWitness_oriented_band_pos k b delta hp target _ z
    apply Or.inl
    have hK : witnessPathSize k = 2*k-1 := by
      change 2*((k-2)+1)+1 = 2*k-1
      have hh := hp.staircase_bound
      omega
    rwa [hK]
  · apply Or.inr ∘ Or.inr
    apply paperWitness_oriented_band_pos k b delta hp target _ z
    apply Or.inr
    have hK : witnessPathSize k = 2*k-1 := by
      change 2*((k-2)+1)+1 = 2*k-1
      have hh := hp.staircase_bound
      omega
    rwa [hK]

/-- Positivity for all `k ≥ 5` outside both remaining balance prefix
conditions. It does not assert support in those remaining conditions. -/
theorem paperWitness_outside_numeric_balance_pos (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu) (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    (hcol : ¬ ∀ t, prefixSum nu.colLen t ≤ youngPrefix (balancePacking k b delta) t)
    (hrow : ¬ ∀ t, prefixSum nu.transpose.colLen t ≤ youngPrefix (balancePacking k b delta) t) :
    0 < kronecker z z target + kronecker z z (transposeTableau target) := by
  rcases paperWitness_numeric_support_frontier k b delta hp target z with hh | hh | hh
  · exact False.elim (hcol hh)
  · exact False.elim (hrow hh)
  · exact hh

end
end HSTZ
#print axioms HSTZ.paperWitness_band_feasible_pos

#print axioms HSTZ.paperWitness_band_geometry_pos

#print axioms HSTZ.paperWitness_transposed_band_geometry_pos

#print axioms HSTZ.paperWitness_oriented_band_pos

#print axioms HSTZ.paperWitness_numeric_support_frontier

#print axioms HSTZ.paperWitness_outside_numeric_balance_pos
