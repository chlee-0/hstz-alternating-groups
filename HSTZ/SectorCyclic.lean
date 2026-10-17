import HSTZ.CyclicSpan
import Mathlib.Algebra.DirectSum.Module
import Mathlib.GroupTheory.GroupAction.Basic

/-! Disjoint-sector decomposition behind the HSTZ/OpenAI projection argument.
Covariance, transitive representatives, base support and independent ambient
sectors are explicit hypotheses. This file does not identify the result with an
induced or Specht module. -/
namespace HSTZ
open scoped DirectSum
variable {R G I V : Type*} [CommRing R] [Group G] [MulAction G I]
  [AddCommGroup V] [Module R V]

/-- The cyclic span of the same prescribed vector under the base-point stabilizer. -/
def stabilizerCyclic (rho : Representation R G V) (i0 : I) (v : V) : Submodule R V :=
  cyclicSpan (rho.comp (MulAction.stabilizer G i0).subtype) v

/-- Transport of the stabilizer span to the sector indexed by i. -/
def sectorCyclic (rho : Representation R G V) (i0 : I) (v : V) (s : I → G) (i : I) :
    Submodule R V := (stabilizerCyclic rho i0 v).map (rho (s i))

theorem stabilizerCyclic_le_global (rho : Representation R G V) (i0 : I) (v : V) :
    stabilizerCyclic rho i0 v ≤ cyclicSpan rho v := by
  apply Submodule.span_le.mpr
  rintro _ ⟨h,rfl⟩
  exact orbit_mem_cyclicSpan rho v h.val

theorem sectorCyclic_le_global (rho : Representation R G V) (i0 : I)
    (v : V) (s : I → G) (i : I) : sectorCyclic rho i0 v s i ≤ cyclicSpan rho v := by
  rintro z hz
  obtain ⟨u,hu,rfl⟩ := Submodule.mem_map.mp hz
  exact cyclicSpan_stable rho v (s i) (stabilizerCyclic_le_global rho i0 v hu)

/-- Transitive representatives suffice for the span equality. No independence,
ambient sector decomposition or representative at i0 equal to 1 is required. -/
theorem cyclicSpan_eq_sector_iSup (rho : Representation R G V) (i0 : I)
    (v : V) (s : I → G) (hs : ∀ i, s i • i0 = i) :
    cyclicSpan rho v = ⨆ i, sectorCyclic rho i0 v s i := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    let h : G := (s (g • i0))⁻¹ * g
    have hh : h ∈ MulAction.stabilizer G i0 := by
      apply MulAction.mem_stabilizer_iff.mpr
      change ((s (g • i0))⁻¹ * g) • i0 = i0
      rw [mul_smul]
      simpa only [hs (g • i0)] using (inv_smul_smul (s (g • i0)) i0)
    apply (le_iSup (fun i => sectorCyclic rho i0 v s i) (g • i0))
    apply Submodule.mem_map.mpr
    refine ⟨rho h v,orbit_mem_cyclicSpan
      (rho.comp (MulAction.stabilizer G i0).subtype) v ⟨h,hh⟩,?_⟩
    simp only [h,← Module.End.mul_apply,← map_mul,mul_inv_cancel_left]
  · exact iSup_le (sectorCyclic_le_global rho i0 v s)

/-- Stabilizer generation stays in the base sector by covariance. -/
theorem stabilizerCyclic_le_sector (rho : Representation R G V) (i0 : I) (v : V)
    (P : I → Submodule R V) (hv : v ∈ P i0)
    (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i)) :
    stabilizerCyclic rho i0 v ≤ P i0 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨h,rfl⟩
  change rho h.val v ∈ P i0
  have hmem := hcov h.val i0 (Submodule.mem_map.mpr ⟨v,hv,rfl⟩)
  simpa only [MulAction.mem_stabilizer_iff.mp h.property] using hmem

/-- Each transported stabilizer span lies in its corresponding sector. -/
theorem sectorCyclic_le_sector (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (hs : ∀ i, s i • i0 = i) (P : I → Submodule R V)
    (hv : v ∈ P i0) (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i)) (i : I) :
    sectorCyclic rho i0 v s i ≤ P i := by
  rintro z hz
  obtain ⟨u,hu,rfl⟩ := Submodule.mem_map.mp hz
  have hmem := hcov (s i) i0 (Submodule.mem_map.mpr
    ⟨u,stabilizerCyclic_le_sector rho i0 v P hv hcov hu,rfl⟩)
  simpa only [hs i] using hmem

/-- Independence of the ambient sectors gives independence of the transported spans. -/
theorem sectorCyclic_independent (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (hs : ∀ i, s i • i0 = i) (P : I → Submodule R V)
    (hv : v ∈ P i0) (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i))
    (hP : iSupIndep P) : iSupIndep (sectorCyclic rho i0 v s) :=
  hP.mono (sectorCyclic_le_sector rho i0 v s hs P hv hcov)

/-- Transport from the base stabilizer span to one of its translates. -/
def sectorTransport (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (i : I) : stabilizerCyclic rho i0 v →ₗ[R] sectorCyclic rho i0 v s i :=
  ((rho (s i)).domRestrict (stabilizerCyclic rho i0 v)).codRestrict
    (sectorCyclic rho i0 v s i) (fun z => Submodule.mem_map.mpr ⟨z.val,z.property,rfl⟩)

theorem sectorTransport_bijective (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (i : I) : Function.Bijective (sectorTransport rho i0 v s i) := by
  constructor
  · intro z u h
    apply Subtype.ext
    have heq := congrArg (fun x => rho ((s i)⁻¹) x.val) h
    change rho ((s i)⁻¹) (rho (s i) z.val) = rho ((s i)⁻¹) (rho (s i) u.val) at heq
    simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using heq
  · intro z
    obtain ⟨u,hu,heq⟩ := Submodule.mem_map.mp z.property
    exact ⟨⟨u,hu⟩,Subtype.ext heq⟩

noncomputable def sectorTransportEquiv (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (i : I) : stabilizerCyclic rho i0 v ≃ₗ[R] sectorCyclic rho i0 v s i :=
  LinearEquiv.ofBijective (sectorTransport rho i0 v s i)
    (sectorTransport_bijective rho i0 v s i)

section DirectSum
variable [DecidableEq I]

/-- Summation map from the transported spans into the global cyclic span. -/
def sectorCyclicSum (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (hs : ∀ i, s i • i0 = i) :
    (⨁ i, sectorCyclic rho i0 v s i) →ₗ[R] cyclicSpan rho v :=
  (DirectSum.coeLinearMap (sectorCyclic rho i0 v s)).codRestrict (cyclicSpan rho v) (by
    intro z
    rw [cyclicSpan_eq_sector_iSup rho i0 v s hs,← DirectSum.range_coeLinearMap]
    exact LinearMap.mem_range.mpr ⟨z,rfl⟩)

theorem sectorCyclicSum_surjective (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (hs : ∀ i, s i • i0 = i) :
    Function.Surjective (sectorCyclicSum rho i0 v s hs) := by
  intro z
  let x : V := z.val
  have hz : x ∈ cyclicSpan rho v := z.property
  rw [cyclicSpan_eq_sector_iSup rho i0 v s hs,← DirectSum.range_coeLinearMap] at hz
  obtain ⟨u,hu⟩ := LinearMap.mem_range.mp hz
  exact ⟨u,Subtype.ext hu⟩

/-- Disjoint sector support proves injectivity directly, without a dimension count. -/
theorem sectorCyclicSum_bijective (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (hs : ∀ i, s i • i0 = i) (P : I → Submodule R V)
    (hv : v ∈ P i0) (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i))
    (hP : iSupIndep P) : Function.Bijective (sectorCyclicSum rho i0 v s hs) := by
  refine ⟨?_,sectorCyclicSum_surjective rho i0 v s hs⟩
  have hinj : Function.Injective (DirectSum.coeLinearMap (sectorCyclic rho i0 v s)) :=
    (sectorCyclic_independent rho i0 v s hs P hv hcov hP).dfinsupp_lsum_injective
  intro z u h
  exact hinj (congrArg Subtype.val h)

/-- Linear identification of the global cyclic span with the direct sum of the transported spans. -/
noncomputable def sectorCyclicEquiv (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (hs : ∀ i, s i • i0 = i) (P : I → Submodule R V)
    (hv : v ∈ P i0) (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i))
    (hP : iSupIndep P) : (⨁ i, sectorCyclic rho i0 v s i) ≃ₗ[R] cyclicSpan rho v :=
  LinearEquiv.ofBijective (sectorCyclicSum rho i0 v s hs)
    (sectorCyclicSum_bijective rho i0 v s hs P hv hcov hP)

/-- A direct sum of copies of the base stabilizer span is linearly isomorphic to the
global cyclic span; no dimension or constituent-support hypothesis is needed. -/
noncomputable def stabilizerCopiesEquiv (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (hs : ∀ i, s i • i0 = i) (P : I → Submodule R V)
    (hv : v ∈ P i0) (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i))
    (hP : iSupIndep P) : (⨁ _i : I, stabilizerCyclic rho i0 v) ≃ₗ[R] cyclicSpan rho v :=
  (DirectSum.congrLinearEquiv (sectorTransportEquiv rho i0 v s)).trans
    (sectorCyclicEquiv rho i0 v s hs P hv hcov hP)

/-- A base-span vector in copy i is carried by the representative s i. -/
theorem stabilizerCopiesEquiv_of (rho : Representation R G V) (i0 : I) (v : V)
    (s : I → G) (hs : ∀ i, s i • i0 = i) (P : I → Submodule R V)
    (hv : v ∈ P i0) (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i))
    (hP : iSupIndep P) (i : I) (u : stabilizerCyclic rho i0 v) :
    (stabilizerCopiesEquiv rho i0 v s hs P hv hcov hP
      (DirectSum.of (fun _ : I => stabilizerCyclic rho i0 v) i u)).val = rho (s i) u.val := by
  simp [stabilizerCopiesEquiv,sectorCyclicEquiv,sectorCyclicSum,
    DirectSum.coe_congrLinearEquiv,sectorTransportEquiv,sectorTransport] <;> rfl
end DirectSum

/-- The representative transition lies in the base stabilizer. It is the
coefficient relating group translation and movement between the copies. -/
def sectorTransition (i0 : I) (s : I → G) (hs : ∀ i, s i • i0 = i) (g : G) (i : I) :
    MulAction.stabilizer G i0 := ⟨(s (g • i))⁻¹ * g * s i,by
  apply MulAction.mem_stabilizer_iff.mpr
  simp only [mul_smul,hs i]
  simpa only [hs (g • i)] using (inv_smul_smul (s (g • i)) i0)⟩

/-- Explicit left-translation normalization, before identification with the
library's inverse/right-translation convention for induction. -/
theorem sectorTransition_apply (rho : Representation R G V) (i0 : I)
    (s : I → G) (hs : ∀ i, s i • i0 = i) (g : G) (i : I) (u : V) :
    rho (s (g • i)) (rho (sectorTransition i0 s hs g i).val u) =
      rho g (rho (s i) u) := by
  simp only [sectorTransition,← Module.End.mul_apply,← map_mul]
  simp [mul_assoc]
end HSTZ

#print axioms HSTZ.cyclicSpan_eq_sector_iSup
#print axioms HSTZ.stabilizerCyclic_le_sector
#print axioms HSTZ.sectorCyclic_independent
#print axioms HSTZ.sectorCyclicSum_surjective
#print axioms HSTZ.sectorCyclicSum_bijective
#print axioms HSTZ.sectorCyclicEquiv
#print axioms HSTZ.sectorTransport_bijective
#print axioms HSTZ.stabilizerCopiesEquiv
#print axioms HSTZ.stabilizerCopiesEquiv_of
#print axioms HSTZ.sectorTransition_apply
