import HSTZ.SectorCyclic
import HSTZ.ProjectionLift
import Mathlib.RepresentationTheory.Induced

/-! Ordinary induction and cyclic sector spaces in the HSTZ/OpenAI projection argument.
The library acts by inverse/right translation; our map sends [h tensor u] to
rho(h^-1)j(u). -/
namespace HSTZ
open TensorProduct Finsupp
open scoped DirectSum

section General
variable {R H G U V : Type*} [CommRing R] [Group H] [Group G]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  (phi : H →* G) (tau : Representation R H U) (rho : Representation R G V)
  (j : Representation.IntertwiningMap tau (rho.comp phi))

/-- The induced linear map, descending through the coinvariant quotient. -/
noncomputable def inducedLinearMap : Representation.IndV phi tau →ₗ[R] V :=
  Representation.Coinvariants.lift _ (TensorProduct.lift <|
    (Finsupp.linearCombination R (fun h => (rho h⁻¹).comp j.toLinearMap)).comp
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap) (fun h => by
      ext g u
      have hj := Representation.IntertwiningMap.isIntertwining _ _ j h u
      simp_all [← Module.End.mul_apply,← map_mul])

@[simp] theorem inducedLinearMap_mk (h : G) (u : U) :
    inducedLinearMap phi tau rho j (Representation.IndV.mk phi tau h u) = rho h⁻¹ (j u) := by
  simp [inducedLinearMap,Representation.IndV.mk]

/-- The descending map is equivariant for the library convention. -/
noncomputable def inducedIntertwiner :
    Representation.IntertwiningMap (Representation.ind phi tau) rho where
  toLinearMap := inducedLinearMap phi tau rho j
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    have heq : (inducedLinearMap phi tau rho j).comp (Representation.ind phi tau g) =
        (rho g).comp (inducedLinearMap phi tau rho j) := by
      apply Representation.IndV.hom_ext
      intro h
      ext u
      change inducedLinearMap phi tau rho j
        (Representation.ind phi tau g (Representation.IndV.mk phi tau h u)) =
        rho g (inducedLinearMap phi tau rho j (Representation.IndV.mk phi tau h u))
      rw [Representation.ind_mk,inducedLinearMap_mk,inducedLinearMap_mk]
      simp [mul_inv_rev,← Module.End.mul_apply,← map_mul]
    exact DFunLike.congr_fun heq z

/-- The subgroup relation used to normalize induced generators. -/
theorem ind_mk_inv_mul (h : H) (g : G) (u : U) :
    Representation.IndV.mk phi tau ((phi h)⁻¹ * g) u =
      Representation.IndV.mk phi tau g (tau h u) := by
  simpa [Representation.IndV.mk,Representation.IndV,Representation.ofMulAction_single]
    using Representation.Coinvariants.mk_inv_tmul
      ((Representation.leftRegular R G).comp phi) tau (MonoidAlgebra.single g 1) u h
end General

section Sectors
variable {R G I V : Type*} [CommRing R] [Group G] [MulAction G I]
  [AddCommGroup V] [Module R V]
  (rho : Representation R G V) (i0 : I) (v : V)

/-- The bundled stabilizer cyclic representation. -/
abbrev stabilizerRepresentation : Representation R (MulAction.stabilizer G i0)
    (stabilizerCyclic rho i0 v) :=
  (cyclicSubrepresentation (rho.comp (MulAction.stabilizer G i0).subtype) v).toRepresentation

/-- Base inclusion into the restricted global cyclic representation. -/
def stabilizerIntoGlobal : Representation.IntertwiningMap (stabilizerRepresentation rho i0 v)
    ((cyclicSubrepresentation rho v).toRepresentation.comp (MulAction.stabilizer G i0).subtype) where
  toLinearMap := (stabilizerCyclic rho i0 v).subtype.codRestrict (cyclicSpan rho v)
    (fun u => stabilizerCyclic_le_global rho i0 v u.property)
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

/-- Ordinary induction mapped into the global prescribed-vector span. -/
noncomputable def sectorInductionMap : Representation.IntertwiningMap
    (Representation.ind (MulAction.stabilizer G i0).subtype (stabilizerRepresentation rho i0 v))
    (cyclicSubrepresentation rho v).toRepresentation :=
  inducedIntertwiner (MulAction.stabilizer G i0).subtype (stabilizerRepresentation rho i0 v)
    (cyclicSubrepresentation rho v).toRepresentation (stabilizerIntoGlobal rho i0 v)

@[simp] theorem sectorInductionMap_mk (h : G) (u : stabilizerCyclic rho i0 v) :
    (sectorInductionMap rho i0 v (Representation.IndV.mk
      (MulAction.stabilizer G i0).subtype (stabilizerRepresentation rho i0 v) h u)).val =
        rho h⁻¹ u.val := by
  exact congrArg Subtype.val (inducedLinearMap_mk (MulAction.stabilizer G i0).subtype
    (stabilizerRepresentation rho i0 v) (cyclicSubrepresentation rho v).toRepresentation
    (stabilizerIntoGlobal rho i0 v) h u)

variable [DecidableEq I]

/-- Representatives define induced generators for the base-span copies. -/
noncomputable def copiesToInduced (s : I → G) :
    (⨁ _i : I, stabilizerCyclic rho i0 v) →ₗ[R]
      Representation.IndV (MulAction.stabilizer G i0).subtype (stabilizerRepresentation rho i0 v) :=
  DirectSum.toModule R I _ (fun i => Representation.IndV.mk
    (MulAction.stabilizer G i0).subtype (stabilizerRepresentation rho i0 v) (s i)⁻¹)

@[simp] theorem copiesToInduced_of (s : I → G) (i : I) (u : stabilizerCyclic rho i0 v) :
    copiesToInduced rho i0 v s (DirectSum.of (fun _ : I => stabilizerCyclic rho i0 v) i u) =
      Representation.IndV.mk (MulAction.stabilizer G i0).subtype
        (stabilizerRepresentation rho i0 v) (s i)⁻¹ u := by
  exact DirectSum.toModule_lof R (M := fun _ : I => stabilizerCyclic rho i0 v)
    (φ := fun i => Representation.IndV.mk (MulAction.stabilizer G i0).subtype
      (stabilizerRepresentation rho i0 v) (s i)⁻¹) i u

/-- Every induced generator comes from one representative copy. -/
theorem induced_mk_mem_copies_range (s : I → G) (hs : ∀ i, s i • i0 = i)
    (h : G) (u : stabilizerCyclic rho i0 v) :
    Representation.IndV.mk (MulAction.stabilizer G i0).subtype
      (stabilizerRepresentation rho i0 v) h u ∈ (copiesToInduced rho i0 v s).range := by
  let i := h⁻¹ • i0
  let m : MulAction.stabilizer G i0 := ⟨(s i)⁻¹ * h⁻¹,by
    apply MulAction.mem_stabilizer_iff.mpr
    change ((s i)⁻¹ * h⁻¹) • i0 = i0
    rw [mul_smul]
    simpa only [hs i] using (inv_smul_smul (s i) i0)⟩
  have hrel := ind_mk_inv_mul (MulAction.stabilizer G i0).subtype
    (stabilizerRepresentation rho i0 v) m (s i)⁻¹ u
  have hrel' : Representation.IndV.mk (MulAction.stabilizer G i0).subtype
      (stabilizerRepresentation rho i0 v) h u =
      Representation.IndV.mk (MulAction.stabilizer G i0).subtype
        (stabilizerRepresentation rho i0 v) (s i)⁻¹ (stabilizerRepresentation rho i0 v m u) := by
    simpa [m,mul_assoc] using hrel
  apply LinearMap.mem_range.mpr
  refine ⟨DirectSum.of (fun _ : I => stabilizerCyclic rho i0 v) i
    (stabilizerRepresentation rho i0 v m u),?_⟩
  rw [copiesToInduced_of]
  exact hrel'.symm

/-- Representative copies span the whole coinvariant induction, without a
finite dimension/index assumption. -/
theorem copiesToInduced_surjective (s : I → G) (hs : ∀ i, s i • i0 = i) :
    Function.Surjective (copiesToInduced rho i0 v s) := by
  let tau := stabilizerRepresentation rho i0 v
  let phi := (MulAction.stabilizer G i0).subtype
  let mk : (MonoidAlgebra R G ⊗[R] stabilizerCyclic rho i0 v) →ₗ[R] Representation.IndV phi tau :=
    Representation.Coinvariants.mk _
  let Q := (copiesToInduced rho i0 v s).range
  have hpure : ∀ (f : MonoidAlgebra R G) (u : stabilizerCyclic rho i0 v), mk (f ⊗ₜ[R] u) ∈ Q := by
    intro f u
    induction f using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f f' hf hf' => simpa [add_tmul] using Q.add_mem hf hf'
    | single h r =>
      have hr : MonoidAlgebra.single h r = r • MonoidAlgebra.single h (1 : R) := by simp
      rw [hr,← smul_tmul',map_smul]
      exact Q.smul_mem r (induced_mk_mem_copies_range rho i0 v s hs h u)
  intro z
  obtain ⟨t,rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  apply LinearMap.mem_range.mp
  change mk t ∈ Q
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f u => exact hpure f u
  | add t t' ht ht' => simpa using Q.add_mem ht ht'

/-- The induced map on representative copies is the sector sum equivalence.
This compares maps, not dimensions or constituents. -/
theorem sectorInductionMap_comp_copies (s : I → G) (hs : ∀ i, s i • i0 = i)
    (P : I → Submodule R V) (hv : v ∈ P i0)
    (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i)) (hP : iSupIndep P) :
    (sectorInductionMap rho i0 v).toLinearMap.comp (copiesToInduced rho i0 v s) =
      (stabilizerCopiesEquiv rho i0 v s hs P hv hcov hP).toLinearMap := by
  ext i u
  change (sectorInductionMap rho i0 v (copiesToInduced rho i0 v s
      (DirectSum.of (fun _ : I => stabilizerCyclic rho i0 v) i u))).val =
    (stabilizerCopiesEquiv rho i0 v s hs P hv hcov hP
      (DirectSum.of (fun _ : I => stabilizerCyclic rho i0 v) i u)).val
  rw [copiesToInduced_of,sectorInductionMap_mk,inv_inv,stabilizerCopiesEquiv_of]

/-- Equivariant identification of induction with the prescribed cyclic span when the
sectors are independent and covariant. -/
theorem sectorInductionMap_bijective (s : I → G) (hs : ∀ i, s i • i0 = i)
    (P : I → Submodule R V) (hv : v ∈ P i0)
    (hcov : ∀ g i, (P i).map (rho g) ≤ P (g • i)) (hP : iSupIndep P) :
    Function.Bijective (sectorInductionMap rho i0 v) := by
  let e := stabilizerCopiesEquiv rho i0 v s hs P hv hcov hP
  have hc : ∀ x, sectorInductionMap rho i0 v (copiesToInduced rho i0 v s x) = e x :=
    DFunLike.congr_fun (sectorInductionMap_comp_copies rho i0 v s hs P hv hcov hP)
  constructor
  · intro z u h
    obtain ⟨x,rfl⟩ := copiesToInduced_surjective rho i0 v s hs z
    obtain ⟨y,rfl⟩ := copiesToInduced_surjective rho i0 v s hs u
    exact congrArg (copiesToInduced rho i0 v s) (e.injective (by
      apply Subtype.ext
      simpa only [hc] using congrArg Subtype.val h))
  · intro z
    obtain ⟨x,rfl⟩ := e.surjective z
    exact ⟨copiesToInduced rho i0 v s x,hc x⟩
end Sectors

section Lift
variable {K G I U V W : Type*} [Field K] [Group G] [Finite G]
  [NeZero (Nat.card G : K)] [MulAction G I] [DecidableEq I]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- An embedding into the induced sector module lifts through the equivariant
projection into the original prescribed-vector cyclic module.
The input embedding and the independent-sector hypotheses are explicit. -/
theorem sectorInduction_embedding_lift
    {rho : Representation K G V} {sigma : Representation K G W} {tau : Representation K G U}
    (phi : Representation.IntertwiningMap rho sigma) (v : V) (i0 : I)
    (s : I → G) (hs : ∀ i, s i • i0 = i) (P : I → Submodule K W)
    (hv : phi v ∈ P i0) (hcov : ∀ g i, (P i).map (sigma g) ≤ P (g • i))
    (hP : iSupIndep P)
    (j : Representation.IntertwiningMap tau
      (Representation.ind (MulAction.stabilizer G i0).subtype
        (stabilizerRepresentation sigma i0 (phi v)))) (hj : Function.Injective j) :
    ∃ i : Representation.IntertwiningMap tau (cyclicSubrepresentation rho v).toRepresentation,
      Function.Injective i ∧ ∀ u, cyclicImageMap phi v (i u) =
        sectorInductionMap sigma i0 (phi v) (j u) := by
  let j' := (sectorInductionMap sigma i0 (phi v)).comp j
  have hj' : Function.Injective j' :=
    (sectorInductionMap_bijective sigma i0 (phi v) s hs P hv hcov hP).injective.comp hj
  exact cyclicImage_embedding_lift phi v j' hj'
end Lift
end HSTZ

#print axioms HSTZ.inducedLinearMap_mk
#print axioms HSTZ.ind_mk_inv_mul
#print axioms HSTZ.sectorInductionMap_mk
#print axioms HSTZ.induced_mk_mem_copies_range
#print axioms HSTZ.copiesToInduced_surjective
#print axioms HSTZ.sectorInductionMap_comp_copies
#print axioms HSTZ.sectorInductionMap_bijective
#print axioms HSTZ.inducedIntertwiner
#print axioms HSTZ.sectorInduction_embedding_lift
