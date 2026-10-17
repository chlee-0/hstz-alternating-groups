import HSTZ.FinsuppAction
import HSTZ.IntertwiningCompat
import HSTZ.AlternatingRestriction
import OAI.RepresentationTheory.Saxl.SpechtClassification

import OAI.RepresentationTheory.Saxl.SupportSeparation

/-! Restriction to the alternating group, part (ii), and the alternating-group
conclusion for every guarded witness. Every irreducible `A_n`-representation embeds
in the restriction of some Specht module (via the left-regular representation, its
simple submodules, the Specht classification adapted from OpenAI's `math`
repository, and Maschke); statement (A) and the sign twist then place it inside
`ψ ⊗ ψ`, `ψ = S^λ|A_n`. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped MonoidAlgebra

/-- A nonzero intertwiner out of an irreducible representation is injective. -/
theorem intertwining_injective_of_irreducible {G U V : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ G U} {σ : Representation ℂ G V} [Representation.IsIrreducible ρ]
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) : Function.Injective f := by
  let K : Subrepresentation ρ := ⟨LinearMap.ker f.toLinearMap, fun g v hv => by
    have hv' : f.toLinearMap v = 0 := LinearMap.mem_ker.mp hv
    apply LinearMap.mem_ker.mpr
    change f (ρ g v) = 0
    rw [f.map_action]
    change σ g (f.toLinearMap v) = 0
    rw [hv', map_zero]⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
  · have hk : LinearMap.ker f.toLinearMap = ⊥ := congrArg Subrepresentation.toSubmodule h
    intro u v huv
    have huv' : f.toLinearMap u = f.toLinearMap v := huv
    have h0 : u - v ∈ LinearMap.ker f.toLinearMap := by
      apply LinearMap.mem_ker.mpr
      rw [sub_eq_add_neg, ← neg_one_smul ℂ v, map_add, map_smul, ← huv',
        show f.toLinearMap u + (-1 : ℂ) • f.toLinearMap u = ((1 : ℂ) + -1) • f.toLinearMap u by
          rw [add_smul, one_smul], add_neg_cancel, zero_smul]
    rw [hk] at h0
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp h0)
  · exfalso
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hk : LinearMap.ker f.toLinearMap = ⊤ := congrArg Subrepresentation.toSubmodule h
    have hv : v ∈ LinearMap.ker f.toLinearMap := hk ▸ Submodule.mem_top
    exact LinearMap.mem_ker.mp hv

theorem intertwining_ne_zero_of_injective {G U V : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ G U} {σ : Representation ℂ G V}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f) (w : U) (hw : w ≠ 0) :
    f ≠ 0 := by
  intro h
  apply hw
  apply hf
  have hx := congrArg (fun F : Representation.IntertwiningMap ρ σ => F w) h
  change f.toLinearMap w = 0 at hx
  exact hx.trans f.toLinearMap.map_zero.symm

theorem irreducible_exists_ne_zero {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) [Representation.IsIrreducible σ] : ∃ w : V, w ≠ 0 := by
  by_contra h
  push_neg at h
  apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  show (⊥ : Submodule ℂ V) = ⊤
  ext w
  simp [h w]

/-- Every irreducible representation of `A_n` embeds in the restriction of some
Specht module. -/
theorem alternating_irrep_in_specht {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (alternatingGroup (Fin n)) W) [Representation.IsIrreducible σ] :
    ∃ p : Nat.Partition n, ∃ f : Representation.IntertwiningMap σ
      ((spechtRep (partitionTableau p)).comp (alternatingGroup (Fin n)).subtype),
      Function.Injective f := by
  classical
  let H := alternatingGroup (Fin n)
  letI : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (Equiv.Perm (Fin n))).ne'⟩
  letI : NeZero (Nat.card H : ℂ) := ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'⟩
  obtain ⟨w0, hw0⟩ := irreducible_exists_ne_zero σ
  let F : Equiv.Perm (Fin n) → W := fun x => if hx : x ∈ H then σ ⟨x, hx⟩ w0 else 0
  let ρG := finsuppAction ℂ (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n))
  let bL : (Equiv.Perm (Fin n) →₀ ℂ) →ₗ[ℂ] W := Finsupp.linearCombination ℂ F
  have hF : ∀ (h : H) (x : Equiv.Perm (Fin n)), F (h.val * x) = σ h (F x) := by
    intro h x
    by_cases hx : x ∈ H
    · have hhx : h.val * x ∈ H := H.mul_mem h.2 hx
      show (if hx' : h.val * x ∈ H then σ ⟨h.val * x, hx'⟩ w0 else 0) =
        σ h (if hx' : x ∈ H then σ ⟨x, hx'⟩ w0 else 0)
      rw [dif_pos hhx, dif_pos hx, show (⟨h.val * x, hhx⟩ : H) = h * ⟨x, hx⟩ from rfl, map_mul]
      rfl
    · have hhx : h.val * x ∉ H := fun hm => hx ((H.mul_mem_cancel_left h.2).mp hm)
      show (if hx' : h.val * x ∈ H then σ ⟨h.val * x, hx'⟩ w0 else 0) =
        σ h (if hx' : x ∈ H then σ ⟨x, hx'⟩ w0 else 0)
      rw [dif_neg hhx, dif_neg hx, map_zero]
  have hb : ∀ (h : H) (v : Equiv.Perm (Fin n) →₀ ℂ), bL (ρG h.val v) = σ h (bL v) := by
    intro h v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]
    | single x c =>
      rw [finsuppAction_single, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, map_smul]
      exact congrArg (c • ·) (hF h x)
  have hb1 : bL (Finsupp.single 1 1) = w0 := by
    rw [Finsupp.linearCombination_single, one_smul]
    show (if hx : (1 : Equiv.Perm (Fin n)) ∈ H then σ ⟨1, hx⟩ w0 else 0) = w0
    rw [dif_pos H.one_mem]
    show σ 1 w0 = w0
    rw [map_one]
    rfl
  have htop := IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) ρG.asModule
  have hex : ∃ m : Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) ρG.asModule,
      IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) m ∧ ∃ x ∈ m, bL x ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hw0
    have hmem : (show ρG.asModule from Finsupp.single (1 : Equiv.Perm (Fin n)) (1 : ℂ)) ∈
        sSup {m : Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) ρG.asModule |
          IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) m} := htop ▸ Submodule.mem_top
    rw [sSup_eq_iSup'] at hmem
    rw [← hb1]
    exact Submodule.iSup_induction _ (motive := fun v : ρG.asModule => bL v = 0) hmem
      (fun m v hv => hall m.val m.property v hv) (map_zero bL)
      (fun x y hx hy => by
        change bL (ρG.asModuleEquiv x) = 0 at hx
        change bL (ρG.asModuleEquiv y) = 0 at hy
        change bL (ρG.asModuleEquiv x + ρG.asModuleEquiv y) = 0
        rw [map_add, hx, hy, add_zero])
  obtain ⟨m, hm, x, hxm, hbx⟩ := hex
  let S := Subrepresentation.ofSubmodule' m
  haveI : Representation.IsIrreducible S.toRepresentation := subrep_irreducible_of_simple m
  obtain ⟨p, ⟨e⟩⟩ := irreducible_equiv_specht S.toRepresentation
  let E := e.toIntertwiningMap
  have hE := e.toLinearEquiv.bijective
  let bS : Representation.IntertwiningMap (S.toRepresentation.comp H.subtype) σ :=
    { toLinearMap := bL ∘ₗ S.toSubmodule.subtype
      isIntertwining' := fun h => LinearMap.ext (fun v => hb h v.val) }
  have hsurj : Function.Surjective bS := by
    let R : Subrepresentation σ := ⟨LinearMap.range bS.toLinearMap, fun h y hy => by
      obtain ⟨v, hv⟩ := hy
      refine ⟨(S.toRepresentation.comp H.subtype) h v, ?_⟩
      rw [← hv]
      exact bS.map_action h v⟩
    rcases IsSimpleOrder.eq_bot_or_eq_top R with h | h
    · exfalso
      apply hbx
      have hr : LinearMap.range bS.toLinearMap = ⊥ := congrArg Subrepresentation.toSubmodule h
      have hmem : bS.toLinearMap ⟨x, hxm⟩ ∈ LinearMap.range bS.toLinearMap := ⟨⟨x, hxm⟩, rfl⟩
      rw [hr] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    · exact LinearMap.range_eq_top.mp (congrArg Subrepresentation.toSubmodule h)
  obtain ⟨i, hi, -⟩ := equivariant_injective_lift bS hsurj
    (Representation.IntertwiningMap.id σ) (fun _ _ h => h)
  exact ⟨p, (intertwiningPullback H.subtype E).comp i, hE.1.comp hi⟩

/-- Part (ii): every irreducible `A_n`-representation occurs in `ψ ⊗ ψ`. -/
theorem paperWitness_alternating_square (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (alternatingGroup (Fin n)) W) [Representation.IsIrreducible σ] :
    ∃ f : Representation.IntertwiningMap σ
      (Representation.tprod ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)
        ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)), f ≠ 0 := by
  obtain ⟨p, a, ha⟩ := alternating_irrep_in_specht σ
  obtain ⟨w0, hw0⟩ := irreducible_exists_ne_zero σ
  let t := partitionTableau p
  have hpos := paperWitness_oriented_pos k b delta hp z t
  by_cases h1 : 0 < kronecker z z t
  · obtain ⟨g, hg⟩ := (kronecker_pos_iff z z t).mp h1
    haveI := specht_irreducible t
    have hgi := intertwining_injective_of_irreducible g hg
    let gP : Representation.IntertwiningMap ((spechtRep t).comp (alternatingGroup (Fin n)).subtype)
        (Representation.tprod ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)
          ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)) :=
      { toLinearMap := g.toLinearMap
        isIntertwining' := fun h => LinearMap.ext <| fun x => g.map_action h.val x }
    let Fm := gP.comp a
    exact ⟨Fm, intertwining_ne_zero_of_injective Fm (hgi.comp ha) w0 hw0⟩
  · have h2 : 0 < kronecker z z (transposeTableau t) := by omega
    obtain ⟨g, hg⟩ := (kronecker_pos_iff z z (transposeTableau t)).mp h2
    haveI := specht_irreducible (transposeTableau t)
    have hgi := intertwining_injective_of_irreducible g hg
    let Sg : Representation.IntertwiningMap ((spechtRep t).comp (alternatingGroup (Fin n)).subtype)
        ((spechtRep (transposeTableau t)).comp (alternatingGroup (Fin n)).subtype) :=
      { toLinearMap := (spechtSignMap t).toLinearMap
        isIntertwining' := fun h => LinearMap.ext <| fun x => by
          have he := (spechtSignMap t).map_action h.val x
          have hs : Equiv.Perm.sign h.val = 1 := Equiv.Perm.mem_alternatingGroup.mp h.2
          rw [show (signTwist (spechtRep (transposeTableau t))) h.val =
              spechtRep (transposeTableau t) h.val from by
            change signC h.val • spechtRep (transposeTableau t) h.val = _
            rw [signC_def, hs]
            simp] at he
          exact he }
    have hSg : Function.Injective Sg := (spechtSignMap_bijective t).1
    let gP : Representation.IntertwiningMap
        ((spechtRep (transposeTableau t)).comp (alternatingGroup (Fin n)).subtype)
        (Representation.tprod ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)
          ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)) :=
      { toLinearMap := g.toLinearMap
        isIntertwining' := fun h => LinearMap.ext <| fun x => g.map_action h.val x }
    let Fm := gP.comp (Sg.comp a)
    exact ⟨Fm, intertwining_ne_zero_of_injective Fm (hgi.comp (hSg.comp ha)) w0 hw0⟩

end
end HSTZ
#print axioms HSTZ.intertwining_injective_of_irreducible
#print axioms HSTZ.alternating_irrep_in_specht
#print axioms HSTZ.paperWitness_alternating_square
