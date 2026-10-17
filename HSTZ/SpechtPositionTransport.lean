import HSTZ.IntertwiningCompat
import HSTZ.YoungDiagramCompat
import HSTZ.WitnessBalancePieriTableaux
import HSTZ.WitnessBalancePieriGroups

/-! Public Specht transport along position equivalences, one-row shapes, and the
Frobenius step "injective into an induced module ⇒ nonzero restricted map".
`positionGenerator`, `positionImage`, `positionSpechtMap` and
`induced_restricted_nonzero` are public copies of the private `target_generator`,
`target_image`, `targetSpechtMap` (WitnessBalancePieriTableaux) and
`restricted_of_induced_injection` (WitnessBalancePieriRestricted). They are built on
APIs from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

theorem positionGenerator {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    positionRelabel E.symm (polytabloid t)=polytabloid (E.trans t) := by
  funext w
  rw [polytabloid_eq_altWord,polytabloid_eq_altWord]
  change altWord (fiberGroup (fun i => (t i).val.2)) (rowWord t) (w ∘ E.symm)=
    altWord (fiberGroup ((fun i => (t i).val.2) ∘ E)) (rowWord t ∘ E) w
  exact altWord_fiber_relabel E _ _ w

theorem positionImage {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    (spechtSub t).toSubmodule.map (positionRelabelIntertwiner E.symm).toLinearMap=
      (spechtSub (E.trans t)).toSubmodule := by
  change (cyclicSpan (wordRep n (nu.colLen 0)) (polytabloid t)).map
    (positionRelabelIntertwiner E.symm).toLinearMap=
    cyclicSpan (wordRep m (nu.colLen 0)) (polytabloid (E.trans t))
  rw [cyclicSpan_image]
  change cyclicSpan ((wordRep m (nu.colLen 0)).comp (positionPermHom E.symm))
    (positionRelabel E.symm (polytabloid t))=_
  rw [positionGenerator,cyclicSpan_comp_surjective _ _
    (positionPermHom_bijective E.symm).2]

/-- Specht module of `t` mapped into the relabelled Specht module, as an intertwiner. -/
def positionSpechtMap {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    Representation.IntertwiningMap (spechtRep t)
      ((spechtRep (E.trans t)).comp (positionPermHom E.symm)) where
  toLinearMap := ((positionRelabelIntertwiner E.symm).toLinearMap.domRestrict
    (spechtSub t).toSubmodule).codRestrict (spechtSub (E.trans t)).toSubmodule (fun x => by
      rw [← positionImage E t]
      exact Submodule.mem_map.mpr ⟨x.val,x.property,rfl⟩)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (positionRelabelIntertwiner E.symm).map_action g x.val

theorem positionSpechtMap_injective {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    Function.Injective (positionSpechtMap E t) := by
  intro x y h
  apply Subtype.ext
  exact (positionRelabel E.symm).injective (congrArg Subtype.val h)

/-- Pull an intertwiner back along a group hom. -/
def intertwiningPullback {G K U V : Type*} [Group G] [Group K]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ G U} {sigma : Representation ℂ G V} (phi : K →* G)
    (J : Representation.IntertwiningMap rho sigma) :
    Representation.IntertwiningMap (rho.comp phi) (sigma.comp phi) where
  toLinearMap := J.toLinearMap
  isIntertwining' g := LinearMap.ext fun x => J.map_action (phi g) x

/-- Local support transported along a position equivalence: if every tableau of
shape `nu` on `Fin n` embeds in `sigma`, then every tableau of that shape on
`Fin m` embeds in `sigma` pulled back along `positionPermHom E`. -/
theorem specht_transport_injective {m n : ℕ} {nu : YoungDiagram} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (E : Fin m ≃ Fin n)
    (sigma : Representation ℂ (Equiv.Perm (Fin n)) V) (t : Tableau m nu)
    (h : ∀ t' : Tableau n nu, ∃ J : Representation.IntertwiningMap (spechtRep t') sigma,
      Function.Injective J) :
    ∃ J : Representation.IntertwiningMap (spechtRep t) (sigma.comp (positionPermHom E)),
      Function.Injective J := by
  obtain ⟨J,hJ⟩ := h (E.symm.trans t)
  let P := intertwiningPullback (positionPermHom E) J
  exact ⟨P.comp (positionSpechtMap E.symm t),hJ.comp (positionSpechtMap_injective E.symm t)⟩

/-- Shape equality transfer for "every tableau embeds" statements. -/
theorem specht_shape_transfer {n : ℕ} {nu nu' : YoungDiagram} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (sigma : Representation ℂ (Equiv.Perm (Fin n)) V)
    (hnu : nu=nu')
    (h : ∀ t' : Tableau n nu', ∃ J : Representation.IntertwiningMap (spechtRep t') sigma,
      Function.Injective J) :
    ∀ t : Tableau n nu, ∃ J : Representation.IntertwiningMap (spechtRep t) sigma,
      Function.Injective J := by
  subst hnu
  exact h

/-- A Young diagram with at most one row is the one-row diagram of its size. -/
theorem eq_oneRowDiagram_of_colLen {mu : YoungDiagram} (h : mu.colLen 0≤1) :
    mu=oneRowDiagram mu.card := by
  have h1 : mu=oneRowDiagram (mu.rowLen 0) := by
    ext ⟨i,j⟩
    show (i,j)∈mu ↔ (i,j)∈oneRowDiagram (mu.rowLen 0)
    rw [mem_oneRowDiagram]
    constructor
    · intro hij
      have hi : i < mu.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hij
      have hle : mu.colLen j ≤ mu.colLen 0 := mu.colLen_anti 0 j (Nat.zero_le j)
      have hi0 : i=0 := by omega
      subst hi0
      exact ⟨rfl,YoungDiagram.mem_iff_lt_rowLen.mp hij⟩
    · rintro ⟨rfl,hj⟩
      exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
  have h2 := congrArg YoungDiagram.card h1
  rw [oneRowDiagram_card] at h2
  rw [h2]
  exact h1

theorem specht_nontrivial {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Nontrivial (Specht t) :=
  ⟨⟨⟨polytabloid t,mem_cyclic _ _⟩,0,fun he =>
    polytabloid_ne_zero t (congrArg Subtype.val he)⟩⟩

/-- Frobenius step: an injection into an induced module gives a nonzero map from
the restriction to the inducing source. -/
theorem induced_restricted_nonzero
    {H G U X : Type*} [Group H] [Finite H] [Group G] [Finite G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    (phi : H →* G) (sigma : Representation ℂ H U) (rho : Representation ℂ G X)
    (J : Representation.IntertwiningMap rho (Representation.ind phi sigma))
    (hJ : Function.Injective J) :
    ∃ b : Representation.IntertwiningMap (rho.comp phi) sigma, b≠0 := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card G).ne'⟩
  letI : NeZero (Nat.card H : ℂ) := ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card H).ne'⟩
  obtain ⟨p,hp⟩ := equivariant_retraction J hJ
  let a : Representation.IntertwiningMap sigma (rho.comp phi) :=
    { toLinearMap := p.toLinearMap.comp (Representation.IndV.mk phi sigma 1)
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro u
        change p.toLinearMap (Representation.IndV.mk phi sigma 1 (sigma h u))=
          rho (phi h) (p.toLinearMap (Representation.IndV.mk phi sigma 1 u))
        have he := p.map_action (phi h) (Representation.IndV.mk phi sigma 1 u)
        change p.toLinearMap (Representation.ind phi sigma (phi h)
          (Representation.IndV.mk phi sigma 1 u))=
          rho (phi h) (p.toLinearMap (Representation.IndV.mk phi sigma 1 u)) at he
        rw [Representation.ind_mk] at he
        exact (congrArg p.toLinearMap (by
          simpa using (ind_mk_inv_mul phi sigma h 1 u).symm)).trans he }
  have ha : a≠0 := by
    intro hz
    have hzero (u : U) : p.toLinearMap (Representation.IndV.mk phi sigma 1 u)=0 := by
      exact congrArg (fun f => f u) hz
    have hmk (g : G) (u : U) : p.toLinearMap (Representation.IndV.mk phi sigma g u)=0 := by
      have he := p.map_action g⁻¹ (Representation.IndV.mk phi sigma 1 u)
      change p.toLinearMap (Representation.ind phi sigma g⁻¹
        (Representation.IndV.mk phi sigma 1 u))=
        rho g⁻¹ (p.toLinearMap (Representation.IndV.mk phi sigma 1 u)) at he
      rw [Representation.ind_mk] at he
      simpa only [inv_inv,one_mul,hzero,map_zero] using he
    have hpzero : p.toLinearMap=0 := by
      apply Representation.IndV.hom_ext
      intro g
      ext u
      exact hmk g u
    obtain ⟨x,hx⟩ := exists_ne (0 : X)
    have he := hp x
    change p.toLinearMap (J x)=x at he
    rw [hpzero,LinearMap.zero_apply] at he
    exact hx he.symm
  let S : Subrepresentation (rho.comp phi) :=
    { toSubmodule := a.toLinearMap.range
      apply_mem_toSubmodule := by
        intro h x hx
        obtain ⟨u,rfl⟩ := hx
        exact ⟨sigma h u,a.map_action h u⟩ }
  let q : Representation.IntertwiningMap sigma S.toRepresentation :=
    { toLinearMap := a.toLinearMap.codRestrict S.toSubmodule (fun u => ⟨u,rfl⟩)
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (a.map_action h u) }
  have hq : Function.Surjective q := by
    rintro ⟨x,u,rfl⟩
    exact ⟨u,rfl⟩
  obtain ⟨s,hs,hqs⟩ := equivariant_injective_lift q hq
    (Representation.IntertwiningMap.id S.toRepresentation) (fun _ _ h => h)
  let i : Representation.IntertwiningMap S.toRepresentation (rho.comp phi) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  have hi : Function.Injective i := fun x y h => Subtype.ext h
  obtain ⟨r,hr⟩ := equivariant_retraction i hi
  refine ⟨s.comp r,?_⟩
  intro hz
  have hpoint : ∃ u, a u≠0 := by
    by_contra hn
    push_neg at hn
    apply ha
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    exact hn u
  obtain ⟨u,hu⟩ := hpoint
  let v : S.toSubmodule := ⟨a u,⟨u,rfl⟩⟩
  have he := congrArg (fun f => f (i v)) hz
  change s (r (i v))=0 at he
  rw [hr] at he
  have he' : s.toLinearMap v=s.toLinearMap 0 :=
    he.trans s.toLinearMap.map_zero.symm
  have hv : v=0 := hs he'
  exact hu (congrArg Subtype.val hv)

end
end HSTZ
#print axioms HSTZ.specht_transport_injective
#print axioms HSTZ.specht_shape_transfer
#print axioms HSTZ.eq_oneRowDiagram_of_colLen
#print axioms HSTZ.induced_restricted_nonzero
