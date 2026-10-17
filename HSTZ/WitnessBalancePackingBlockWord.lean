import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePackingBlockStrips
import HSTZ.ContainedSpechtSupport
import HSTZ.OneRowInduction
import HSTZ.OneRowTableau
import OAI.RepresentationTheory.Saxl.SignEquivalence

/-! The original block strip colors constrain a complement word source. Uses the
positive strip restriction, Maschke splitting, multiplicity evaluation and
`orbitAverage` interfaces, building on OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No local constituent height or physical K alignment is inferred here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

private def colorStab {d r : ℕ} (a : Fin d → Fin r) : Subgroup (Equiv.Perm (Fin d)) where
  carrier := {h | a ∘ h=a}
  one_mem' := rfl
  mul_mem' := by
    intro h g hh hg
    funext i
    exact (congrFun hh (g i)).trans (congrFun hg i)
  inv_mem' := by
    intro h hh
    funext i
    have he := congrFun hh (h⁻¹ i)
    simpa using he.symm

private theorem chain_fixed_core {bs : List ℕ} {nu mu : YoungDiagram}
    (hs : SizedStripChain bs nu mu) {a n d : ℕ}
    (s : Tableau a nu) (t : Tableau n mu) (e : Fin n ≃ Fin a ⊕ Fin d) :
    ∃ (w : Fin d → Fin bs.length)
      (f : coreMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e))),
      f≠0 ∧ ∀ h : Equiv.Perm (Fin d), w ∘ h=w →
        complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e)) h f=f := by
  obtain ⟨t',hi⟩ := exists_block_tableau s t hs.le e
  obtain ⟨c,F,hF,hbound,hzero,hcount,hcov⟩ := stripChain_restriction_any hs s t'
  have hleft (i : Fin a) : c (e.symm (.inl i))=0 := by
    apply (hzero _).mpr
    exact ⟨i,by rw [hi]; rfl⟩
  have hpos (j : Fin d) : 0<c (e.symm (.inr j)) := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨i,he⟩ := (hzero _).mp hz
    rw [hi] at he
    have ht : (Sum.inl i : Fin a ⊕ Fin d) = Sum.inr j := e.symm.injective he
    cases ht
  let w : Fin d → Fin bs.length := fun j =>
    ⟨c (e.symm (.inr j))-1, by have hp := hpos j; have hb := hbound (e.symm (.inr j)); omega⟩
  let L := colorStab w
  let phi : (Equiv.Perm (Fin a) × L) →* Equiv.Perm (Fin n) :=
    (sumPermHom e).comp ((MonoidHom.fst _ _).prod
      (L.subtype.comp (MonoidHom.snd _ _)))
  have hcolors (g : Equiv.Perm (Fin a)) (h : L) : ∀ i, c (phi (g,h) i)=c i := by
    intro i
    obtain ⟨v,rfl⟩ := e.symm.surjective i
    cases v with
    | inl j =>
      have he : phi (g,h) (e.symm (.inl j))=e.symm (.inl (g j)) := by
        simp [phi,sumPermHom,sumPerm,Equiv.permCongr_apply]
      rw [he,hleft,hleft]
    | inr j =>
      have he : phi (g,h) (e.symm (.inr j))=e.symm (.inr ((h : Equiv.Perm (Fin d)) j)) := by
        simp [phi,sumPermHom,sumPerm,Equiv.permCongr_apply]
      rw [he]
      have hw := congrArg Fin.val (congrFun h.property j)
      change c (e.symm (.inr ((h : Equiv.Perm (Fin d)) j)))-1=c (e.symm (.inr j))-1 at hw
      have hp := hpos j
      have hp' := hpos ((h : Equiv.Perm (Fin d)) j)
      omega
  have hcore (g : Equiv.Perm (Fin a)) (h : L) :
      ∀ i, phi (g,h) (tableauInclusion s t' hs.le i)=tableauInclusion s t' hs.le (g i) := by
    rw [hi]
    intro i
    exact sumPerm_left e g h.val i
  let rho := (spechtRep s).comp (MonoidHom.fst (Equiv.Perm (Fin a)) L)
  let tau := (spechtRep t').comp phi
  let P : Representation.IntertwiningMap tau rho :=
    { toLinearMap := F
      isIntertwining' := fun gh => LinearMap.ext <| fun x => hcov (phi gh) gh.1 (hcolors gh.1 gh.2) (hcore gh.1 gh.2) x }
  letI : NeZero (Nat.card (Equiv.Perm (Fin a) × L) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card (Equiv.Perm (Fin a) × L)).ne'⟩
  obtain ⟨J,hJ,hPJ⟩ := equivariant_injective_lift P hF
    (Representation.IntertwiningMap.id rho) (fun _ _ he => he)
  let f0 : coreMultiplicity (spechtRep s) ((spechtRep t').comp (sumPermHom e)) :=
    { toLinearMap := J.toLinearMap
      isIntertwining' := fun g => LinearMap.ext <| fun x => J.map_action (g,1) x }
  have hf0 : f0≠0 := by
    intro hz
    let p : Specht s := ⟨polytabloid s,mem_cyclic _ _⟩
    have he : J p=0 := congrArg (fun A : coreMultiplicity (spechtRep s)
      ((spechtRep t').comp (sumPermHom e)) => A p) hz
    have hp : p=0 := hJ (he.trans (map_zero J.toLinearMap).symm)
    exact polytabloid_ne_zero s (congrArg Subtype.val hp)
  let eta := complementMultiplicity (spechtRep s) ((spechtRep t').comp (sumPermHom e))
  have hfix0 (h : Equiv.Perm (Fin d)) (hh : w ∘ h=w) : eta h f0=f0 := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have he := J.map_action (1,(⟨h,hh⟩ : L)) x
    change J (spechtRep s 1 x)=spechtRep t' (sumPermHom e (1,h)) (J x) at he
    rw [map_one,Module.End.one_apply] at he
    exact he.symm
  let f : coreMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e)) :=
    { toLinearMap := (tableauSpechtMap t' t).toLinearMap.comp f0.toLinearMap
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        change tableauSpechtMap t' t (f0 (spechtRep s g x))=
          spechtRep t (sumPermHom e (g,1)) (tableauSpechtMap t' t (f0 x))
        have he : f0 (spechtRep s g x)=spechtRep t' (sumPermHom e (g,1)) (f0 x) :=
          f0.map_action g x
        exact (congrArg (tableauSpechtMap t' t) he).trans
          ((tableauSpechtMap t' t).map_action _ _) }
  have hf : f≠0 := by
    intro hz
    apply hf0
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply (tableauSpechtMap_bijective t' t).1
    exact congrArg (fun A : coreMultiplicity (spechtRep s)
      ((spechtRep t).comp (sumPermHom e)) => A x) hz
  refine ⟨w,f,hf,?_⟩
  intro h hh
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change spechtRep t (sumPermHom e (1,h)) (tableauSpechtMap t' t (f0 x))=
    tableauSpechtMap t' t (f0 x)
  have he0 : spechtRep t' (sumPermHom e (1,h)) (f0 x)=f0 x :=
    congrArg (fun A : coreMultiplicity (spechtRep s)
      ((spechtRep t').comp (sumPermHom e)) => A x) (hfix0 h hh)
  exact ((tableauSpechtMap t' t).map_action _ _).symm.trans
    (congrArg (tableauSpechtMap t' t) he0)

private theorem fixed_core_word {a n d r : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (e : Fin n ≃ Fin a ⊕ Fin d)
    (w : Fin d → Fin r)
    (f : coreMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e)))
    (hf : f≠0)
    (hfix : ∀ h : Equiv.Perm (Fin d), w ∘ h=w →
      complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e)) h f=f) :
    ∃ O : Representation.IntertwiningMap (wordRep d r)
      (complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e))),
      O (Pi.single w (1 : ℂ))≠0 := by
  let eta := complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e))
  let O := orbitAverage eta w f
  refine ⟨O,?_⟩
  rw [show O (Pi.single w (1 : ℂ))=_ from orbitAverage_base eta w f hfix]
  apply smul_ne_zero _ hf
  apply Nat.cast_ne_zero.mpr
  exact Finset.card_ne_zero.mpr ⟨1,by simp⟩

private def wordBoundaryCut (nu mu : YoungDiagram) (d : ℕ) (hc : mu.card=nu.card+d) :
    Fin mu.card ≃ Fin nu.card ⊕ Fin d := (finCongr hc).trans finSumFinEquiv.symm

/-- Each coherent original block has a nonzero color-word orbit map
into the full complement multiplicity representation of its adjacent boundary.
The source alphabet is the original strip count, not a new height hypothesis. -/
theorem paperWitness_balance_boundary_word_source (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ D : Fin ((witnessBalancePackingBlocks k delta).length+1) → YoungDiagram,
      D 0=⊥ ∧ D (Fin.last (witnessBalancePackingBlocks k delta).length)=mu ∧
      ∀ j : Fin (witnessBalancePackingBlocks k delta).length,
        SizedStripChain
          (witnessBalancePackingParts hp.staircase_bound z (witnessBalancePackingBlocks k delta)[j.val])
          (D j.castSucc) (D j.succ) ∧
        ∃ hc : (D j.succ).card=(D j.castSucc).card+
          Fintype.card {i : Fin n // witnessBalancePackingPositionKind hp.staircase_bound z i=
            (witnessBalancePackingBlocks k delta)[j.val]},
        ∃ (w : Fin (Fintype.card {i : Fin n // witnessBalancePackingPositionKind hp.staircase_bound z i=
          (witnessBalancePackingBlocks k delta)[j.val]}) →
            Fin (witnessBalancePackingParts hp.staircase_bound z
              (witnessBalancePackingBlocks k delta)[j.val]).length),
        ∃ O : Representation.IntertwiningMap
          (wordRep (Fintype.card {i : Fin n // witnessBalancePackingPositionKind hp.staircase_bound z i=
            (witnessBalancePackingBlocks k delta)[j.val]})
            (witnessBalancePackingParts hp.staircase_bound z
              (witnessBalancePackingBlocks k delta)[j.val]).length)
          (complementMultiplicity (spechtRep (shapeTableau (D j.castSucc)))
            ((spechtRep (shapeTableau (D j.succ))).comp
              (sumPermHom (wordBoundaryCut (D j.castSucc) (D j.succ) _ hc)))),
          O (Pi.single w (1 : ℂ))≠0 := by
  obtain ⟨D,hzero,hlast,hsteps⟩ := paperWitness_balance_physical_block_strips k b delta hp z s hprefix
  refine ⟨D,hzero,hlast,?_⟩
  intro j
  obtain ⟨hs,hc⟩ := hsteps j
  obtain ⟨w,f,hf,hfix⟩ := chain_fixed_core hs (shapeTableau (D j.castSucc))
    (shapeTableau (D j.succ)) (wordBoundaryCut _ _ _ hc)
  obtain ⟨O,hO⟩ := fixed_core_word _ _ _ w f hf hfix
  exact ⟨hs,hc,w,O,hO⟩

private def localWordInduced {a n d : ℕ} {nu : YoungDiagram}
    (s : Tableau a nu) (e : Fin n ≃ Fin a ⊕ Fin d) (r : ℕ) := by
  letI : AddCommGroup (Specht s ⊗[ℂ] WordSpace d r) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht s ⊗[ℂ] WordSpace d r) := TensorProduct.leftModule
  exact Representation.ind (A := Specht s ⊗[ℂ] WordSpace d r) (sumPermHom e)
    (independentTensor (spechtRep s) (wordRep d r))

private theorem word_to_induction {a n d r : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (e : Fin n ≃ Fin a ⊕ Fin d)
    (w : Fin d → Fin r)
    (O : Representation.IntertwiningMap (wordRep d r)
      (complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e))))
    (hO : O (Pi.single w (1 : ℂ))≠0) :
    ∃ E : Representation.IntertwiningMap (spechtRep t) (localWordInduced s e r),
      Function.Injective E := by
  let B : Representation.IntertwiningMap
      (independentTensor (spechtRep s) (wordRep d r))
      ((spechtRep t).comp (sumPermHom e)) :=
    (multiplicityIntertwiner (spechtRep s) ((spechtRep t).comp (sumPermHom e))).comp
      (independentTensorMap (Representation.IntertwiningMap.id (spechtRep s)) O)
  have hB : B≠0 := by
    intro hz
    apply hO
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have he : B (x ⊗ₜ[ℂ] Pi.single w (1 : ℂ))=0 :=
      congrArg (fun A : Representation.IntertwiningMap
        (independentTensor (spechtRep s) (wordRep d r))
        ((spechtRep t).comp (sumPermHom e)) => A (x ⊗ₜ[ℂ] Pi.single w (1 : ℂ))) hz
    have hval : B (x ⊗ₜ[ℂ] Pi.single w (1 : ℂ))=(O (Pi.single w (1 : ℂ))) x := by
      change multiplicityEvaluation (spechtRep s) ((spechtRep t).comp (sumPermHom e))
        (TensorProduct.map (Representation.IntertwiningMap.id (spechtRep s)).toLinearMap
          O.toLinearMap (x ⊗ₜ[ℂ] Pi.single w (1 : ℂ)))=_
      rw [TensorProduct.map_tmul]
      rfl
    exact hval.symm.trans he
  letI : AddCommGroup (Specht s ⊗[ℂ] WordSpace d r) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht s ⊗[ℂ] WordSpace d r) := TensorProduct.leftModule
  letI : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card (Equiv.Perm (Fin n))).ne'⟩
  letI := specht_irreducible t
  exact induced_target_embedding_of_nonzero (sumPermHom e)
    (independentTensor (spechtRep s) (wordRep d r)) (spechtRep t) B hB

/-- The boundary target embeds in ordinary induction from its core Specht module
and the original strip-color word module; the source is constrained before local
Specht constituents are selected. The entire word module is not claimed to embed in C. -/
theorem paperWitness_balance_boundary_word_induction (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ D : Fin ((witnessBalancePackingBlocks k delta).length+1) → YoungDiagram,
      D 0=⊥ ∧ D (Fin.last (witnessBalancePackingBlocks k delta).length)=mu ∧
      ∀ j : Fin (witnessBalancePackingBlocks k delta).length,
        SizedStripChain
          (witnessBalancePackingParts hp.staircase_bound z (witnessBalancePackingBlocks k delta)[j.val])
          (D j.castSucc) (D j.succ) ∧
        ∃ hc : (D j.succ).card=(D j.castSucc).card+
          Fintype.card {i : Fin n // witnessBalancePackingPositionKind hp.staircase_bound z i=
            (witnessBalancePackingBlocks k delta)[j.val]},
        ∃ E : Representation.IntertwiningMap (spechtRep (shapeTableau (D j.succ)))
          (localWordInduced (shapeTableau (D j.castSucc))
            (wordBoundaryCut (D j.castSucc) (D j.succ) _ hc)
            (witnessBalancePackingParts hp.staircase_bound z
              (witnessBalancePackingBlocks k delta)[j.val]).length), Function.Injective E := by
  obtain ⟨D,hzero,hlast,hsteps⟩ := paperWitness_balance_boundary_word_source k b delta hp z s hprefix
  refine ⟨D,hzero,hlast,?_⟩
  intro j
  obtain ⟨hs,hc,w,O,hO⟩ := hsteps j
  exact ⟨hs,hc,word_to_induction (shapeTableau (D j.castSucc))
    (shapeTableau (D j.succ)) (wordBoundaryCut _ _ _ hc) w O hO⟩

end
end HSTZ
#print axioms HSTZ.paperWitness_balance_boundary_word_source
#print axioms HSTZ.paperWitness_balance_boundary_word_induction
