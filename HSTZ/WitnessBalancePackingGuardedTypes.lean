import HSTZ.WitnessBalancePackingBlockWord

/-! Select local Specht types from the original strip-color word source.
Uses the Maschke, simple-sector, classification and column-alternation APIs,
building on OpenAI's `math` repository (commit adc7f1241, Apache-2.0). No physical H/K alignment
or global nonzero map from the projected source is inferred. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

private theorem word_height {d r : ℕ} {mu : YoungDiagram} (t : Tableau d mu)
    (J : Representation.IntertwiningMap (spechtRep t) (wordRep d r))
    (hJ : Function.Injective J) : mu.colLen 0≤r := by
  by_contra hn
  have ht : r < mu.colLen 0 := by omega
  let c : Fin (mu.colLen 0) → Fin d := fun i =>
    t.symm ⟨(i.val,0),YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩
  have hci : Function.Injective c := by
    intro i j he
    have hc := congrArg (fun k => (t k).val.1) he
    exact Fin.ext (by simpa [c] using hc)
  have hc0 (i : Fin (mu.colLen 0)) : (t (c i)).val.2=0 := by simp [c]
  have hsingle (q : Fin d → Fin r) : columnAlt t (Pi.single (M := fun _ => ℂ) q (1 : ℂ))=0 := by
    obtain ⟨i,j,hij,hq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => q (c i))
      (by simpa using ht)
    exact columnAlt_collision t q (c i) (c j) (fun he => hij (hci he))
      ((hc0 i).trans (hc0 j).symm) hq
  have hz (x : WordSpace d r) : columnAlt t x=0 := by
    have he : x=∑ q : Fin d → Fin r, Pi.single (M := fun _ => ℂ) q (x q) := by funext q; simp
    rw [he,map_sum]
    apply Finset.sum_eq_zero
    intro q hq
    have heq : Pi.single (M := fun _ => ℂ) q (x q)=(x q) • Pi.single (M := fun _ => ℂ) q (1 : ℂ) := by
      funext v
      simp [Pi.single_apply]
    rw [heq,map_smul,hsingle,smul_zero]
  let p : Specht t := ⟨polytabloid t,mem_cyclic _ _⟩
  have he := columnOperator_intertwining t J p
  have hw : columnOperator t (wordRep d r) (J p)=0 := hz (J p)
  rw [hw] at he
  have hp : columnOperator t (spechtRep t) p=0 := hJ (he.trans (map_zero J.toLinearMap).symm)
  have hv := congrArg Subtype.val hp
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans hv)

open scoped MonoidAlgebra in
private theorem word_sector {a n d r : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (e : Fin n ≃ Fin a ⊕ Fin d)
    (w : Fin d → Fin r)
    (O : Representation.IntertwiningMap (wordRep d r)
      (complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e))))
    (hO : O (Pi.single w (1 : ℂ))≠0) :
    ∃ p : Nat.Partition d, (partitionDiagram p).colLen 0≤r ∧
      ∃ J : Representation.IntertwiningMap (spechtRep (partitionTableau p)) (wordRep d r),
        Function.Injective J ∧ O.comp J≠0 := by
  let rho := wordRep d r
  let eta := complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e))
  let A := Representation.IntertwiningMap.equivLinearMapAsModule rho eta O
  letI : NeZero (Nat.card (Equiv.Perm (Fin d)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card (Equiv.Perm (Fin d))).ne'⟩
  obtain ⟨T,hT⟩ := exists_isCompl A.ker
  have hTne : T≠⊥ := by
    intro he
    have hk : A.ker=⊤ := by simpa only [he,sup_bot_eq] using hT.sup_eq_top
    have hx : rho.asModuleEquiv.symm (Pi.single w (1 : ℂ))∈A.ker := by rw [hk]; trivial
    exact hO hx
  obtain ⟨S,hST,hS⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le T).resolve_left hTne
  letI := hS
  let P := Subrepresentation.ofSubmodule' S
  have hP : Representation.IsIrreducible P.toRepresentation := subrep_irreducible_of_simple S
  let inc : Representation.IntertwiningMap P.toRepresentation rho :=
    { toLinearMap := P.toSubmodule.subtype
      isIntertwining' := fun _ => LinearMap.ext (fun _ => rfl) }
  have hinc : Function.Injective inc := fun _ _ he => Subtype.ext he
  have hOI : O.comp inc≠0 := by
    intro hz
    letI : Nontrivial S := IsSimpleModule.nontrivial (R := ℂ[Equiv.Perm (Fin d)]) (M := S)
    obtain ⟨v,hv⟩ := exists_ne (0 : S)
    let x : P := ⟨rho.asModuleEquiv v.val,v.property⟩
    have he : O x.val=0 := congrArg (fun L : Representation.IntertwiningMap P.toRepresentation eta => L x) hz
    have hx : v.val∈A.ker ⊓ T := ⟨he,hST v.property⟩
    rw [hT.inf_eq_bot] at hx
    exact hv (Subtype.ext ((Submodule.mem_bot _).mp hx))
  letI := hP
  letI : Module.Finite ℂ P.toSubmodule := inferInstance
  obtain ⟨p,⟨iso⟩⟩ := irreducible_equiv_specht P.toRepresentation
  let j : Representation.IntertwiningMap (spechtRep (partitionTableau p)) P.toRepresentation :=
    iso.symm.toIntertwiningMap
  have hj : Function.Bijective j := iso.symm.toLinearEquiv.bijective
  let J := inc.comp j
  have hJ : Function.Injective J := hinc.comp hj.1
  have hOJ : O.comp J≠0 := by
    intro hz
    apply hOI
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨v,hv⟩ := hj.2 x
    subst x
    exact congrArg (fun L : Representation.IntertwiningMap (spechtRep (partitionTableau p)) eta => L v) hz
  exact ⟨p,word_height (partitionTableau p) J hJ,J,hJ,hOJ⟩

private def guardedCut (nu mu : YoungDiagram) (d : ℕ) (hc : mu.card=nu.card+d) :
    Fin mu.card ≃ Fin nu.card ⊕ Fin d := (finCongr hc).trans finSumFinEquiv.symm

/-- Every original block selects a Specht module of its local degree from the
same nonzero strip-color source, with height at most `Parts.length` (2, 1 or 4)
and a nonzero multiplicity map on that selected type. -/
theorem paperWitness_balance_guarded_local_types (k b delta : ℕ)
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
        ∃ p : Nat.Partition (Fintype.card {i : Fin n //
          witnessBalancePackingPositionKind hp.staircase_bound z i=
            (witnessBalancePackingBlocks k delta)[j.val]}),
          (partitionDiagram p).colLen 0≤(witnessBalancePackingParts hp.staircase_bound z
            (witnessBalancePackingBlocks k delta)[j.val]).length ∧
        ∃ L : Representation.IntertwiningMap (spechtRep (partitionTableau p))
          (complementMultiplicity (spechtRep (shapeTableau (D j.castSucc)))
            ((spechtRep (shapeTableau (D j.succ))).comp
              (sumPermHom (guardedCut (D j.castSucc) (D j.succ) _ hc)))), L≠0 := by
  obtain ⟨D,hzero,hlast,hsteps⟩ := paperWitness_balance_boundary_word_source k b delta hp z s hprefix
  refine ⟨D,hzero,hlast,?_⟩
  intro j
  obtain ⟨hs,hc,w,O,hO⟩ := hsteps j
  obtain ⟨p,hh,J,hJ,hOJ⟩ := word_sector (shapeTableau (D j.castSucc))
    (shapeTableau (D j.succ)) (guardedCut _ _ _ hc) w O hO
  exact ⟨hs,hc,p,hh,O.comp J,hOJ⟩

private def selectedInduced {a n d : ℕ} {nu : YoungDiagram}
    (s : Tableau a nu) (e : Fin n ≃ Fin a ⊕ Fin d) (p : Nat.Partition d) := by
  letI : AddCommGroup (Specht s ⊗[ℂ] Specht (partitionTableau p)) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht s ⊗[ℂ] Specht (partitionTableau p)) := TensorProduct.leftModule
  exact Representation.ind (A := Specht s ⊗[ℂ] Specht (partitionTableau p)) (sumPermHom e)
    (independentTensor (spechtRep s) (spechtRep (partitionTableau p)))

private theorem selected_to_induction {a n d : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (e : Fin n ≃ Fin a ⊕ Fin d) (p : Nat.Partition d)
    (L : Representation.IntertwiningMap (spechtRep (partitionTableau p))
      (complementMultiplicity (spechtRep s) ((spechtRep t).comp (sumPermHom e))))
    (hL : L≠0) :
    ∃ E : Representation.IntertwiningMap (spechtRep t) (selectedInduced s e p),
      Function.Injective E := by
  let B : Representation.IntertwiningMap
      (independentTensor (spechtRep s) (spechtRep (partitionTableau p)))
      ((spechtRep t).comp (sumPermHom e)) :=
    (multiplicityIntertwiner (spechtRep s) ((spechtRep t).comp (sumPermHom e))).comp
      (independentTensorMap (Representation.IntertwiningMap.id (spechtRep s)) L)
  have hB : B≠0 := by
    intro hz
    apply hL
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have he : B (x ⊗ₜ[ℂ] v)=0 := congrArg
      (fun A : Representation.IntertwiningMap
        (independentTensor (spechtRep s) (spechtRep (partitionTableau p)))
        ((spechtRep t).comp (sumPermHom e)) => A (x ⊗ₜ[ℂ] v)) hz
    have hval : B (x ⊗ₜ[ℂ] v)=(L v) x := by
      change multiplicityEvaluation (spechtRep s) ((spechtRep t).comp (sumPermHom e))
        (TensorProduct.map (Representation.IntertwiningMap.id (spechtRep s)).toLinearMap
          L.toLinearMap (x ⊗ₜ[ℂ] v))=_
      rw [TensorProduct.map_tmul]
      rfl
    exact hval.symm.trans he
  letI : AddCommGroup (Specht s ⊗[ℂ] Specht (partitionTableau p)) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht s ⊗[ℂ] Specht (partitionTableau p)) := TensorProduct.leftModule
  letI : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card (Equiv.Perm (Fin n))).ne'⟩
  letI := specht_irreducible t
  exact induced_target_embedding_of_nonzero (sumPermHom e)
    (independentTensor (spechtRep s) (spechtRep (partitionTableau p))) (spechtRep t) B hB

/-- The coherent original boundaries and local degrees select short Specht
constituents with ordinary target injections, constructed from the original strip
colors. -/
theorem paperWitness_balance_guarded_boundary_induction (k b delta : ℕ)
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
        ∃ p : Nat.Partition (Fintype.card {i : Fin n //
          witnessBalancePackingPositionKind hp.staircase_bound z i=
            (witnessBalancePackingBlocks k delta)[j.val]}),
          (partitionDiagram p).colLen 0≤(witnessBalancePackingParts hp.staircase_bound z
            (witnessBalancePackingBlocks k delta)[j.val]).length ∧
        ∃ E : Representation.IntertwiningMap (spechtRep (shapeTableau (D j.succ)))
          (selectedInduced (shapeTableau (D j.castSucc))
            (guardedCut (D j.castSucc) (D j.succ) _ hc) p), Function.Injective E := by
  obtain ⟨D,hzero,hlast,hsteps⟩ := paperWitness_balance_guarded_local_types k b delta hp z s hprefix
  refine ⟨D,hzero,hlast,?_⟩
  intro j
  obtain ⟨hs,hc,p,hh,L,hL⟩ := hsteps j
  exact ⟨hs,hc,p,hh,selected_to_induction (shapeTableau (D j.castSucc))
    (shapeTableau (D j.succ)) (guardedCut _ _ _ hc) p L hL⟩

end
end HSTZ
#print axioms HSTZ.paperWitness_balance_guarded_local_types
#print axioms HSTZ.paperWitness_balance_guarded_boundary_induction
