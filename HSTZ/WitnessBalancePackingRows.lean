import HSTZ.WitnessBalancePackingGenerator

/-! All original cyclic component factors map onto the same original H-cyclic C.
Uses the multilinear `map_sum` and span interfaces, building on
OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The normalization is derived internally. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
  (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessBalancePackingRowsSpace :=
  ⨂[ℂ] a : witnessBalancePackingLabelIndex k delta,
    (witnessBalanceComponentRows hk z a.val).toSubmodule

private def rowRestriction (hd : delta ≤ 1)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0))
    (a : witnessBalancePackingLabelIndex k delta) :=
  fun i : Fin (witnessBalanceComponentSize hk z a.val) =>
    w ((witnessBalancePackingLabelCut hk z hd).symm ⟨a,i⟩)

private theorem assemble_restrict (hd : delta ≤ 1)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0)) :
    witnessBalancePackingRowAssembly hk z hd (rowRestriction hk z hd w)=w := by
  funext i
  exact congrArg w ((witnessBalancePackingLabelCut hk z hd).symm_apply_apply i)

private theorem restriction_action (hd : delta ≤ 1)
    (g : witnessBalancePackingOriginalGroup hk z)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0))
    (a : witnessBalancePackingLabelIndex k delta) :
    rowRestriction hk z hd (w ∘ (witnessBalancePackingOriginalHom hk z hd g).val) a=
      rowRestriction hk z hd w a ∘ g a := by
  let E := witnessBalancePackingLabelCut hk z hd
  funext i
  change w ((witnessBalancePackingOriginalHom hk z hd g).val (E.symm ⟨a,i⟩))=
    w (E.symm ⟨a,g a i⟩)
  have hi : E (E.symm ⟨a,i⟩)=⟨a,i⟩ := E.apply_symm_apply ⟨a,i⟩
  have hp := witnessBalancePackingOriginalHom_value hk z hd g (E.symm ⟨a,i⟩)
  change (witnessBalancePackingOriginalHom hk z hd g).val (E.symm ⟨a,i⟩)=
    E.symm ⟨(E (E.symm ⟨a,i⟩)).1,g (E (E.symm ⟨a,i⟩)).1 (E (E.symm ⟨a,i⟩)).2⟩ at hp
  rw [hi] at hp
  exact congrArg w hp

private def rowCoefficient (hd : delta ≤ 1) : MultilinearMap ℂ
    (fun a : witnessBalancePackingLabelIndex k delta =>
      WordSpace (witnessBalanceComponentSize hk z a.val) ((witnessDiagram k b delta hk).colLen 0))
    (WordSpace n ((witnessDiagram k b delta hk).colLen 0)) :=
  MultilinearMap.pi fun w =>
    (MultilinearMap.mkPiAlgebra ℂ (witnessBalancePackingLabelIndex k delta) ℂ).compLinearMap
      (fun a => (witnessBalancePackingBaseCoefficient hk z a.val)⁻¹ •
        LinearMap.proj (rowRestriction hk z hd w a))

private theorem rowCoefficient_value (hd : delta ≤ 1)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      WordSpace (witnessBalanceComponentSize hk z a.val) ((witnessDiagram k b delta hk).colLen 0))
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0)) :
    rowCoefficient hk z hd x w=
      ∏ a, x a (rowRestriction hk z hd w a)/witnessBalancePackingBaseCoefficient hk z a.val := by
  change (∏ a, (witnessBalancePackingBaseCoefficient hk z a.val)⁻¹*
    x a (rowRestriction hk z hd w a))=_
  apply Finset.prod_congr rfl
  intro a _
  simp only [div_eq_mul_inv,mul_comm]

private theorem rowCoefficient_orbit (hd : delta ≤ 1)
    (g : witnessBalancePackingOriginalGroup hk z) :
    rowCoefficient hk z hd (fun a => wordRep _ _ (g a) (witnessBalanceComponentWord hk z a.val))=
      wordRep n ((witnessDiagram k b delta hk).colLen 0)
        (witnessBalancePackingOriginalHom hk z hd g).val (polytabloid z) := by
  funext w
  rw [rowCoefficient_value]
  change _=polytabloid z (w ∘ (witnessBalancePackingOriginalHom hk z hd g).val)
  have h := witnessBalancePackingGenerator_coordinates hk z hd
    (rowRestriction hk z hd (w ∘ (witnessBalancePackingOriginalHom hk z hd g).val))
  rw [assemble_restrict] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro a _
  rw [restriction_action]
  rfl

/-- Concrete finite inclusion of the original C factors, normalized by the
prescribed row-base coefficients, which are shown to be nonzero. -/
def witnessBalancePackingRowsWords (hd : delta ≤ 1) :
    witnessBalancePackingRowsSpace hk z →ₗ[ℂ] WordSpace n ((witnessDiagram k b delta hk).colLen 0) :=
  PiTensorProduct.lift ((rowCoefficient hk z hd).compLinearMap
    (fun a : witnessBalancePackingLabelIndex k delta =>
      (witnessBalanceComponentRows hk z a.val).toSubmodule.subtype))

private theorem rowsWords_tprod (hd : delta ≤ 1)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceComponentRows hk z a.val).toSubmodule) :
    witnessBalancePackingRowsWords hk z hd (PiTensorProduct.tprod ℂ x)=
      rowCoefficient hk z hd (fun a => (x a).val) := PiTensorProduct.lift.tprod _

/-- The same original H-orbit carrier. This does not identify the whole restricted
Specht module or the diagonal cyclic span of a repeated square tensor. -/
theorem witnessBalancePackingRowsWords_range (hd : delta ≤ 1) :
    (witnessBalancePackingRowsWords hk z hd).range=(witnessBalanceLocalRows hk z).toSubmodule := by
  apply le_antisymm
  · rintro v ⟨q,rfl⟩
    induction q using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul]
      apply Submodule.smul_mem
      rw [rowsWords_tprod]
      have hx : ∀ a : witnessBalancePackingLabelIndex k delta,
          ∃ c : Equiv.Perm (Fin (witnessBalanceComponentSize hk z a.val)) → ℂ,
            ∑ g, c g • wordRep _ _ g (witnessBalanceComponentWord hk z a.val)=(x a).val := by
        intro a
        apply (Submodule.mem_span_range_iff_exists_fun ℂ).mp
        exact (x a).property
      choose c hc using hx
      have he : (fun a => (x a).val)=(fun a => ∑ g, c a g •
          wordRep _ _ g (witnessBalanceComponentWord hk z a.val)) := by
        funext a
        exact (hc a).symm
      rw [he,MultilinearMap.map_sum]
      apply Submodule.sum_mem
      intro g _
      rw [MultilinearMap.map_smul_univ,rowCoefficient_orbit]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨witnessBalancePackingOriginalHom hk z hd g,rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · change Submodule.span ℂ (Set.range fun g : witnessBalanceGroup hk z =>
      wordRep n ((witnessDiagram k b delta hk).colLen 0) g.val (polytabloid z)) ≤ _
    apply Submodule.span_le.mpr
    rintro v ⟨g,rfl⟩
    obtain ⟨p,hp⟩ := (witnessBalancePackingOriginalHom_bijective hk z hd).2 g
    let x : ∀ a : witnessBalancePackingLabelIndex k delta,
        (witnessBalanceComponentRows hk z a.val).toSubmodule := fun a =>
      ⟨wordRep _ _ (p a) (witnessBalanceComponentWord hk z a.val),Submodule.subset_span ⟨p a,rfl⟩⟩
    refine ⟨PiTensorProduct.tprod ℂ x,?_⟩
    rw [rowsWords_tprod]
    change rowCoefficient hk z hd (fun a => wordRep _ _ (p a) (witnessBalanceComponentWord hk z a.val))=_
    rw [rowCoefficient_orbit,hp]

/-- Coefficients of the normalized row map over all original components. -/
theorem witnessBalancePackingRowsWords_tprod_value (hd : delta ≤ 1)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceComponentRows hk z a.val).toSubmodule)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0)) :
    witnessBalancePackingRowsWords hk z hd (PiTensorProduct.tprod ℂ x) w=
      ∏ a, (x a).val (leftWord (witnessBalanceComponentCut hk z a.val) w)/
        witnessBalancePackingBaseCoefficient hk z a.val := by
  rw [rowsWords_tprod,rowCoefficient_value]
  rfl

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingRowsWords
#print axioms HSTZ.witnessBalancePackingRowsWords_range

#print axioms HSTZ.witnessBalancePackingRowsWords_tprod_value
