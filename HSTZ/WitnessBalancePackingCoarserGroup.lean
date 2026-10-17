import HSTZ.WitnessBalancePackingJointPair

/-! A larger joint/rest block group acting on the original physical positions.
Reuses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This is a group homomorphism on positions; it gives no module transitivity, identification
with `H`, or support statement. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical
section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessBalancePackingJointDegree := witnessBalanceComponentSize hk z 0+
  witnessBalanceComponentSize hk z (witnessBalancePackingJointLabel delta)
abbrev witnessBalancePackingRestPositions :=
  Σ a : witnessBalancePackingRestIndex k delta, Fin (witnessBalanceComponentSize hk z a.val.val)

private def jointFiberPositions :
    (Σ a : witnessBalancePackingJointIndex k delta, Fin (witnessBalanceComponentSize hk z a.val.val)) ≃
      Fin (witnessBalancePackingJointDegree hk z) := by
  let N : Unit ⊕ Unit → Type := fun u => Fin (witnessBalanceComponentSize hk z
    (witnessBalancePackingJointOrder k delta u).val.val)
  exact (Equiv.sigmaCongrLeft' (witnessBalancePackingJointOrder k delta).symm).trans
    ((Equiv.sumSigmaDistrib N).trans
      ((Equiv.sumCongr (Equiv.uniqueSigma (fun u : Unit => N (.inl u)))
        (Equiv.uniqueSigma (fun u : Unit => N (.inr u)))).trans finSumFinEquiv))

private theorem jointFiber_first
    (i : Fin (witnessBalanceComponentSize hk z 0)) :
    (jointFiberPositions hk z).symm (finSumFinEquiv (.inl i))=
      ⟨witnessBalancePackingJointOrder k delta (.inl ()),i⟩ := by
  apply (jointFiberPositions hk z).injective
  rw [Equiv.apply_symm_apply]
  unfold jointFiberPositions
  simp only [Equiv.trans_apply,Equiv.sigmaCongrLeft',Equiv.symm_symm]
  have he : (Equiv.sigmaCongrLeft (β:=fun a : witnessBalancePackingJointIndex k delta =>
      Fin (witnessBalanceComponentSize hk z a.val.val))
      (witnessBalancePackingJointOrder k delta)).symm
        ⟨witnessBalancePackingJointOrder k delta (.inl ()),i⟩=⟨.inl (),i⟩ :=
    (Equiv.sigmaCongrLeft (β:=fun a : witnessBalancePackingJointIndex k delta =>
      Fin (witnessBalanceComponentSize hk z a.val.val))
      (witnessBalancePackingJointOrder k delta)).symm_apply_apply ⟨.inl (),i⟩
  rw [he]
  rfl

private theorem jointFiber_second
    (i : Fin (witnessBalanceComponentSize hk z (witnessBalancePackingJointLabel delta))) :
    (jointFiberPositions hk z).symm (finSumFinEquiv (.inr i))=
      ⟨witnessBalancePackingJointOrder k delta (.inr ()),i⟩ := by
  apply (jointFiberPositions hk z).injective
  rw [Equiv.apply_symm_apply]
  unfold jointFiberPositions
  simp only [Equiv.trans_apply,Equiv.sigmaCongrLeft',Equiv.symm_symm]
  have he : (Equiv.sigmaCongrLeft (β:=fun a : witnessBalancePackingJointIndex k delta =>
      Fin (witnessBalanceComponentSize hk z a.val.val))
      (witnessBalancePackingJointOrder k delta)).symm
        ⟨witnessBalancePackingJointOrder k delta (.inr ()),i⟩=⟨.inr (),i⟩ :=
    (Equiv.sigmaCongrLeft (β:=fun a : witnessBalancePackingJointIndex k delta =>
      Fin (witnessBalanceComponentSize hk z a.val.val))
      (witnessBalancePackingJointOrder k delta)).symm_apply_apply ⟨.inr (),i⟩
  rw [he]
  rfl

/-- The same original `LabelCut`, regrouped through fibers before block enumeration. -/
def witnessBalancePackingCoarserPositions (hd : delta≤1) : Fin n ≃
    Fin (witnessBalancePackingJointDegree hk z) ⊕ witnessBalancePackingRestPositions hk z :=
  (witnessBalancePackingLabelCut hk z hd).trans
    ((Equiv.sigmaCongrLeft' (witnessBalancePackingJointRestCut k delta)).trans
      ((Equiv.sumSigmaDistrib (fun a : witnessBalancePackingJointIndex k delta ⊕
          witnessBalancePackingRestIndex k delta =>
        Fin (witnessBalanceComponentSize hk z ((witnessBalancePackingJointRestCut k delta).symm a).val))).trans
        (Equiv.sumCongr (jointFiberPositions hk z) (Equiv.refl _))))

theorem witnessBalancePackingCoarserPositions_first (hd : delta≤1)
    (i : Fin (witnessBalanceComponentSize hk z 0)) :
    (witnessBalancePackingCoarserPositions hk z hd).symm
      (.inl (finSumFinEquiv (.inl i)))=
      (witnessBalancePackingLabelCut hk z hd).symm
        ⟨(witnessBalancePackingJointOrder k delta (.inl ())).val,i⟩ := by
  change (witnessBalancePackingLabelCut hk z hd).symm
    ((Equiv.sigmaCongrLeft' (witnessBalancePackingJointRestCut k delta)).symm
      ((Equiv.sumSigmaDistrib (fun a : witnessBalancePackingJointIndex k delta ⊕
          witnessBalancePackingRestIndex k delta =>
        Fin (witnessBalanceComponentSize hk z ((witnessBalancePackingJointRestCut k delta).symm a).val))).symm
        (.inl ((jointFiberPositions hk z).symm (finSumFinEquiv (.inl i))))))=_
  rw [jointFiber_first]
  simp [Equiv.sigmaCongrLeft',Equiv.sumSigmaDistrib,witnessBalancePackingJointRestCut]
  rfl

theorem witnessBalancePackingCoarserPositions_second (hd : delta≤1)
    (i : Fin (witnessBalanceComponentSize hk z (witnessBalancePackingJointLabel delta))) :
    (witnessBalancePackingCoarserPositions hk z hd).symm
      (.inl (finSumFinEquiv (.inr i)))=
      (witnessBalancePackingLabelCut hk z hd).symm
        ⟨(witnessBalancePackingJointOrder k delta (.inr ())).val,i⟩ := by
  change (witnessBalancePackingLabelCut hk z hd).symm
    ((Equiv.sigmaCongrLeft' (witnessBalancePackingJointRestCut k delta)).symm
      ((Equiv.sumSigmaDistrib (fun a : witnessBalancePackingJointIndex k delta ⊕
          witnessBalancePackingRestIndex k delta =>
        Fin (witnessBalanceComponentSize hk z ((witnessBalancePackingJointRestCut k delta).symm a).val))).symm
        (.inl ((jointFiberPositions hk z).symm (finSumFinEquiv (.inr i))))))=_
  rw [jointFiber_second]
  simp [Equiv.sigmaCongrLeft',Equiv.sumSigmaDistrib,witnessBalancePackingJointRestCut]
  rfl

theorem witnessBalancePackingCoarserPositions_rest (hd : delta≤1)
    (a : witnessBalancePackingRestIndex k delta)
    (i : Fin (witnessBalanceComponentSize hk z a.val.val)) :
    (witnessBalancePackingCoarserPositions hk z hd).symm (.inr ⟨a,i⟩)=
      (witnessBalancePackingLabelCut hk z hd).symm ⟨a.val,i⟩ := by
  simp [witnessBalancePackingCoarserPositions,Equiv.sigmaCongrLeft',
    Equiv.sumSigmaDistrib,witnessBalancePackingJointRestCut]

abbrev witnessBalancePackingCoarserGroup := Equiv.Perm (Fin (witnessBalancePackingJointDegree hk z)) ×
  (∀ a : witnessBalancePackingRestIndex k delta, Equiv.Perm (Fin (witnessBalanceComponentSize hk z a.val.val)))

private def coarserPerm : witnessBalancePackingCoarserGroup hk z →*
    Equiv.Perm (Fin (witnessBalancePackingJointDegree hk z) ⊕ witnessBalancePackingRestPositions hk z) :=
  (Equiv.Perm.sumCongrHom _ _).comp
    ((MonoidHom.id _).prodMap (Equiv.Perm.sigmaCongrRightHom fun a : witnessBalancePackingRestIndex k delta =>
      Fin (witnessBalanceComponentSize hk z a.val.val)))

/-- The full joint permutation group and all independent rest label permutation groups act
on the source positions. This group is larger than `H`; no source representation is extended
to it. -/
def witnessBalancePackingCoarserHom (hd : delta≤1) : witnessBalancePackingCoarserGroup hk z →*
    Equiv.Perm (Fin n) :=
  ((witnessBalancePackingCoarserPositions hk z hd).symm.permCongrHom.toMonoidHom).comp (coarserPerm hk z)

theorem witnessBalancePackingCoarserHom_value (hd : delta≤1)
    (g : witnessBalancePackingCoarserGroup hk z)
    (v : Fin (witnessBalancePackingJointDegree hk z) ⊕ witnessBalancePackingRestPositions hk z) :
    witnessBalancePackingCoarserHom hk z hd g ((witnessBalancePackingCoarserPositions hk z hd).symm v)=
      (witnessBalancePackingCoarserPositions hk z hd).symm
        (v.map g.1 (fun a => ⟨a.1,g.2 a.1 a.2⟩)) := by
  simp [witnessBalancePackingCoarserHom,coarserPerm,Equiv.permCongr_apply]
  cases v with
  | inl i => rfl
  | inr v => rcases v with ⟨a,i⟩; rfl

/-- Original labels 0 and 1/2 remain separate under this subgroup inclusion. -/
def witnessBalancePackingOriginalToCoarser : witnessBalancePackingOriginalGroup hk z →*
    witnessBalancePackingCoarserGroup hk z where
  toFun g := (sumPermHom (finSumFinEquiv.symm : Fin (witnessBalancePackingJointDegree hk z) ≃
      Fin (witnessBalanceComponentSize hk z 0) ⊕
        Fin (witnessBalanceComponentSize hk z (witnessBalancePackingJointLabel delta)))
      (witnessBalancePackingJointProductHom hk z g), fun a => g a.val)
  map_one' := by simp only [map_one]; rfl
  map_mul' g h := by simp only [map_mul]; rfl

private theorem original_inverse_value (hd : delta≤1)
    (g : witnessBalancePackingOriginalGroup hk z)
    (a : witnessBalancePackingLabelIndex k delta)
    (j : Fin (witnessBalanceComponentSize hk z a.val)) :
    (witnessBalancePackingOriginalHom hk z hd g).val
      ((witnessBalancePackingLabelCut hk z hd).symm ⟨a,j⟩)=
        (witnessBalancePackingLabelCut hk z hd).symm ⟨a,g a j⟩ := by
  let E : Fin n ≃ Σ a : witnessBalancePackingLabelIndex k delta,
    Fin (witnessBalanceComponentSize hk z a.val) := witnessBalancePackingLabelCut hk z hd
  have he : E (E.symm ⟨a,j⟩)=⟨a,j⟩ := E.apply_symm_apply ⟨a,j⟩
  rw [witnessBalancePackingOriginalHom_value]
  change E.symm ⟨(E (E.symm ⟨a,j⟩)).1,g (E (E.symm ⟨a,j⟩)).1 (E (E.symm ⟨a,j⟩)).2⟩=
    E.symm ⟨a,g a j⟩
  rw [he]

/-- Restricting the larger physical block homomorphism gives the original inclusion of `H`. -/
theorem witnessBalancePackingCoarserHom_original (hd : delta≤1)
    (g : witnessBalancePackingOriginalGroup hk z) :
    witnessBalancePackingCoarserHom hk z hd (witnessBalancePackingOriginalToCoarser hk z g)=
      (witnessBalancePackingOriginalHom hk z hd g).val := by
  apply Equiv.ext
  intro i
  obtain ⟨v,rfl⟩ := (witnessBalancePackingCoarserPositions hk z hd).symm.surjective i
  cases v with
  | inl v =>
    obtain ⟨u,rfl⟩ := (finSumFinEquiv :
      Fin (witnessBalanceComponentSize hk z 0) ⊕
        Fin (witnessBalanceComponentSize hk z (witnessBalancePackingJointLabel delta)) ≃
        Fin (witnessBalancePackingJointDegree hk z)).surjective v
    cases u with
    | inl j =>
      rw [witnessBalancePackingCoarserHom_value,witnessBalancePackingCoarserPositions_first]
      change (witnessBalancePackingCoarserPositions hk z hd).symm
        (.inl (sumPermHom finSumFinEquiv.symm (witnessBalancePackingJointProductHom hk z g)
          (finSumFinEquiv (.inl j))))=_
      simp only [sumPermHom,OAI.Saxl.sumPerm,Equiv.permCongr_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,
        witnessBalancePackingJointProductHom,MonoidHom.coe_mk,OneHom.coe_mk,
        Equiv.symm_symm,Sum.map_inl,Sum.map_inr]
      rw [witnessBalancePackingCoarserPositions_first]
      exact (original_inverse_value hk z hd g
        (witnessBalancePackingJointOrder k delta (.inl ())).val j).symm
    | inr j =>
      rw [witnessBalancePackingCoarserHom_value,witnessBalancePackingCoarserPositions_second]
      change (witnessBalancePackingCoarserPositions hk z hd).symm
        (.inl (sumPermHom finSumFinEquiv.symm (witnessBalancePackingJointProductHom hk z g)
          (finSumFinEquiv (.inr j))))=_
      simp only [sumPermHom,OAI.Saxl.sumPerm,Equiv.permCongr_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,
        witnessBalancePackingJointProductHom,MonoidHom.coe_mk,OneHom.coe_mk,
        Equiv.symm_symm,Sum.map_inl,Sum.map_inr]
      rw [witnessBalancePackingCoarserPositions_second]
      exact (original_inverse_value hk z hd g
        (witnessBalancePackingJointOrder k delta (.inr ())).val j).symm
  | inr v =>
    rcases v with ⟨a,j⟩
    rw [witnessBalancePackingCoarserHom_value,witnessBalancePackingCoarserPositions_rest]
    change (witnessBalancePackingCoarserPositions hk z hd).symm (.inr ⟨a,g a.val j⟩)=_
    rw [witnessBalancePackingCoarserPositions_rest]
    exact (original_inverse_value hk z hd g a.val j).symm

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingCoarserPositions
#print axioms HSTZ.witnessBalancePackingCoarserPositions_first
#print axioms HSTZ.witnessBalancePackingCoarserPositions_second
#print axioms HSTZ.witnessBalancePackingCoarserPositions_rest
#print axioms HSTZ.witnessBalancePackingCoarserHom
#print axioms HSTZ.witnessBalancePackingCoarserHom_value
#print axioms HSTZ.witnessBalancePackingOriginalToCoarser
#print axioms HSTZ.witnessBalancePackingCoarserHom_original
