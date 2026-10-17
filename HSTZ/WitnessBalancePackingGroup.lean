import HSTZ.WitnessBalancePackingGeometry

/-! The finite product of all original label position groups, mapping back to the same `H`.
Reuses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Joint packing blocks keep distinct original labels. No merged permutation action, finite
tensor image or Young support is asserted here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

def witnessBalancePackingOriginalLabels (k delta : ℕ) : List ℕ :=
  (witnessBalancePackingBlocks k delta).flatMap (witnessBalancePackingLabels delta)

abbrev witnessBalancePackingLabelIndex (k delta : ℕ) :=
  {a : ℕ // a∈witnessBalancePackingOriginalLabels k delta}

instance (k delta : ℕ) : Fintype (witnessBalancePackingLabelIndex k delta) :=
  Fintype.subtype (witnessBalancePackingOriginalLabels k delta).toFinset (by intro a; simp)

theorem witnessBalance_packing_original_label_mem (hd : delta≤1) (i : Fin n) :
    witnessBalanceLabel hk z i∈witnessBalancePackingOriginalLabels k delta := by
  apply List.mem_flatMap.mpr
  let q := witnessBalancePackingPositionKind hk z i
  have hq := witnessBalance_packing_position_mem hk z hd i
  exact ⟨q,hq,(witnessBalance_packing_position_iff hk z hd q hq i).mpr rfl⟩

/-- The original label subtype, before component `Fin` enumeration. -/
def witnessBalancePackingLabelCells (hd : delta≤1) : Fin n ≃
    (Σ a : witnessBalancePackingLabelIndex k delta,
      {i : Fin n // witnessBalanceLabel hk z i=a.val}) where
  toFun i := ⟨⟨witnessBalanceLabel hk z i,witnessBalance_packing_original_label_mem hk z hd i⟩,⟨i,rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨a,ha⟩,⟨i,hi⟩⟩
    dsimp at hi
    subst a
    rfl

/-- Each named original component `Fin`, transported through the label cells. -/
def witnessBalancePackingLabelCut (hd : delta≤1) : Fin n ≃
    (Σ a : witnessBalancePackingLabelIndex k delta,
      Fin (witnessBalanceComponentSize hk z a.val)) :=
  (witnessBalancePackingLabelCells hk z hd).trans
    (Equiv.sigmaCongrRight fun a => Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=a.val})

theorem witnessBalancePackingLabelCut_label (hd : delta≤1) (i : Fin n) :
    (witnessBalancePackingLabelCut hk z hd i).1.val=witnessBalanceLabel hk z i := rfl

theorem witnessBalancePackingLabelCut_inverse_label (hd : delta≤1)
    (a : witnessBalancePackingLabelIndex k delta)
    (j : Fin (witnessBalanceComponentSize hk z a.val)) :
    witnessBalanceLabel hk z ((witnessBalancePackingLabelCut hk z hd).symm ⟨a,j⟩)=a.val :=
  ((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=a.val}).symm j).property

abbrev witnessBalancePackingOriginalGroup :=
  ∀ a : witnessBalancePackingLabelIndex k delta, Equiv.Perm (Fin (witnessBalanceComponentSize hk z a.val))

private def originalProductPerm (hd : delta≤1) : witnessBalancePackingOriginalGroup hk z →*
    Equiv.Perm (Fin n) :=
  ((witnessBalancePackingLabelCut hk z hd).symm.permCongrHom.toMonoidHom).comp
    (Equiv.Perm.sigmaCongrRightHom fun a : witnessBalancePackingLabelIndex k delta =>
      Fin (witnessBalanceComponentSize hk z a.val))

/-- All original labels, each acted on independently, give exactly the original `H`. -/
def witnessBalancePackingOriginalHom (hd : delta≤1) : witnessBalancePackingOriginalGroup hk z →*
    witnessBalanceGroup hk z where
  toFun g := ⟨originalProductPerm hk z hd g,by
    intro i
    change witnessBalanceLabel hk z ((witnessBalancePackingLabelCut hk z hd).symm
      ⟨(witnessBalancePackingLabelCut hk z hd i).1,
       g (witnessBalancePackingLabelCut hk z hd i).1 (witnessBalancePackingLabelCut hk z hd i).2⟩)=
      witnessBalanceLabel hk z i
    rw [witnessBalancePackingLabelCut_inverse_label,witnessBalancePackingLabelCut_label]⟩
  map_one' := Subtype.ext ((originalProductPerm hk z hd).map_one)
  map_mul' g h := Subtype.ext ((originalProductPerm hk z hd).map_mul g h)

theorem witnessBalancePackingOriginalHom_value (hd : delta≤1)
    (g : witnessBalancePackingOriginalGroup hk z) (i : Fin n) :
    (witnessBalancePackingOriginalHom hk z hd g).val i=
      (witnessBalancePackingLabelCut hk z hd).symm
        ⟨(witnessBalancePackingLabelCut hk z hd i).1,
         g (witnessBalancePackingLabelCut hk z hd i).1 (witnessBalancePackingLabelCut hk z hd i).2⟩ := rfl

private def originalLabelPerm (a : ℕ) (g : witnessBalanceGroup hk z) :
    Equiv.Perm {i : Fin n // witnessBalanceLabel hk z i=a} :=
  g.val.subtypeEquiv (fun i => by rw [g.property i])

theorem witnessBalancePackingOriginalHom_bijective (hd : delta≤1) :
    Function.Bijective (witnessBalancePackingOriginalHom hk z hd) := by
  constructor
  · intro g h he
    have hv := congrArg (fun x : witnessBalanceGroup hk z => x.val) he
    apply Equiv.Perm.sigmaCongrRightHom_injective
    exact (witnessBalancePackingLabelCut hk z hd).symm.permCongr.injective hv
  · intro g
    let p : witnessBalancePackingOriginalGroup hk z := fun a =>
      (Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=a.val}).permCongr
        (originalLabelPerm hk z a.val g)
    refine ⟨p,Subtype.ext ?_⟩
    apply Equiv.ext
    intro i
    change ((Fintype.equivFin {j : Fin n // witnessBalanceLabel hk z j=witnessBalanceLabel hk z i}).symm
      ((Fintype.equivFin {j : Fin n // witnessBalanceLabel hk z j=witnessBalanceLabel hk z i}).permCongr
        (originalLabelPerm hk z (witnessBalanceLabel hk z i) g)
        ((Fintype.equivFin {j : Fin n // witnessBalanceLabel hk z j=witnessBalanceLabel hk z i}) ⟨i,rfl⟩))).val=g.val i
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
    rfl

def witnessBalancePackingOriginalEquiv (hd : delta≤1) :
    witnessBalancePackingOriginalGroup hk z ≃* witnessBalanceGroup hk z :=
  MulEquiv.ofBijective (witnessBalancePackingOriginalHom hk z hd)
    (witnessBalancePackingOriginalHom_bijective hk z hd)

/-- The projected factor family over the all-label product group.
This specifies actions only, not a tensor image or support of the selected other factor. -/
def witnessBalancePackingFactorAction (a : witnessBalancePackingLabelIndex k delta) :
    Representation ℂ (witnessBalancePackingOriginalGroup hk z)
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule :=
  (witnessBalanceLocalProjectedFactor hk z a.val).toRepresentation.comp
    { toFun := fun g => g a
      map_one' := rfl
      map_mul' _ _ := rfl }

theorem witnessBalancePackingFactorAction_value (a : witnessBalancePackingLabelIndex k delta)
    (g : witnessBalancePackingOriginalGroup hk z)
    (v : (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule) :
    witnessBalancePackingFactorAction hk z a g v=
      (witnessBalanceLocalProjectedFactor hk z a.val).toRepresentation (g a) v := rfl

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingOriginalLabels
#print axioms HSTZ.witnessBalance_packing_original_label_mem
#print axioms HSTZ.witnessBalancePackingLabelCells
#print axioms HSTZ.witnessBalancePackingLabelCut
#print axioms HSTZ.witnessBalancePackingLabelCut_label
#print axioms HSTZ.witnessBalancePackingLabelCut_inverse_label
#print axioms HSTZ.witnessBalancePackingOriginalHom
#print axioms HSTZ.witnessBalancePackingOriginalHom_value
#print axioms HSTZ.witnessBalancePackingOriginalHom_bijective
#print axioms HSTZ.witnessBalancePackingOriginalEquiv
#print axioms HSTZ.witnessBalancePackingFactorAction
#print axioms HSTZ.witnessBalancePackingFactorAction_value
