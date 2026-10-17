import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePieriInductionActual

/-! Target tableaux for both original Pieri branches and the local components.
Reuses OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Private position/cyclic
steps reuse the existing alternant relabelling; there is no public generic lift.
All target coordinates and both independent projected factors remain explicit. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

private theorem target_generator {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    positionRelabel E.symm (polytabloid t)=polytabloid (E.trans t) := by
  funext w
  rw [polytabloid_eq_altWord,polytabloid_eq_altWord]
  change altWord (fiberGroup (fun i => (t i).val.2)) (rowWord t) (w ∘ E.symm)=
    altWord (fiberGroup ((fun i => (t i).val.2) ∘ E)) (rowWord t ∘ E) w
  exact altWord_fiber_relabel E _ _ w

private theorem target_image {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    (spechtSub t).toSubmodule.map (positionRelabelIntertwiner E.symm).toLinearMap=
      (spechtSub (E.trans t)).toSubmodule := by
  change (cyclicSpan (wordRep n (nu.colLen 0)) (polytabloid t)).map
    (positionRelabelIntertwiner E.symm).toLinearMap=
    cyclicSpan (wordRep m (nu.colLen 0)) (polytabloid (E.trans t))
  rw [cyclicSpan_image]
  change cyclicSpan ((wordRep m (nu.colLen 0)).comp (positionPermHom E.symm))
    (positionRelabel E.symm (polytabloid t))=_
  rw [target_generator,cyclicSpan_comp_surjective _ _
    (positionPermHom_bijective E.symm).2]

private def targetSpechtMap {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    Representation.IntertwiningMap (spechtRep t)
      ((spechtRep (E.trans t)).comp (positionPermHom E.symm)) where
  toLinearMap := ((positionRelabelIntertwiner E.symm).toLinearMap.domRestrict
    (spechtSub t).toSubmodule).codRestrict (spechtSub (E.trans t)).toSubmodule (fun x => by
      rw [← target_image E t]
      exact Submodule.mem_map.mpr ⟨x.val,x.property,rfl⟩)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (positionRelabelIntertwiner E.symm).map_action g x.val

private theorem targetSpechtMap_surjective {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    Function.Surjective (targetSpechtMap E t) := by
  intro v
  have hv := v.property
  change v.val ∈ (spechtSub (E.trans t)).toSubmodule at hv
  rw [← target_image E t] at hv
  obtain ⟨u,hu,hev⟩ := Submodule.mem_map.mp hv
  exact ⟨⟨u,hu⟩,Subtype.ext hev⟩

private theorem targetSpechtMap_injective {m n : ℕ} {nu : YoungDiagram}
    (E : Fin m ≃ Fin n) (t : Tableau n nu) :
    Function.Injective (targetSpechtMap E t) := by
  intro x y h
  apply Subtype.ext
  exact (positionRelabel E.symm).injective (congrArg Subtype.val h)

private def targetReturn {m n : ℕ} {nu : YoungDiagram} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (E : Fin m ≃ Fin n) (t : Tableau n nu)
    (sigma : Representation ℂ (Equiv.Perm (Fin n)) V)
    (J : Representation.IntertwiningMap (spechtRep (E.trans t))
      (sigma.comp (positionPermHom E))) :
    Representation.IntertwiningMap (spechtRep t) sigma where
  toLinearMap := J.toLinearMap.comp (targetSpechtMap E t).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro u
    have hB := (targetSpechtMap E t).map_action g u
    change (targetSpechtMap E t).toLinearMap (spechtRep t g u)=
      spechtRep (E.trans t) (positionPermHom E.symm g)
        ((targetSpechtMap E t).toLinearMap u) at hB
    have hJ := J.map_action (positionPermHom E.symm g) ((targetSpechtMap E t) u)
    change J.toLinearMap (spechtRep (E.trans t) (positionPermHom E.symm g)
        ((targetSpechtMap E t).toLinearMap u))=
      sigma (positionPermHom E (positionPermHom E.symm g))
        (J.toLinearMap ((targetSpechtMap E t).toLinearMap u)) at hJ
    have hi : positionPermHom E (positionPermHom E.symm g)=g :=
      E.permCongr.apply_symm_apply g
    rw [hi] at hJ
    exact (congrArg J.toLinearMap hB).trans hJ

private theorem targetReturn_injective {m n : ℕ} {nu : YoungDiagram} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (E : Fin m ≃ Fin n) (t : Tableau n nu)
    (sigma : Representation ℂ (Equiv.Perm (Fin n)) V)
    (J : Representation.IntertwiningMap (spechtRep (E.trans t))
      (sigma.comp (positionPermHom E))) (hJ : Function.Injective J) :
    Function.Injective (targetReturn E t sigma J) :=
  hJ.comp (targetSpechtMap_injective E t)

section
variable {k b n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b 0 hk))

/-- The tableau for the existing Pieri statement, obtained from the joint target tableau. -/
def witnessBalanceTwosTailNativeTableau {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1) nu) :
    Tableau ((witnessAttachment (b+1) 0).card+1) nu :=
  (witnessBalanceTwosTailPositions hk z).trans t

theorem witnessBalance_twos_tail_native_tableau_cell {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1) nu)
    (i : Fin ((witnessAttachment (b+1) 0).card+1)) :
    witnessBalanceTwosTailNativeTableau hk z t i=t (witnessBalanceTwosTailPositions hk z i) := rfl

end

section
variable {k b n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b 1 hk))

/-- The tableau for the existing Pieri statement, obtained from the joint target tableau. -/
def witnessBalanceTwosThreeNativeTableau {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2) nu) :
    Tableau ((witnessAttachment (b+1) 0).card+3) nu :=
  (witnessBalanceTwosThreePositions hk z).trans t

theorem witnessBalance_twos_three_native_tableau_cell {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2) nu)
    (i : Fin ((witnessAttachment (b+1) 0).card+3)) :
    witnessBalanceTwosThreeNativeTableau hk z t i=t (witnessBalanceTwosThreePositions hk z i) := rfl

end
section LocalTargets
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- Four-row targets of full component degree for complete neighboring pairs.
The tableau for the existing statement and the inverse action are constructed
internally; the strict pair guard is kept. -/
theorem witnessBalance_neighbor_actual_tableau_support (s : ℕ)
    (hs : 2*s+1<k-(2+delta)) {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z (3+s)) nu) (ht : nu.colLen 0≤4) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceLocalProjectedFactor hk z (3+s)).toRepresentation,
      Function.Injective J := by
  let E := witnessBalanceNeighborPositions hk z s hs
  have hsupport : ∃ J : Representation.IntertwiningMap (spechtRep (E.trans t))
      ((witnessBalanceLocalProjectedFactor hk z (3+s)).toRepresentation.comp
        (positionPermHom E)), Function.Injective J := by
    erw [witnessBalance_neighbor_projected_factor hk z s]
    exact witnessBalanceNeighbor_projected_support hk z s hs (E.trans t) ht
  obtain ⟨J,hJ⟩ := hsupport
  exact ⟨targetReturn E t _ J,targetReturn_injective E t _ J hJ⟩

/-- Even-row two-row targets of full component degree for output 2; the source and
inverse positions are constructed internally. -/
theorem witnessBalance_twos_actual_tableau_support {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0) nu)
    (he : AttachmentEvenRows nu) (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation,
      Function.Injective J := by
  let E := witnessBalanceTwosPositions hk z
  obtain ⟨J,hJ⟩ := witnessBalanceTwos_projected_support hk z (E.trans t) he ht
  exact ⟨targetReturn E t _ J,targetReturn_injective E t _ J hJ⟩
end LocalTargets

section ThreeTarget
variable {k b n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b 1 hk))

/-- Height-three component degree and action, for an arbitrary one-row tableau of size 3. -/
theorem witnessBalance_three_actual_tableau_support
    (t : Tableau (witnessBalanceComponentSize hk z 2) (oneRowDiagram 3)) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceLocalProjectedFactor hk z 2).toRepresentation,
      Function.Injective J := by
  let E := witnessBalanceThreePositions hk z
  obtain ⟨J,hJ⟩ := witnessBalanceThree_projected_support hk z
  let A := tableauSpechtMap (E.trans t) (oneRowTableau 3)
  have hA : Function.Injective A := (tableauSpechtMap_bijective _ _).1
  exact ⟨targetReturn E t _ (J.comp A),targetReturn_injective E t _ (J.comp A) (hJ.comp hA)⟩
end ThreeTarget

section UnmatchedTarget
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- The unmatched original one-row height, with its degree, action and tableau;
the strict unmatched cutoff is kept, without extrapolating from complete pairs. -/
theorem witnessBalance_unmatched_actual_tableau_support (s : ℕ)
    (hd : delta≤1) (hs : k-(2+delta)=2*s+1)
    (t : Tableau (witnessBalanceComponentSize hk z (3+s)) (oneRowDiagram (k-2*s))) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceLocalProjectedFactor hk z (3+s)).toRepresentation,
      Function.Injective J := by
  let E := witnessBalanceUnmatchedPositions hk z s hd hs
  obtain ⟨J,hJ⟩ := witnessBalanceUnmatched_projected_support hk z s hd hs
  let A := tableauSpechtMap (E.trans t) (oneRowTableau (k-2*s))
  have hA : Function.Injective A := (tableauSpechtMap_bijective _ _).1
  exact ⟨targetReturn E t _ (J.comp A),targetReturn_injective E t _ (J.comp A) (hJ.comp hA)⟩

/-- All original output-1 columns, with the whole-tail degree and an arbitrary one-row tableau. -/
theorem witnessBalance_tail_actual_tableau_support
    (t : Tableau (witnessBalanceComponentSize hk z 1)
      (oneRowDiagram (witnessBalanceComponentSize hk z 1))) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceLocalProjectedFactor hk z 1).toRepresentation,
      Function.Injective J := by
  obtain ⟨J,hJ⟩ := witnessBalanceTail_projected_support hk z
  let A := tableauSpechtMap t (oneRowTableau (witnessBalanceComponentSize hk z 1))
  have hA : Function.Injective A := (tableauSpechtMap_bijective _ _).1
  exact ⟨J.comp A,hJ.comp hA⟩
end UnmatchedTarget

section ActualJointInduction
variable {k b n : ℕ} (hk : 5 ≤ k)

/-- All two-row targets of joint degree inject into the original delta = 0
independent-factor ordinary induction, with whole-tail source positions. -/
theorem witnessBalanceTwosTail_actual_tableau_induced_support
    (z : Tableau n (witnessDiagram k b 0 hk)) {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1) nu)
    (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceTwosTailActualInduced hk z), Function.Injective J := by
  let E := witnessBalanceTwosTailPositions hk z
  obtain ⟨J,hJ⟩ := witnessBalanceTwosTail_actual_induced_native_support hk z (E.trans t) ht
  exact ⟨targetReturn E t _ J,targetReturn_injective E t _ J hJ⟩

/-- All two-row targets of joint degree inject into the original delta = 1
independent-factor induction; the case b = 0 / c = 2, x = 3 and the separate tail
are included. -/
theorem witnessBalanceTwosThree_actual_tableau_induced_support
    (z : Tableau n (witnessDiagram k b 1 hk)) {nu : YoungDiagram}
    (t : Tableau (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2) nu)
    (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (witnessBalanceTwosThreeActualInduced hk z), Function.Injective J := by
  let E := witnessBalanceTwosThreePositions hk z
  obtain ⟨J,hJ⟩ := witnessBalanceTwosThree_actual_induced_native_support hk z (E.trans t) ht
  exact ⟨targetReturn E t _ J,targetReturn_injective E t _ J hJ⟩
end ActualJointInduction

end
end HSTZ
#print axioms HSTZ.witnessBalanceTwosTailNativeTableau
#print axioms HSTZ.witnessBalance_twos_tail_native_tableau_cell
#print axioms HSTZ.witnessBalanceTwosThreeNativeTableau
#print axioms HSTZ.witnessBalance_twos_three_native_tableau_cell

#print axioms HSTZ.witnessBalance_neighbor_actual_tableau_support
#print axioms HSTZ.witnessBalance_twos_actual_tableau_support

#print axioms HSTZ.witnessBalance_three_actual_tableau_support

#print axioms HSTZ.witnessBalance_unmatched_actual_tableau_support

#print axioms HSTZ.witnessBalance_tail_actual_tableau_support

#print axioms HSTZ.witnessBalanceTwosTail_actual_tableau_induced_support
#print axioms HSTZ.witnessBalanceTwosThree_actual_tableau_induced_support
