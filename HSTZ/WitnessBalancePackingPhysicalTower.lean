import HSTZ.InducedPiRelabel
import HSTZ.WitnessBalancePackingPiTower
import HSTZ.WitnessBalancePackingCoarserGroup

/-! The ordered witness tower relabelled to the physical joint/rest block group.
Block 0 is the joint block; every other original packing block carries exactly one
original label, which is a rest label. Block degrees equal the corresponding physical
component sizes, so the ordered block hom and the physical `CoarserHom` are conjugate,
and the original target injects into induction along `CoarserHom`. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

/-- The single original label of a non-joint packing block. -/
def witnessBalancePackingBlockLabel : WitnessBalancePackingKind → ℕ
  | .joint => 0
  | .tail => 1
  | .early s => 3+s

theorem witnessBalancePackingBlockLabel_mem {delta : ℕ} (q : WitnessBalancePackingKind)
    (hq : q≠.joint) : witnessBalancePackingBlockLabel q∈witnessBalancePackingLabels delta q := by
  cases q with
  | joint => exact absurd rfl hq
  | tail => simp [witnessBalancePackingBlockLabel,witnessBalancePackingLabels]
  | early s => simp [witnessBalancePackingBlockLabel,witnessBalancePackingLabels]

theorem witnessBalancePackingBlockLabel_injective (p q : WitnessBalancePackingKind)
    (hp : p≠.joint) (hq : q≠.joint)
    (h : witnessBalancePackingBlockLabel p=witnessBalancePackingBlockLabel q) : p=q := by
  cases p <;> cases q <;> simp_all [witnessBalancePackingBlockLabel] <;> omega

theorem witnessBalancePackingBlockLabel_not_joint {k delta : ℕ} (q : WitnessBalancePackingKind)
    (hq : q∈witnessBalancePackingBlocks k delta) (hj : q≠.joint) :
    ¬(witnessBalancePackingBlockLabel q=0 ∨
      witnessBalancePackingBlockLabel q=witnessBalancePackingJointLabel delta) := by
  rcases (witnessBalance_packing_blocks_mem k delta q).mp hq with h | ⟨hd,h⟩ | ⟨s,h,_⟩
  · exact absurd h hj
  · subst h
    subst hd
    decide
  · subst h
    simp only [witnessBalancePackingBlockLabel,witnessBalancePackingJointLabel]
    split_ifs <;> omega

/-- Packing block -> joint or its rest label. -/
def witnessBalancePackingBlockTarget (k delta : ℕ)
    (i : Fin (witnessBalancePackingBlocks k delta).length) :
    Unit ⊕ witnessBalancePackingRestIndex k delta :=
  if h : (witnessBalancePackingBlocks k delta)[i.val]=.joint then .inl () else
    .inr ⟨⟨witnessBalancePackingBlockLabel (witnessBalancePackingBlocks k delta)[i.val],
      List.mem_flatMap.mpr ⟨_,List.getElem_mem ..,witnessBalancePackingBlockLabel_mem _ h⟩⟩,
      witnessBalancePackingBlockLabel_not_joint _ (List.getElem_mem ..) h⟩

theorem witnessBalancePackingBlockTarget_injective (k delta : ℕ) :
    Function.Injective (witnessBalancePackingBlockTarget k delta) := by
  intro i j hij
  apply Fin.ext
  apply (List.Nodup.getElem_inj_iff (witnessBalance_packing_blocks_nodup k delta)).mp
  unfold witnessBalancePackingBlockTarget at hij
  by_cases hi : (witnessBalancePackingBlocks k delta)[i.val]=.joint <;>
    by_cases hj : (witnessBalancePackingBlocks k delta)[j.val]=.joint
  · rw [hi,hj]
  · rw [dif_pos hi,dif_neg hj] at hij
    exact absurd hij Sum.inl_ne_inr
  · rw [dif_neg hi,dif_pos hj] at hij
    exact absurd hij Sum.inr_ne_inl
  · rw [dif_neg hi,dif_neg hj] at hij
    have hl := congrArg (fun a : witnessBalancePackingRestIndex k delta => a.val.val) (Sum.inr.inj hij)
    exact witnessBalancePackingBlockLabel_injective _ _ hi hj hl

theorem witnessBalancePackingBlockTarget_surjective (k delta : ℕ) :
    Function.Surjective (witnessBalancePackingBlockTarget k delta) := by
  intro x
  rcases x with ⟨⟩ | a
  · have hpos : 0<(witnessBalancePackingBlocks k delta).length := by
      simp [witnessBalancePackingBlocks]
    have h0 : (witnessBalancePackingBlocks k delta)[0]=.joint := by
      simp [witnessBalancePackingBlocks]
    exact ⟨⟨0,hpos⟩,dif_pos h0⟩
  · have hmem := a.val.property
    unfold witnessBalancePackingOriginalLabels at hmem
    obtain ⟨q,hq,ha⟩ := List.mem_flatMap.mp hmem
    have hqj : q≠.joint := by
      intro h
      subst h
      apply a.property
      simpa [witnessBalancePackingJointPredicate,witnessBalancePackingJointLabel,
        witnessBalancePackingLabels] using ha
    have hlab : witnessBalancePackingBlockLabel q=a.val.val := by
      cases q with
      | joint => exact absurd rfl hqj
      | tail =>
        simp only [witnessBalancePackingLabels,List.mem_singleton] at ha
        simp [witnessBalancePackingBlockLabel,ha]
      | early s =>
        simp only [witnessBalancePackingLabels,List.mem_singleton] at ha
        simp [witnessBalancePackingBlockLabel,ha]
    obtain ⟨i,hi,hiq⟩ := List.mem_iff_getElem.mp hq
    refine ⟨⟨i,hi⟩,?_⟩
    have hne : (witnessBalancePackingBlocks k delta)[i]≠.joint := by rw [hiq]; exact hqj
    unfold witnessBalancePackingBlockTarget
    rw [dif_neg hne]
    refine congrArg Sum.inr (Subtype.ext (Subtype.ext ?_))
    show witnessBalancePackingBlockLabel (witnessBalancePackingBlocks k delta)[i]=a.val.val
    rw [hiq]
    exact hlab

/-- The tower block index set is in bijection with joint ⊕ rest labels. -/
def witnessBalancePackingBlockBeta (k delta : ℕ) :
    TowerIdx (witnessBalancePackingBlocks k delta).length (witnessBalancePackingBlocks k delta).length ≃
      Unit ⊕ witnessBalancePackingRestIndex k delta :=
  (Equiv.subtypeUnivEquiv (fun i : Fin (witnessBalancePackingBlocks k delta).length => i.isLt)).trans
    (Equiv.ofBijective _ ⟨witnessBalancePackingBlockTarget_injective k delta,
      witnessBalancePackingBlockTarget_surjective k delta⟩)

section
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

private theorem degree_single (q : WitnessBalancePackingKind) (hq : q≠.joint) :
    witnessBalancePackingDegree hk z q=
      witnessBalanceComponentSize hk z (witnessBalancePackingBlockLabel q) := by
  cases q with
  | joint => exact absurd rfl hq
  | tail => simp [witnessBalancePackingDegree,witnessBalancePackingLabels,witnessBalancePackingBlockLabel]
  | early s => simp [witnessBalancePackingDegree,witnessBalancePackingLabels,witnessBalancePackingBlockLabel]

/-- The block degree equals the joint degree or the matching rest component size. -/
theorem witnessBalancePackingBlockTarget_card (hd : delta≤1)
    (i : Fin (witnessBalancePackingBlocks k delta).length) :
    witnessBalancePackingSelectedDegree hk z i=
      Sum.elim (fun _ : Unit => witnessBalancePackingJointDegree hk z)
        (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val)
        (witnessBalancePackingBlockTarget k delta i) := by
  refine (witnessBalance_packing_block_card hk z hd _ (List.getElem_mem ..)).symm.trans ?_
  unfold witnessBalancePackingBlockTarget
  by_cases h : (witnessBalancePackingBlocks k delta)[i.val]=.joint
  · rw [dif_pos h,h]
    simp [witnessBalancePackingDegree,witnessBalancePackingLabels,witnessBalancePackingJointDegree,
      witnessBalancePackingJointLabel]
  · rw [dif_neg h]
    exact degree_single hk z _ h

/-- Fiber relabelling of each tower block (only cardinalities matter). -/
def witnessBalancePackingBlockFiber (hd : delta≤1)
    (v : TowerIdx (witnessBalancePackingBlocks k delta).length (witnessBalancePackingBlocks k delta).length) :
    Fin (witnessBalancePackingSelectedDegree hk z v.val) ≃
      Fin (Sum.elim (fun _ : Unit => witnessBalancePackingJointDegree hk z)
        (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val)
        (witnessBalancePackingBlockBeta k delta v)) :=
  finCongr (witnessBalancePackingBlockTarget_card hk z hd v.val)

/-- The ordered block product relabelled to the physical joint/rest group. -/
def witnessBalancePackingBlockRelabel (hd : delta≤1) :=
  blockRelabel (witnessBalancePackingJointDegree hk z)
    (fun r : witnessBalancePackingRestIndex k delta => witnessBalanceComponentSize hk z r.val.val)
    (fun v : TowerIdx (witnessBalancePackingBlocks k delta).length
      (witnessBalancePackingBlocks k delta).length => witnessBalancePackingSelectedDegree hk z v.val)
    (witnessBalancePackingBlockBeta k delta) (witnessBalancePackingBlockFiber hk z hd)
end

/-- The original target injects into induction along the physical block hom of the
Pi tensor of all selected local Specht modules, from the same coherent guarded chain. -/
theorem paperWitness_balance_physical_tower_embedding (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ D : Fin ((witnessBalancePackingBlocks k delta).length+1) → YoungDiagram,
      D 0=⊥ ∧ D (Fin.last (witnessBalancePackingBlocks k delta).length)=mu ∧
    ∃ hc : ∀ i : Fin (witnessBalancePackingBlocks k delta).length,
      (D i.succ).card=(D i.castSucc).card+
        witnessBalancePackingSelectedDegree hp.staircase_bound z i,
    ∃ p : ∀ i, Nat.Partition (witnessBalancePackingSelectedDegree hp.staircase_bound z i),
      (∀ i, SizedStripChain
        (witnessBalancePackingParts hp.staircase_bound z (witnessBalancePackingBlocks k delta)[i.val])
        (D i.castSucc) (D i.succ) ∧
        (partitionDiagram (p i)).colLen 0≤(witnessBalancePackingParts hp.staircase_bound z
          (witnessBalancePackingBlocks k delta)[i.val]).length) ∧
    ∃ E : Representation.IntertwiningMap (spechtRep s)
      (Representation.ind (witnessBalancePackingCoarserHom hp.staircase_bound z hp.parity)
        ((towerRep (witnessBalancePackingSelectedDegree hp.staircase_bound z)
          (fun i => spechtRep (partitionTableau (p i)))
          (witnessBalancePackingBlocks k delta).length).comp
            (witnessBalancePackingBlockRelabel hp.staircase_bound z hp.parity).symm.toMonoidHom)),
      Function.Injective E := by
  obtain ⟨D,hzero,hlast,hc,h0,p,hrows,E,hE⟩ :=
    paperWitness_balance_pi_tower_embedding k b delta hp z s hprefix
  refine ⟨D,hzero,hlast,hc,p,hrows,?_⟩
  have hcard : mu.card=n := by
    have he := Fintype.card_congr s
    simpa using he.symm
  subst hlast
  subst hcard
  let M := tableauSpechtMap s (shapeTableau (D (Fin.last (witnessBalancePackingBlocks k delta).length)))
  have hM : Function.Injective M := (tableauSpechtMap_bijective _ _).1
  have hY : ∀ h x, towerHom (fun j => (D j).card)
      (witnessBalancePackingSelectedDegree hp.staircase_bound z) hc h0
      (Fin.last (witnessBalancePackingBlocks k delta).length) h
        ((towerPos (fun j => (D j).card) (witnessBalancePackingSelectedDegree hp.staircase_bound z) hc h0
          (Fin.last (witnessBalancePackingBlocks k delta).length)).symm x) =
      (towerPos (fun j => (D j).card) (witnessBalancePackingSelectedDegree hp.staircase_bound z) hc h0
          (Fin.last (witnessBalancePackingBlocks k delta).length)).symm
        (Equiv.sigmaCongrRight h x) := by
    intro h x
    rw [towerHom_apply,Equiv.apply_symm_apply]
  have hphi := fun h => blockHom_conj (witnessBalancePackingJointDegree hp.staircase_bound z)
    (fun r : witnessBalancePackingRestIndex k delta =>
      witnessBalanceComponentSize hp.staircase_bound z r.val.val)
    (fun v : TowerIdx (witnessBalancePackingBlocks k delta).length
      (witnessBalancePackingBlocks k delta).length =>
        witnessBalancePackingSelectedDegree hp.staircase_bound z v.val)
    (witnessBalancePackingBlockBeta k delta)
    (witnessBalancePackingBlockFiber hp.staircase_bound z hp.parity)
    (towerPos (fun j => (D j).card) (witnessBalancePackingSelectedDegree hp.staircase_bound z) hc h0
      (Fin.last (witnessBalancePackingBlocks k delta).length))
    (witnessBalancePackingCoarserPositions hp.staircase_bound z hp.parity)
    (towerHom (fun j => (D j).card) (witnessBalancePackingSelectedDegree hp.staircase_bound z) hc h0
      (Fin.last (witnessBalancePackingBlocks k delta).length))
    (witnessBalancePackingCoarserHom hp.staircase_bound z hp.parity) hY
    (fun k' z' => witnessBalancePackingCoarserHom_value hp.staircase_bound z hp.parity k' z') h
  exact ⟨(inducedRelabel _ _ _ _ _ hphi).comp (E.comp M),
    (inducedRelabel_bijective _ _ _ _ _ hphi).1.comp (hE.comp hM)⟩

end
end HSTZ
#print axioms HSTZ.witnessBalancePackingBlockTarget_injective
#print axioms HSTZ.witnessBalancePackingBlockTarget_surjective
#print axioms HSTZ.witnessBalancePackingBlockTarget_card
#print axioms HSTZ.paperWitness_balance_physical_tower_embedding
