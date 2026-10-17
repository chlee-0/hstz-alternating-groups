import HSTZ.InducedPiTower
import HSTZ.WitnessBalancePackingGuardedTypes
import HSTZ.WitnessBalancePackingSelectedPrefix

/-! The witness LR boundary chain assembled by the generic ordered tower.
The guarded boundary induction supplies D, the cardinality identities, local
partitions with the packing height guards, and every one-step injection;
`tower_embedding` turns them into one injection of the final boundary Specht module
into induction from the ordered product of all local block groups, acting on explicit
block positions, of the Pi tensor of all selected local Specht modules. Alignment
with the physical `CoarserHom` is a separate step. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

/-- Ordered Young-subgroup support of the final boundary, from the same coherent
guarded chain. -/
theorem paperWitness_balance_pi_tower_embedding (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ D : Fin ((witnessBalancePackingBlocks k delta).length+1) → YoungDiagram,
      D 0=⊥ ∧ D (Fin.last (witnessBalancePackingBlocks k delta).length)=mu ∧
    ∃ hc : ∀ i : Fin (witnessBalancePackingBlocks k delta).length,
      (D i.succ).card=(D i.castSucc).card+
        witnessBalancePackingSelectedDegree hp.staircase_bound z i,
    ∃ h0 : (D 0).card=0,
    ∃ p : ∀ i, Nat.Partition (witnessBalancePackingSelectedDegree hp.staircase_bound z i),
      (∀ i, SizedStripChain
        (witnessBalancePackingParts hp.staircase_bound z (witnessBalancePackingBlocks k delta)[i.val])
        (D i.castSucc) (D i.succ) ∧
        (partitionDiagram (p i)).colLen 0≤(witnessBalancePackingParts hp.staircase_bound z
          (witnessBalancePackingBlocks k delta)[i.val]).length) ∧
    ∃ E : Representation.IntertwiningMap
      (spechtRep (shapeTableau (D (Fin.last (witnessBalancePackingBlocks k delta).length))))
      (Representation.ind
        (towerHom (fun j => (D j).card) (witnessBalancePackingSelectedDegree hp.staircase_bound z)
          hc h0 (Fin.last (witnessBalancePackingBlocks k delta).length))
        (towerRep (witnessBalancePackingSelectedDegree hp.staircase_bound z)
          (fun i => spechtRep (partitionTableau (p i)))
          (Fin.last (witnessBalancePackingBlocks k delta).length).val)),
      Function.Injective E := by
  obtain ⟨D,hzero,hlast,hsteps⟩ := paperWitness_balance_guarded_boundary_induction k b delta hp z s hprefix
  choose hc p hh E hE using (fun i => (hsteps i).2)
  have h0 : (D 0).card=0 := by
    rw [hzero]
    rfl
  refine ⟨D,hzero,hlast,hc,h0,p,fun i => ⟨(hsteps i).1,hh i⟩,?_⟩
  haveI : Representation.IsIrreducible
      ((fun j => spechtRep (shapeTableau (D j))) 0) := specht_irreducible _
  let v0 : Specht (shapeTableau (D 0)) := ⟨polytabloid (shapeTableau (D 0)),mem_cyclic _ _⟩
  have hv0 : v0≠0 := fun h => polytabloid_ne_zero _ (congrArg Subtype.val h)
  exact tower_embedding (fun j => (D j).card) (witnessBalancePackingSelectedDegree hp.staircase_bound z)
    hc h0 (fun i => spechtRep (partitionTableau (p i)))
    (fun j => spechtRep (shapeTableau (D j))) v0 hv0 (fun i => ⟨E i,hE i⟩)
    (Fin.last (witnessBalancePackingBlocks k delta).length)

end
end HSTZ
#print axioms HSTZ.paperWitness_balance_pi_tower_embedding
