import HSTZ.WitnessBalanceComponentFactor
import HSTZ.BandPath

/-! The original H-cyclic carrier, built from independent component and remaining
factors. Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This does not identify the whole restricted Specht module. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (a : ℕ)

abbrev witnessBalanceOtherGroup := fiberGroup
  (fun i : Fin (witnessBalanceOtherSize hk z a) =>
    witnessBalanceLabel hk z ((witnessBalanceComponentCut hk z a).symm (.inr i)))

private theorem balanceComponentSector (g : witnessBalanceGroup hk z) :
    g.val∈sectorGroup (fun i => (witnessBalanceComponentCut hk z a i).isLeft=true) := by
  intro i
  change (witnessBalanceComponentCut hk z a (g.val i)).isLeft=true ↔
    (witnessBalanceComponentCut hk z a i).isLeft=true
  rw [witnessBalanceComponentCut_mask,witnessBalanceComponentCut_mask]
  rw [g.property i]

def witnessBalanceComponentHom :
    (Equiv.Perm (Fin (witnessBalanceComponentSize hk z a)) × witnessBalanceOtherGroup hk z a) →*
      witnessBalanceGroup hk z where
  toFun gh := ⟨sumPerm (witnessBalanceComponentCut hk z a) gh.1 gh.2.val,by
    have hp : gh.1∈fiberGroup (fun i => witnessBalanceLabel hk z
        ((witnessBalanceComponentCut hk z a).symm (.inl i))) := by
      intro i
      change witnessBalanceLabel hk z ((witnessBalanceComponentCut hk z a).symm (.inl (gh.1 i)))=
        witnessBalanceLabel hk z ((witnessBalanceComponentCut hk z a).symm (.inl i))
      exact (witnessBalanceComponentCut_left hk z a (gh.1 i)).trans
        (witnessBalanceComponentCut_left hk z a i).symm
    exact (fiberSplit (witnessBalanceComponentCut hk z a) (witnessBalanceLabel hk z)
      (⟨gh.1,hp⟩,gh.2)).property.1⟩
  map_one' := Subtype.ext ((sumPermHom (witnessBalanceComponentCut hk z a)).map_one)
  map_mul' gh pq := Subtype.ext ((sumPermHom (witnessBalanceComponentCut hk z a)).map_mul
    (gh.1,gh.2.val) (pq.1,pq.2.val))

theorem witnessBalanceComponentHom_value (gh) :
    (witnessBalanceComponentHom hk z a gh).val=
      sumPermHom (witnessBalanceComponentCut hk z a) (gh.1,gh.2.val) := rfl

theorem witnessBalanceComponentHom_bijective : Function.Bijective (witnessBalanceComponentHom hk z a) := by
  constructor
  · intro p q h
    have hh : sumPerm (witnessBalanceComponentCut hk z a) p.1 p.2.val =
        sumPerm (witnessBalanceComponentCut hk z a) q.1 q.2.val :=
      congrArg (fun u : witnessBalanceGroup hk z => u.val) h
    have he : (p.1,p.2.val)=(q.1,q.2.val) :=
      @sumPerm_injective n (witnessBalanceComponentSize hk z a)
        (witnessBalanceOtherSize hk z a) (witnessBalanceComponentCut hk z a)
        (p.1,p.2.val) (q.1,q.2.val) hh
    apply Prod.ext
    · exact congrArg (fun r : Equiv.Perm (Fin (witnessBalanceComponentSize hk z a)) ×
        Equiv.Perm (Fin (witnessBalanceOtherSize hk z a)) => r.1) he
    · apply Subtype.ext
      exact congrArg (fun r : Equiv.Perm (Fin (witnessBalanceComponentSize hk z a)) ×
        Equiv.Perm (Fin (witnessBalanceOtherSize hk z a)) => r.2) he
  · intro g
    let g' : ↥(fiberGroup (witnessBalanceLabel hk z) ⊓
        sectorGroup (fun i => (witnessBalanceComponentCut hk z a i).isLeft=true)) :=
      ⟨g.val,⟨g.property,balanceComponentSector hk z a g⟩⟩
    let E := fiberSplit (witnessBalanceComponentCut hk z a) (witnessBalanceLabel hk z)
    let p := E.symm g'
    refine ⟨(p.1.val,p.2),Subtype.ext ?_⟩
    change sumPerm (witnessBalanceComponentCut hk z a) p.1.val p.2.val=g.val
    exact congrArg (fun u : ↥(fiberGroup (witnessBalanceLabel hk z) ⊓
      sectorGroup (fun i => (witnessBalanceComponentCut hk z a i).isLeft=true)) => u.val)
      (E.apply_symm_apply g')

abbrev witnessBalanceComponentRows := cyclicSubrepresentation
  (wordRep (witnessBalanceComponentSize hk z a) ((witnessDiagram k b delta hk).colLen 0))
  (witnessBalanceComponentWord hk z a)

abbrev witnessBalanceOtherRows := cyclicSubrepresentation
  ((wordRep (witnessBalanceOtherSize hk z a) ((witnessDiagram k b delta hk).colLen 0)).comp
    (witnessBalanceOtherGroup hk z a).subtype) (witnessBalanceOtherWord hk z a)

def witnessBalanceComponentPositionMap : Representation.IntertwiningMap
    (independentTensor
      (wordRep (witnessBalanceComponentSize hk z a) ((witnessDiagram k b delta hk).colLen 0))
      ((wordRep (witnessBalanceOtherSize hk z a) ((witnessDiagram k b delta hk).colLen 0)).comp
        (witnessBalanceOtherGroup hk z a).subtype))
    (((wordRep n ((witnessDiagram k b delta hk).colLen 0)).comp (witnessBalanceGroup hk z).subtype).comp
      (witnessBalanceComponentHom hk z a)) where
  toLinearMap := (positionTensor (witnessBalanceComponentCut hk z a)).toLinearMap
  isIntertwining' gh := LinearMap.ext fun v =>
    positionTensor_equivariant (witnessBalanceComponentCut hk z a) gh.1 gh.2.val v

/-- The image in the same original C, with the remaining-label group. -/
theorem witnessBalance_component_carrier_image :
    (LinearMap.range (TensorProduct.mapIncl
      (witnessBalanceComponentRows hk z a).toSubmodule
      (witnessBalanceOtherRows hk z a).toSubmodule)).map
      (positionTensor (witnessBalanceComponentCut hk z a)).toLinearMap =
        (witnessBalanceLocalRows hk z).toSubmodule := by
  change (LinearMap.range (TensorProduct.mapIncl
    (cyclicSpan (wordRep (witnessBalanceComponentSize hk z a) ((witnessDiagram k b delta hk).colLen 0))
      (witnessBalanceComponentWord hk z a))
    (cyclicSpan ((wordRep (witnessBalanceOtherSize hk z a) ((witnessDiagram k b delta hk).colLen 0)).comp
      (witnessBalanceOtherGroup hk z a).subtype) (witnessBalanceOtherWord hk z a)))).map _ = _
  rw [cyclic_tensor_range_eq]
  have he := cyclicSpan_image (witnessBalanceComponentPositionMap hk z a)
    (witnessBalanceComponentWord hk z a ⊗ₜ[ℂ] witnessBalanceOtherWord hk z a)
  rw [show witnessBalanceComponentPositionMap hk z a
      (witnessBalanceComponentWord hk z a ⊗ₜ[ℂ] witnessBalanceOtherWord hk z a)=polytabloid z from
        witnessBalance_component_tensor hk z a] at he
  exact he.trans (cyclicSpan_comp_surjective
    ((wordRep n ((witnessDiagram k b delta hk).colLen 0)).comp (witnessBalanceGroup hk z).subtype)
    (witnessBalanceComponentHom hk z a) (witnessBalanceComponentHom_bijective hk z a).2 (polytabloid z))

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceComponentHom_value
#print axioms HSTZ.witnessBalanceComponentHom_bijective
#print axioms HSTZ.witnessBalanceComponentPositionMap
#print axioms HSTZ.witnessBalance_component_carrier_image
