import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalanceNeighborWords

/-! The complete-neighbor Specht module in the original component `C_a`.
Reuses the cyclic image APIs, building on OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The finite position equivalence and the same prescribed generator are retained. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (s : ℕ)
    (hs : 2*s+1<k-(2+delta))
include hs

private theorem neighbor_carrier_mem
    (x : Specht (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))) :
    witnessBalanceNeighborWordMap hk z s hs x.val ∈
      (witnessBalanceComponentRows hk z (3+s)).toSubmodule := by
  have hx : x.val ∈ cyclicSpan (wordRep _ _)
      (polytabloid (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))) := x.property
  have he := cyclicSpan_apply_mem (witnessBalanceNeighborWordMap hk z s hs)
    (polytabloid (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))) hx
  rw [witnessBalanceNeighborWordMap_generator] at he
  rw [cyclicSpan_comp_surjective _ _
    (positionPermHom_bijective (witnessBalanceNeighborPositions hk z s hs)).2] at he
  exact he

/-- The full native local Specht module maps into the full component cyclic
carrier. -/
def witnessBalanceNeighborSpechtMap : Representation.IntertwiningMap
    (spechtRep (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)))
    ((witnessBalanceComponentRows hk z (3+s)).toRepresentation.comp
      (positionPermHom (witnessBalanceNeighborPositions hk z s hs))) where
  toLinearMap := ((witnessBalanceNeighborWordMap hk z s hs).toLinearMap.domRestrict
    (spechtSub (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s))).toSubmodule).codRestrict
      (witnessBalanceComponentRows hk z (3+s)).toSubmodule (neighbor_carrier_mem hk z s hs)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessBalanceNeighborWordMap hk z s hs).map_action g x.val

theorem witnessBalanceNeighborSpechtMap_injective :
    Function.Injective (witnessBalanceNeighborSpechtMap hk z s hs) := by
  intro x y h
  apply Subtype.ext
  exact witnessBalanceNeighborWordMap_injective hk z s hs (congrArg Subtype.val h)

theorem witnessBalanceNeighborSpechtMap_generator :
    (witnessBalanceNeighborSpechtMap hk z s hs
      ⟨polytabloid (balanceNeighborTableau (witnessBalanceNeighborSize (k:=k) s)),mem_cyclic _ _⟩).val=
        witnessBalanceComponentWord hk z (3+s) :=
  witnessBalanceNeighborWordMap_generator hk z s hs

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceNeighborSpechtMap
#print axioms HSTZ.witnessBalanceNeighborSpechtMap_injective
#print axioms HSTZ.witnessBalanceNeighborSpechtMap_generator
