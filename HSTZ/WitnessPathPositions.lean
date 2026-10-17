import HSTZ.WitnessPathCells
import OAI.RepresentationTheory.Saxl.BandFactorization

/-! Original-band and ordered-path positions in the asymmetric witness.
The row and column fiber subgroups are kept under the full position group.
No projected witness vector or word alternant identity is asserted here. -/
namespace HSTZ
open OAI.Saxl

noncomputable def witnessBandPositionCell (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (bandSize (k-2) 2)) : (witnessDiagram k b delta hk).cells :=
  witnessPathCell k b delta hk (bandCellsEquiv (k-2) 2 i)

theorem witnessBandPositionCell_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessBandPositionCell k b delta hk) :=
  (witnessPathCell_injective k b delta hk).comp (bandCellsEquiv (k-2) 2).injective

theorem witnessBandPositionCell_row (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (bandSize (k-2) 2)) :
    (witnessBandPositionCell k b delta hk i).val.1 = (bandTableau (k-2) 2 i).val.1 := rfl

theorem witnessBandPositionCell_column_eq_iff (k b delta : ℕ) (hk : 5 ≤ k)
    (i j : Fin (bandSize (k-2) 2)) :
    (witnessBandPositionCell k b delta hk i).val.2 =
      (witnessBandPositionCell k b delta hk j).val.2 ↔
      (bandTableau (k-2) 2 i).val.2 = (bandTableau (k-2) 2 j).val.2 :=
  witnessPathCell_column_eq_iff k b delta hk
    (bandCellsEquiv (k-2) 2 i) (bandCellsEquiv (k-2) 2 j)

theorem witnessBand_rowGroup (k b delta : ℕ) (hk : 5 ≤ k) :
    fiberGroup (fun i => (witnessBandPositionCell k b delta hk i).val.1) =
      bandRowGroup (k-2) 2 := rfl

theorem witnessBand_columnGroup (k b delta : ℕ) (hk : 5 ≤ k) :
    fiberGroup (fun i => (witnessBandPositionCell k b delta hk i).val.2) =
      bandColumnGroup (k-2) 2 := by
  ext g
  change (∀ i, (witnessBandPositionCell k b delta hk (g i)).val.2 =
    (witnessBandPositionCell k b delta hk i).val.2) ↔
    (∀ i, (bandTableau (k-2) 2 (g i)).val.2 = (bandTableau (k-2) 2 i).val.2)
  constructor
  · intro hg i
    exact (witnessBandPositionCell_column_eq_iff k b delta hk (g i) i).mp (hg i)
  · intro hg i
    exact (witnessBandPositionCell_column_eq_iff k b delta hk (g i) i).mpr (hg i)

noncomputable def witnessPathPositionCell (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (2*((k-2)+1)+1)) : (witnessDiagram k b delta hk).cells :=
  witnessPathCell k b delta hk (pathCellsEquiv (k-2) i)

theorem witnessPathPositionCell_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessPathPositionCell k b delta hk) :=
  (witnessPathCell_injective k b delta hk).comp (pathCellsEquiv (k-2)).injective

theorem witnessPathPositionCell_band (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (2*((k-2)+1)+1)) :
    witnessPathPositionCell k b delta hk i =
      witnessBandPositionCell k b delta hk (bandPathEquiv (k-2) i) := by
  unfold witnessPathPositionCell witnessBandPositionCell bandPathEquiv
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]

theorem witnessPathPositionCell_endpoint (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessPathPositionCell k b delta hk
      ⟨2*((k-2)+1), by omega⟩).val = (0,k+b+delta-1) := by
  have he : (pathCellsEquiv (k-2) ⟨2*((k-2)+1), by omega⟩).val = (0,k-1) := by
    apply Prod.ext <;> dsimp [pathCellsEquiv] <;> omega
  have hc : pathCellsEquiv (k-2) ⟨2*((k-2)+1), by omega⟩ =
      witnessNativeBandEndpoint k hk := Subtype.ext he
  unfold witnessPathPositionCell
  rw [hc]
  exact witnessPathCell_endpoint k b delta hk

theorem witnessPathPosition_degree (k : ℕ) (hk : 5 ≤ k) :
    2*((k-2)+1)+1 = 2*k-1 := by omega

end HSTZ
#print axioms HSTZ.witnessBandPositionCell_injective
#print axioms HSTZ.witnessBandPositionCell_column_eq_iff
#print axioms HSTZ.witnessBand_rowGroup
#print axioms HSTZ.witnessBand_columnGroup
#print axioms HSTZ.witnessPathPositionCell_injective
#print axioms HSTZ.witnessPathPositionCell_band
#print axioms HSTZ.witnessPathPositionCell_endpoint
#print axioms HSTZ.witnessPathPosition_degree
