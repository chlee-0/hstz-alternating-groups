import HSTZ.WitnessSelectedFactors
import HSTZ.BandPath

/-! Row and column fibers and letters of the selected path, identified with the
native path layers. Uses the path alternation and letter transport from OpenAI's
`math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessLowColumnLetter (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin 2 ↪ Fin ((witnessDiagram k b delta hk).colLen 0) where
  toFun i := ⟨i.val,by rw [witnessDiagram_height]; have hi := i.isLt; omega⟩
  inj' := by intro i j he; exact Fin.ext (congrArg (fun x : Fin ((witnessDiagram k b delta hk).colLen 0) => x.val) he)

theorem witness_native_path_row_group (k b delta : ℕ) (hk : 5 ≤ k) :
    fiberGroup (fun i : Fin (witnessPathSize k) =>
      (witnessPathPositionCell k b delta hk i).val.1)=
      fiberGroup (@PathLayer.tag ((k-2)+1)) := by
  have he := bandRow_path_group (k-2)
  change fiberGroup (fun i => (bandTableau (k-2) 2 (bandPathEquiv (k-2) i)).val.1)=_ at he
  simpa only [witnessPathPositionCell_band,witnessBandPositionCell_row] using he

theorem witness_native_path_column_group (k b delta : ℕ) (hk : 5 ≤ k) :
    fiberGroup (fun i : Fin (witnessPathSize k) =>
      (witnessPathPositionCell k b delta hk i).val.2)=
      fiberGroup (fun i => PathLayer.tag (Fin.rev i)) := by
  ext g
  change (∀ i, (witnessPathPositionCell k b delta hk (g i)).val.2=
    (witnessPathPositionCell k b delta hk i).val.2) ↔
    (∀ i, PathLayer.tag (Fin.rev (g i))=PathLayer.tag (Fin.rev i))
  have hh (i j : Fin (witnessPathSize k)) :
      (witnessPathPositionCell k b delta hk i).val.2=
        (witnessPathPositionCell k b delta hk j).val.2 ↔
      PathLayer.tag (Fin.rev i)=PathLayer.tag (Fin.rev j) := by
    rw [witnessPathPositionCell_band,witnessPathPositionCell_band,
      witnessBandPositionCell_column_eq_iff]
    rw [bandPath_coordinates,bandPath_coordinates]
    change i.val/2=j.val/2 ↔ _
    simp only [PathLayer.tag,Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    change i.val<2*((k-2)+1)+1 at hi
    change j.val<2*((k-2)+1)+1 at hj
    unfold witnessPathSize
    omega
  exact ⟨fun h i => (hh (g i) i).mp (h i),fun h i => (hh (g i) i).mpr (h i)⟩

theorem witness_native_path_column_base (k b delta : ℕ) (hk : 5 ≤ k) :
    witnessPathColumnBase k b delta hk=
      fun i => witnessLowColumnLetter k b delta hk (PathLayer.base (Fin.rev i)) := by
  funext i
  apply Fin.ext
  rw [witnessPathColumnBase_all]
  change (if i=witnessPathEndpoint k then 0 else (i.val+1)%2)=
    (PathLayer.base (Fin.rev i)).val
  have hi := i.isLt
  change i.val<2*((k-2)+1)+1 at hi
  have hv : (Fin.rev i).val=2*((k-2)+1)-i.val := by
    simp only [Fin.val_rev]
    unfold witnessPathSize
    omega
  have hb : (PathLayer.base (Fin.rev i)).val=
      if (Fin.rev i).val=0 then 0 else ((Fin.rev i).val+1)%2 := by
    unfold PathLayer.base
    split_ifs <;> rfl
  rw [hb,hv]
  by_cases he : i=witnessPathEndpoint k
  · subst i
    change (if witnessPathEndpoint k=witnessPathEndpoint k then 0 else _)=
      if 2*((k-2)+1)-2*((k-2)+1)=0 then 0 else _
    simp
  · have hn : i.val≠2*((k-2)+1) := by
      intro h; exact he (Fin.ext h)
    rw [if_neg he]
    split_ifs <;> omega

theorem witness_native_path_row_word (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessSelectedPathRowWord k b delta hp=
      letterLift (witnessLowRowLetter k b delta hp.staircase_bound)
        (PathLayer.rowAlt ((k-2)+1)) := by
  unfold witnessSelectedPathRowWord
  rw [witness_native_path_row_group]
  change altWord _ (fun i => witnessExchangedRowBase k b delta hp.staircase_bound
    (paperWitness_attachment_positive k b delta hp) (witnessComplementOrder k b delta (.inl i)))=_
  rw [witnessExchangedRowBase_path]
  change altWord _ ((witnessLowRowLetter k b delta hp.staircase_bound) ∘ PathLayer.base)=_
  rw [← letterLift_altWord]
  rfl

theorem witness_native_path_column_word (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessSelectedPathColumnWord k b delta hp=
      letterLift (witnessLowColumnLetter k b delta hp.staircase_bound)
        (wordRep _ 2 Fin.revPerm (PathLayer.rowAlt ((k-2)+1))) := by
  unfold witnessSelectedPathColumnWord
  rw [witness_native_path_column_group]
  have hb : leftWord (witnessComplementOrder k b delta).symm
      (witnessComplementColumnBase k b delta hp.staircase_bound)=
      witnessPathColumnBase k b delta hp.staircase_bound := by
    funext i
    exact witnessComplementColumnBase_path k b delta hp.staircase_bound i
  rw [hb,witness_native_path_column_base]
  change altWord _ ((witnessLowColumnLetter k b delta hp.staircase_bound) ∘
    (PathLayer.base ∘ Fin.revPerm))=_
  rw [← letterLift_altWord]
  congr 1
  funext w
  have he := altWord_fiber_relabel (Fin.revPerm : Fin (witnessPathSize k) ≃ _)
    (@PathLayer.tag ((k-2)+1)) (@PathLayer.base ((k-2)+1)) w
  simpa [PathLayer.rowAlt,wordRep,Function.comp_def,Fin.revPerm] using he.symm

end
end HSTZ
#print axioms HSTZ.witness_native_path_row_group
#print axioms HSTZ.witness_native_path_column_group
#print axioms HSTZ.witness_native_path_column_base
#print axioms HSTZ.witness_native_path_row_word
#print axioms HSTZ.witness_native_path_column_word
