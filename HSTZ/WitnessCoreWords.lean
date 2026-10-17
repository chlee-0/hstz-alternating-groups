import HSTZ.WitnessRowPositions
import HSTZ.WitnessColumnPositions
import HSTZ.StaircaseRowGeometry

/-! Core coordinates of the rotated layers of the asymmetric witness.
Uses the word and sector interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0);
the HSTZ proofs are separate. The canonical core tableau is named explicitly;
no identification with the native `stairTableau` or a global shuffle is asserted. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev witnessCanonicalCore (k : ℕ) :
    Tableau (staircase (k-2)).card (staircase (k-2)) :=
  canonicalTableau (staircase (k-2)) rfl

def witnessCoreRowLetter (k b delta : ℕ) (hk : 5 ≤ k)
    (a : Fin ((staircase (k-2)).transpose.colLen 0)) :
    Fin ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  ⟨(witnessMarkedRowLetter k b delta hk
    ⟨a.val,by simpa only [YoungDiagram.colLen_transpose,staircase_row_length,Nat.sub_zero] using a.isLt⟩).val,
    by simpa only [YoungDiagram.colLen_transpose,witnessDiagram_width] using
       (witnessMarkedRowLetter k b delta hk
         ⟨a.val,by simpa only [YoungDiagram.colLen_transpose,staircase_row_length,Nat.sub_zero] using a.isLt⟩).isLt⟩

def witnessCoreColumnLetter (k b delta : ℕ) (hk : 5 ≤ k)
    (a : Fin ((staircase (k-2)).colLen 0)) :
    Fin ((witnessDiagram k b delta hk).colLen 0) :=
  ⟨a.val+2,by
    rw [witnessDiagram_height]
    have ha : a.val<k-2 := by simpa only [staircase_colLen,Nat.sub_zero] using a.isLt
    omega⟩

theorem witnessCoreRowLetter_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessCoreRowLetter k b delta hk) := by
  intro a z he
  have ha : a.val<k-2 := by simpa only [YoungDiagram.colLen_transpose,staircase_row_length,Nat.sub_zero] using a.isLt
  have hz : z.val<k-2 := by simpa only [YoungDiagram.colLen_transpose,staircase_row_length,Nat.sub_zero] using z.isLt
  have hv := congrArg
    (fun j : Fin ((witnessDiagram k b delta hk).transpose.colLen 0) => j.val) he
  have hh : (⟨a.val,ha⟩ : Fin (k-2))=⟨z.val,hz⟩ :=
    witnessMarkedRowLetter_injective k b delta hk (Fin.ext hv)
  apply Fin.ext
  exact congrArg (fun i : Fin (k-2) => i.val) hh

theorem witnessCoreColumnLetter_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessCoreColumnLetter k b delta hk) := by
  intro a z he
  have hh := congrArg Fin.val he
  change a.val+2=z.val+2 at hh
  exact Fin.ext (by omega)

def witnessCoreRowEmbedding (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin ((staircase (k-2)).transpose.colLen 0) ↪
      Fin ((witnessDiagram k b delta hk).transpose.colLen 0) :=
  ⟨witnessCoreRowLetter k b delta hk,witnessCoreRowLetter_injective k b delta hk⟩
def witnessCoreColumnEmbedding (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin ((staircase (k-2)).colLen 0) ↪ Fin ((witnessDiagram k b delta hk).colLen 0) :=
  ⟨witnessCoreColumnLetter k b delta hk,witnessCoreColumnLetter_injective k b delta hk⟩

theorem witnessCoreRowLetter_value (k b delta : ℕ) (hk : 5 ≤ k)
    (a : Fin ((staircase (k-2)).transpose.colLen 0)) :
    (witnessCoreRowLetter k b delta hk a).val=
      if a.val=k-3 then k+b-1 else a.val+2 := rfl

theorem witnessCoreColumnLetter_value (k b delta : ℕ) (hk : 5 ≤ k)
    (a : Fin ((staircase (k-2)).colLen 0)) :
    (witnessCoreColumnLetter k b delta hk a).val=a.val+2 := rfl

-- Every position of the ordered core, with the original witness caller.
theorem witness_core_row_word (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin (staircase (k-2)).card) :
    rowWord (transposeTableau t)
      ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
        ((witnessCutPositionEquiv k b delta hk t).symm (.inl i))) =
      witnessCoreRowLetter k b delta hk
        (rowWord (transposeTableau (witnessCanonicalCore k)) i) := by
  apply Fin.ext
  change (t ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
    ((witnessCutPositionEquiv k b delta hk t).symm (.inl i)))).val.2=_
  rw [witnessRowRotationPositions_cell,witnessCutPosition_core,witnessRowRotation_core]
  rfl

theorem witness_core_column_word (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin (staircase (k-2)).card) :
    rowWord t
      ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
        ((witnessCutPositionEquiv k b delta hk t).symm (.inl i))) =
      witnessCoreColumnLetter k b delta hk (rowWord (witnessCanonicalCore k) i) := by
  apply Fin.ext
  change (t ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
    ((witnessCutPositionEquiv k b delta hk t).symm (.inl i)))).val.1=_
  rw [witnessColumnRotationPositions_cell,witnessCutPosition_core,witnessColumnRotation_core]
  rfl

theorem witness_core_row_word_all (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    (fun i => rowWord (transposeTableau t)
      ((witnessRowRotationPositions k b delta hk t : Equiv.Perm (Fin n))
        ((witnessCutPositionEquiv k b delta hk t).symm (.inl i)))) =
      witnessCoreRowLetter k b delta hk ∘ rowWord (transposeTableau (witnessCanonicalCore k)) := by
  funext i
  exact witness_core_row_word k b delta hk t i

theorem witness_core_column_word_all (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    (fun i => rowWord t
      ((witnessColumnRotationPositions k b delta hk t : Equiv.Perm (Fin n))
        ((witnessCutPositionEquiv k b delta hk t).symm (.inl i)))) =
      witnessCoreColumnLetter k b delta hk ∘ rowWord (witnessCanonicalCore k) := by
  funext i
  exact witness_core_column_word k b delta hk t i

end
end HSTZ
#print axioms HSTZ.witnessCoreRowLetter_injective
#print axioms HSTZ.witnessCoreColumnLetter_injective
#print axioms HSTZ.witnessCoreRowLetter_value
#print axioms HSTZ.witnessCoreColumnLetter_value
#print axioms HSTZ.witness_core_row_word
#print axioms HSTZ.witness_core_column_word
#print axioms HSTZ.witness_core_row_word_all
#print axioms HSTZ.witness_core_column_word_all
