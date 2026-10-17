import HSTZ.WitnessFirstRowRotation
import HSTZ.WitnessMarkedCells

/-! Row-preserving rotation of the asymmetric witness.
Uses the first-row and marked-cell interfaces together with geometry from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). Attachment tails are kept; no global
shuffle phase is asserted. -/
namespace HSTZ
open OAI.Saxl

def witnessRowTailForward (q c : ℕ) : ℕ :=
  if c<q then c+2 else if c<q+2 then c-q else c
def witnessRowTailBackward (q a : ℕ) : ℕ :=
  if a<2 then a+q else if a<q+2 then a-2 else a

theorem witnessRowTailBackward_forward (q c : ℕ) :
    witnessRowTailBackward q (witnessRowTailForward q c)=c := by
  unfold witnessRowTailForward
  split_ifs <;> unfold witnessRowTailBackward <;> split_ifs <;> omega
theorem witnessRowTailForward_backward (q a : ℕ) :
    witnessRowTailForward q (witnessRowTailBackward q a)=a := by
  unfold witnessRowTailBackward
  split_ifs <;> unfold witnessRowTailForward <;> split_ifs <;> omega

def witnessRowForward (k b r c : ℕ) : ℕ :=
  if r=0 then witnessFirstRowForward k b c else witnessRowTailForward (k-2-r) c
def witnessRowBackward (k b r a : ℕ) : ℕ :=
  if r=0 then witnessFirstRowBackward k b a else witnessRowTailBackward (k-2-r) a

def witnessRowRotateCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    (witnessDiagram k b delta hk).cells :=
  ⟨(x.val.1,witnessRowForward k b x.val.1 x.val.2),by
    have hx : x.val.2<witnessRow k b delta x.val.1 := by
      simpa only [witnessDiagram_row_length] using YoungDiagram.mem_iff_lt_rowLen.mp x.property
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    rw [witnessDiagram_row_length]
    by_cases hr : x.val.1=0
    · have hc : x.val.2<k+b+delta := by simpa [witnessRow,hr,Nat.add_assoc] using hx
      have hb := (witnessFirstRowRotate k b delta hk ⟨x.val.2,hc⟩).isLt
      change witnessFirstRowForward k b x.val.2<k+b+delta at hb
      simpa [witnessRowForward,witnessRow,hr,Nat.add_assoc] using hb
    · unfold witnessRow at hx
      unfold witnessRowForward witnessRow witnessRowTailForward
      simp only [if_neg hr] at hx ⊢
      split_ifs at hx ⊢ <;> omega⟩

def witnessRowUnrotateCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    (witnessDiagram k b delta hk).cells :=
  ⟨(x.val.1,witnessRowBackward k b x.val.1 x.val.2),by
    have hx : x.val.2<witnessRow k b delta x.val.1 := by
      simpa only [witnessDiagram_row_length] using YoungDiagram.mem_iff_lt_rowLen.mp x.property
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    rw [witnessDiagram_row_length]
    by_cases hr : x.val.1=0
    · have hc : x.val.2<k+b+delta := by simpa [witnessRow,hr,Nat.add_assoc] using hx
      have hb := (witnessFirstRowUnrotate k b delta hk ⟨x.val.2,hc⟩).isLt
      change witnessFirstRowBackward k b x.val.2<k+b+delta at hb
      simpa [witnessRowBackward,witnessRow,hr,Nat.add_assoc] using hb
    · unfold witnessRow at hx
      unfold witnessRowBackward witnessRow witnessRowTailBackward
      simp only [if_neg hr] at hx ⊢
      split_ifs at hx ⊢ <;> omega⟩

def witnessRowRotation (k b delta : ℕ) (hk : 5 ≤ k) :
    Equiv.Perm (witnessDiagram k b delta hk).cells where
  toFun:=witnessRowRotateCell k b delta hk
  invFun:=witnessRowUnrotateCell k b delta hk
  left_inv x:=by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change witnessRowBackward k b x.val.1 (witnessRowForward k b x.val.1 x.val.2)=x.val.2
      by_cases hr : x.val.1=0
      · have hc : x.val.2<k+b+delta := by
          have hx:=YoungDiagram.mem_iff_lt_rowLen.mp x.property
          simpa [witnessDiagram_row_length,witnessRow,hr,Nat.add_assoc] using hx
        simpa only [witnessRowBackward,witnessRowForward,if_pos hr] using
          witnessFirstRowBackward_forward k b delta x.val.2 hk hc
      · simpa only [witnessRowBackward,witnessRowForward,if_neg hr] using
          witnessRowTailBackward_forward (k-2-x.val.1) x.val.2
  right_inv x:=by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change witnessRowForward k b x.val.1 (witnessRowBackward k b x.val.1 x.val.2)=x.val.2
      by_cases hr : x.val.1=0
      · have hc : x.val.2<k+b+delta := by
          have hx:=YoungDiagram.mem_iff_lt_rowLen.mp x.property
          simpa [witnessDiagram_row_length,witnessRow,hr,Nat.add_assoc] using hx
        simpa only [witnessRowForward,witnessRowBackward,if_pos hr] using
          witnessFirstRowForward_backward k b delta x.val.2 hk hc
      · simpa only [witnessRowForward,witnessRowBackward,if_neg hr] using
          witnessRowTailForward_backward (k-2-x.val.1) x.val.2

end HSTZ
#print axioms HSTZ.witnessRowTailBackward_forward
#print axioms HSTZ.witnessRowTailForward_backward
#print axioms HSTZ.witnessRowRotation
