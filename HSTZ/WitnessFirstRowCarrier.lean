import HSTZ.WitnessFirstRowFunctions

/-! Typed first-row permutation and its inverse on the witness width.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0);
no permutation between unequal alphabets is used. -/
namespace HSTZ

def witnessFirstRowRotate (k b delta : ℕ) (hk : 5 ≤ k)
    (c : Fin (k+b+delta)) : Fin (k+b+delta) :=
  ⟨witnessFirstRowForward k b c.val, by
    have hc:=c.isLt
    unfold witnessFirstRowForward
    split_ifs <;> omega⟩

def witnessFirstRowUnrotate (k b delta : ℕ) (hk : 5 ≤ k)
    (a : Fin (k+b+delta)) : Fin (k+b+delta) :=
  ⟨witnessFirstRowBackward k b a.val, by
    have ha:=a.isLt
    unfold witnessFirstRowBackward
    split_ifs <;> omega⟩

def witnessFirstRowRotation (k b delta : ℕ) (hk : 5 ≤ k) :
    Equiv.Perm (Fin (k+b+delta)) where
  toFun:=witnessFirstRowRotate k b delta hk
  invFun:=witnessFirstRowUnrotate k b delta hk
  left_inv c:=by
    have hc:=c.isLt
    apply Fin.ext
    change witnessFirstRowBackward k b (witnessFirstRowForward k b c.val)=c.val
    exact witnessFirstRowBackward_forward k b delta c.val hk hc
  right_inv a:=by
    have ha:=a.isLt
    apply Fin.ext
    change witnessFirstRowForward k b (witnessFirstRowBackward k b a.val)=a.val
    exact witnessFirstRowForward_backward k b delta a.val hk ha

end HSTZ
#print axioms HSTZ.witnessFirstRowRotation
