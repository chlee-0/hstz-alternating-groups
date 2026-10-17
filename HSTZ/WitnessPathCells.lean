import HSTZ.WitnessDiagram

/-! Endpoint relocation from the native two-band cells into the asymmetric witness.
This is geometry, not a selected-generator identity.
The column alphabet is embedded in the larger width; it is not permuted. -/
namespace HSTZ

abbrev WitnessNativeBandCells (k : ℕ) :=
  {c : ℕ × ℕ // k-2 ≤ c.1+c.2 ∧ c.1+c.2 < k-2+2}

def witnessPathColumn (k b delta : ℕ) (c : Fin k) : Fin (k+b+delta) :=
  ⟨if c.val=k-1 then k+b+delta-1 else c.val, by
    have hc := c.isLt
    split_ifs <;> omega⟩

theorem witnessPathColumn_injective (k b delta : ℕ) :
    Function.Injective (witnessPathColumn k b delta) := by
  intro i j he
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have he' := congrArg Fin.val he
  change (if i.val=k-1 then k+b+delta-1 else i.val) =
    (if j.val=k-1 then k+b+delta-1 else j.val) at he'
  split_ifs at he' <;> omega

theorem witnessNativeBandCell_bounds (k : ℕ) (hk : 5 ≤ k)
    (x : WitnessNativeBandCells k) : x.val.1+x.val.2 < k := by
  have hx := x.property
  omega

def witnessPathCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : WitnessNativeBandCells k) : (witnessDiagram k b delta hk).cells :=
  ⟨(x.val.1, (witnessPathColumn k b delta
    ⟨x.val.2, by have hx := witnessNativeBandCell_bounds k hk x; omega⟩).val), by
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    rw [witnessDiagram_row_length]
    have hx := witnessNativeBandCell_bounds k hk x
    change (if x.val.2=k-1 then k+b+delta-1 else x.val.2) <
      witnessRow k b delta x.val.1
    unfold witnessRow
    split_ifs <;> omega⟩

theorem witnessPathCell_row (k b delta : ℕ) (hk : 5 ≤ k)
    (x : WitnessNativeBandCells k) : (witnessPathCell k b delta hk x).val.1 = x.val.1 := rfl

theorem witnessPathCell_column_eq_iff (k b delta : ℕ) (hk : 5 ≤ k)
    (x y : WitnessNativeBandCells k) :
    (witnessPathCell k b delta hk x).val.2 = (witnessPathCell k b delta hk y).val.2 ↔
      x.val.2 = y.val.2 := by
  have hx := witnessNativeBandCell_bounds k hk x
  have hy := witnessNativeBandCell_bounds k hk y
  let a : Fin k := ⟨x.val.2, by omega⟩
  let b' : Fin k := ⟨y.val.2, by omega⟩
  change (witnessPathColumn k b delta a).val = (witnessPathColumn k b delta b').val ↔ _
  constructor
  · intro he
    exact congrArg Fin.val (witnessPathColumn_injective k b delta (Fin.ext he))
  · intro he
    have hh : a=b' := Fin.ext he
    rw [hh]

theorem witnessPathCell_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessPathCell k b delta hk) := by
  intro x y he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun c : (witnessDiagram k b delta hk).cells => c.val.1) he
  · exact (witnessPathCell_column_eq_iff k b delta hk x y).mp
      (congrArg (fun c : (witnessDiagram k b delta hk).cells => c.val.2) he)

def witnessNativeBandEndpoint (k : ℕ) (hk : 5 ≤ k) : WitnessNativeBandCells k :=
  ⟨(0,k-1), by constructor <;> omega⟩

theorem witnessPathCell_endpoint (k b delta : ℕ) (hk : 5 ≤ k) :
    (witnessPathCell k b delta hk (witnessNativeBandEndpoint k hk)).val =
      (0,k+b+delta-1) := by
  simp [witnessPathCell, witnessNativeBandEndpoint, witnessPathColumn]

theorem witnessNativeBandCell_endpoint_iff (k : ℕ) (hk : 5 ≤ k)
    (x : WitnessNativeBandCells k) : x.val.2=k-1 ↔ x.val=(0,k-1) := by
  have hx := witnessNativeBandCell_bounds k hk x
  constructor
  · intro he
    apply Prod.ext <;> dsimp <;> omega
  · intro he
    exact congrArg Prod.snd he

theorem witnessPathCell_unchanged (k b delta : ℕ) (hk : 5 ≤ k)
    (x : WitnessNativeBandCells k) (hx : x.val ≠ (0,k-1)) :
    (witnessPathCell k b delta hk x).val = x.val := by
  have hc : x.val.2 ≠ k-1 := mt (witnessNativeBandCell_endpoint_iff k hk x).mp hx
  apply Prod.ext
  · rfl
  · change (if x.val.2=k-1 then k+b+delta-1 else x.val.2) = x.val.2
    exact if_neg hc

end HSTZ
#print axioms HSTZ.witnessPathColumn_injective
#print axioms HSTZ.witnessPathCell_row
#print axioms HSTZ.witnessPathCell_column_eq_iff
#print axioms HSTZ.witnessPathCell_injective
#print axioms HSTZ.witnessPathCell_endpoint
#print axioms HSTZ.witnessNativeBandCell_endpoint_iff
#print axioms HSTZ.witnessPathCell_unchanged
