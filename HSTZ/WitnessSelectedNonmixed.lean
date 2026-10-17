import HSTZ.WitnessFactorAlphabets

/-! Mixed terms of the selected complement vanish for covectors that annihilate
the opposite alphabets. The covector hypothesis is explicit: the existence of a
common flag, full unprojected separation and nonvanishing of the surviving
contraction are not proved in this file. Uses `wordMap` and `altWord` adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- A target row-letter assignment matches the original cut. -/
def witnessFlagMatches {d : ℕ} (k b delta : ℕ) (ell : Fin d → Prop)
    (a : Fin (witnessComplementSize k b delta) → Fin d) : Prop :=
  ∀ i, ell (a i) ↔ witnessComplementPathMask k b delta i

/-- Opposite-alphabet annihilation, only on low-column letters. -/
def witnessFlagSeparated {d : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (ell : Fin d → Prop)
    (L : Fin d → Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
      (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ) : Prop :=
  ∀ j v, (finProdFinEquiv.symm v).2.val<2 →
    ¬((finProdFinEquiv.symm v).1.val<2 ↔ ell j) → L j v=0

def witnessSelectedFlagSum (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {mu : YoungDiagram} (t : Tableau (witnessComplementSize k b delta) mu)
    (ell : Fin (mu.colLen 0) → Prop)
    (L : Fin (mu.colLen 0) → Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ) : ℂ := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t, signC g.val *
    if witnessFlagMatches k b delta ell (rowWord t ∘ g.val.symm) then
      dotProduct (wordMap L (Pi.single (rowWord t ∘ g.val.symm) 1))
        (witnessSelectedComplementPairWord k b delta hp) else 0

end
end HSTZ
