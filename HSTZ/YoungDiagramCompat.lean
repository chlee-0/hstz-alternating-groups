import Mathlib.Combinatorics.Young.YoungDiagram

/-! The antitone column-length interface used by the HSTZ construction. -/

namespace YoungDiagram

theorem colLen_antitone (μ : YoungDiagram) : Antitone μ.colLen :=
  fun _ _ h => μ.colLen_anti _ _ h

theorem rowLen_antitone (μ : YoungDiagram) : Antitone μ.rowLen :=
  fun _ _ h => μ.rowLen_anti _ _ h

end YoungDiagram
