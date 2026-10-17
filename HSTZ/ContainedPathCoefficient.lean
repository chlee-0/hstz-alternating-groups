import HSTZ.ContainedPathColumnOrder
import HSTZ.FourRowSupport

/-! The coefficient of the prescribed consecutive-column path polytabloid.
Reuses the native matrix contraction from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This supplies a path coefficient, not a common separated flag. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem column_chain_degree (mu : YoungDiagram) {n : ℕ}
    (hn : n=mu.transpose.rowLens.sum) :
    Path.chainFunctional n 1 (wordMap
      (fun (i : Fin (mu.colLen 0)) (a : Fin 4) =>
        Band.conjugation (Band.basis i.val) (Path.parts a).1 (Path.parts a).2)
      (polytabloid ((finCongr hn).trans (Columns.columnTableau mu))))=
    Path.chainFunctional mu.transpose.rowLens.sum 1 (wordMap
      (fun (i : Fin (mu.colLen 0)) (a : Fin 4) =>
        Band.conjugation (Band.basis i.val) (Path.parts a).1 (Path.parts a).2)
      (polytabloid (Columns.columnTableau mu))) := by
  subst n
  rfl

private theorem column_path_coefficient (r : ℕ) (mu : YoungDiagram)
    (hn : (2*r+1)=mu.transpose.rowLens.sum) (hmu : mu.colLen 0≤4) :
    dotProduct (wordMap
      (fun (i : Fin (mu.colLen 0)) (a : Fin 4) =>
        Band.conjugation (Band.basis i.val) (Path.parts a).1 (Path.parts a).2)
      (polytabloid ((finCongr hn).trans (Columns.columnTableau mu))))
      (pathPairWord r) ≠ 0 := by
  have hs : Path.chainFunctional (2*r+1) 1 (wordMap
      (fun (i : Fin (mu.colLen 0)) (a : Fin 4) =>
        Band.conjugation (Band.basis i.val) (Path.parts a).1 (Path.parts a).2)
      (polytabloid ((finCongr hn).trans (Columns.columnTableau mu)))) 0 0≠0 := by
    rw [column_chain_degree,
      Path.chainFunctional_column mu 1 (fun i => Band.conjugation (Band.basis i)),
      Band.segments_conjugation]
    exact Band.conjugation_blocks_ne_zero _ (Path.fourRow_column_lengths mu hmu)
  rw [Path.chainFunctional_endpoint] at hs
  rw [pathPairWord_eq_signed,dotProduct_smul,smul_eq_mul]
  exact hs

section Witness
variable {h e : ℕ → ℕ} (hh : Antitone h) {d m t : ℕ}
    (k : ℕ) (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)

/-- The native row matrix at every path target row. -/
def containedPathNativeLetters :
    Fin ((containedPath h hh d (witnessPathSize k) m).colLen 0) → Fin 4 → ℂ :=
  fun i a => Band.conjugation (Band.basis i.val) (Path.parts a).1 (Path.parts a).2

/-- The prescribed prefix-order polytabloid itself, rather than an arbitrary Specht vector. -/
theorem containedPath_native_coefficient
    (hmu : (containedPath h hh d (witnessPathSize k) m).colLen 0≤4) :
    dotProduct (wordMap (containedPathNativeLetters hh k)
      (polytabloid (containedPathPrefixOrder hh htm hroom hclear hcapacity)))
      (pathPairWord ((k-2)+1))≠0 := by
  rw [containedPath_orders_equal]
  unfold containedPathColumnOrder containedPathNativeLetters
  exact column_path_coefficient _ _ _ hmu
end Witness
end
end HSTZ
#print axioms HSTZ.containedPathNativeLetters
#print axioms HSTZ.containedPath_native_coefficient
