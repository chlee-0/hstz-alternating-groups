import HSTZ.YoungDiagramCompat
import HSTZ.ParityCapacity

/-! Contained diagrams of a prescribed size, extracted from a row prefix. This is
pure extraction, with no attachment, parity or clearance inputs. Empty diagrams,
zero depth and zero requested size are allowed. -/
namespace HSTZ

/-- The greedy diagram inside the first d rows of nu. -/
def prefixSubdiagram (nu : YoungDiagram) (d K : ℕ) : YoungDiagram :=
  fromColumns (greedy nu.colLen d K) (greedy_antitone nu.colLen_antitone d K) (nu.rowLen 0)

theorem prefixSubdiagram_le (nu : YoungDiagram) (d K : ℕ) :
    prefixSubdiagram nu d K ≤ nu := by
  have he := fromColumns_le (greedy_antitone nu.colLen_antitone d K) nu.colLen_antitone
    (nu.rowLen 0) (fun i _ => greedy_le_height nu.colLen d K i)
  rw [fromColumns_target] at he
  exact he

theorem prefixSubdiagram_rows (nu : YoungDiagram) (d K : ℕ) :
    (prefixSubdiagram nu d K).colLen 0 ≤ d := by
  by_contra hn
  have hx : (d, 0) ∈ prefixSubdiagram nu d K :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hi := (mem_fromColumns _ _ _ _ _).mp hx
  have hd := greedy_le_depth nu.colLen d K 0
  omega

theorem prefixSubdiagram_card (nu : YoungDiagram) {d K : ℕ}
    (hK : K ≤ prefixSum nu.rowLen d) : (prefixSubdiagram nu d K).card = K := by
  rw [prefixSubdiagram, fromColumns_card, prefix_greedy,
    ← row_prefix_eq_capped_columns, Nat.min_eq_left hK]

/-- Geometric interface, without the attachment clearance guard. -/
theorem exists_prefix_subdiagram (nu : YoungDiagram) {d K : ℕ}
    (hK : K ≤ prefixSum nu.rowLen d) :
    ∃ pi : YoungDiagram, pi ≤ nu ∧ pi.card = K ∧ pi.colLen 0 ≤ d :=
  ⟨prefixSubdiagram nu d K, prefixSubdiagram_le nu d K,
    prefixSubdiagram_card nu hK, prefixSubdiagram_rows nu d K⟩

end HSTZ
#print axioms HSTZ.prefixSubdiagram_le
#print axioms HSTZ.prefixSubdiagram_rows
#print axioms HSTZ.prefixSubdiagram_card
#print axioms HSTZ.exists_prefix_subdiagram
