import HSTZ.YoungDiagramCompat
import HSTZ.BalanceOutputTwoSupport
import HSTZ.PieriArithmetic
import HSTZ.PieriSupport

/-! Even precursor and Pieri constituent for the paper's cases x = 1, 3.
Adapts `WordPackingPieri` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
We keep the bound x ≤ c+1, including the case c = 2, x = 3, and reuse the existing
Pieri maps. This file does not prove a component packing or full-square assembly theorem. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem precursor_row_length (b delta r : ℕ) :
    (witnessAttachment b delta).rowLen r=
      if r=0 then b+delta else if r=1 then b else 0 := by
  have hh (j : ℕ) : j<(witnessAttachment b delta).rowLen r ↔
      j<(if r=0 then b+delta else if r=1 then b else 0) := by
    rw [← YoungDiagram.mem_iff_lt_rowLen,mem_witnessAttachment]
    by_cases h0 : r=0
    · simp [h0]
    · by_cases h1 : r=1 <;> simp [h0,h1]
  have h1 := hh ((witnessAttachment b delta).rowLen r)
  have h2 := hh (if r=0 then b+delta else if r=1 then b else 0)
  omega

private theorem target_two_rows (nu : YoungDiagram) (ht : nu.colLen 0≤2)
    {r j : ℕ} (h : (r,j)∈nu) : r=0 ∨ r=1 := by
  have hh := YoungDiagram.mem_iff_lt_colLen.mp
    (nu.up_left_mem le_rfl (Nat.zero_le _) h)
  omega

theorem balanceEvenPrecursor_geometry {c x : ℕ} {nu : YoungDiagram}
    (hc : c%2=0) (hx : x=1 ∨ x=3) (hlegal : x≤c+1)
    (ht : nu.colLen 0≤2) (hn : nu.card=c+x) :
    ∃ xi : YoungDiagram, xi.card=c ∧ AttachmentEvenRows xi ∧ xi.colLen 0≤2 ∧
      HorizontalStrip xi nu := by
  have hs := row_prefix_full nu ht
  simp only [prefix_succ,prefix_zero] at hs
  have hab : nu.rowLen 1≤nu.rowLen 0 := nu.rowLen_anti 0 1 (by omega)
  have hsize : nu.rowLen 0+nu.rowLen 1=c+x := by omega
  have hodd : x%2=1 := by rcases hx with rfl | rfl <;> decide
  obtain ⟨y,hy,hl,hu⟩ := even_precursor_odd hc hodd hlegal
    (by omega : 2*nu.rowLen 1≤c+x)
  have hb : nu.rowLen 1≤c := by omega
  obtain ⟨gamma,z,hgz,hg,hz,hzg,hzb,hbg,hga⟩ :=
    (even_precursor_iff_interlacing hc hsize hb).mp ⟨y,hy,hl,hu⟩
  let xi := witnessAttachment z (gamma-z)
  have hfirst : z+(gamma-z)=gamma := by omega
  have hcard : xi.card=c := by
    rw [witnessAttachment_card]
    omega
  have he : AttachmentEvenRows xi := by
    intro r
    rw [precursor_row_length]
    split_ifs <;> omega
  have hin : xi≤nu := by
    intro v hv
    rcases v with ⟨r,j⟩
    change (r,j)∈witnessAttachment z (gamma-z) at hv
    rcases (mem_witnessAttachment _ _ _ _).mp hv with ⟨rfl,hj⟩ | ⟨rfl,hj⟩
    · exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    · exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have hstrip : HorizontalStrip xi nu := by
    refine ⟨hin,?_⟩
    intro a ha hna b hb' hnb heq
    rcases a with ⟨r,j⟩
    rcases b with ⟨s,l⟩
    have hr := target_two_rows nu ht ha
    have hs' := target_two_rows nu ht hb'
    have hra : j<nu.rowLen r := YoungDiagram.mem_iff_lt_rowLen.mp ha
    have hsb : l<nu.rowLen s := YoungDiagram.mem_iff_lt_rowLen.mp hb'
    change j=l at heq
    have hna' : ¬ ((r=0 ∧ j<gamma) ∨ (r=1 ∧ j<z)) := by
      simpa only [xi,mem_witnessAttachment,hfirst] using hna
    have hnb' : ¬ ((s=0 ∧ l<gamma) ∨ (s=1 ∧ l<z)) := by
      simpa only [xi,mem_witnessAttachment,hfirst] using hnb
    have hrs : r=s := by rcases hr with rfl | rfl <;>
      rcases hs' with rfl | rfl <;> omega
    exact Prod.ext hrs heq
  exact ⟨xi,hcard,he,witnessAttachment_rows _ _,hstrip⟩

/-- The target chooses its even precursor internally. Both the symmetric cyclic
support of the precursor and its ordinary Pieri embedding are provided. No
identification with a component tensor, block or packing is asserted. -/
theorem balanceEvenPrecursor_pieri (m x : ℕ) (hx : x=1 ∨ x=3)
    (hlegal : x≤2*m+1) {nu : YoungDiagram}
    (t : Tableau ((witnessAttachment m 0).card+x) nu) (ht : nu.colLen 0≤2) :
    ∃ (xi : YoungDiagram) (s : Tableau (witnessAttachment m 0).card xi),
      AttachmentEvenRows xi ∧ xi.colLen 0≤2 ∧ ∃ hstrip : HorizontalStrip xi nu,
      (∃ B : Representation.IntertwiningMap (spechtRep s)
        (cyclic (wordRep (witnessAttachment m 0).card 2)
          (balanceOutputTwoOrdered m)).toRepresentation, Function.Injective B) ∧
      (∃ E : Representation.IntertwiningMap (spechtRep t)
        (Representation.ind (A := Specht s)
          (positionPairAmbient (tableauInclusion s t hstrip.1))
          ((spechtRep s).comp (positionPairCore (tableauInclusion s t hstrip.1)))),
        Function.Injective E) := by
  have hcard : nu.card=(witnessAttachment m 0).card+x := by
    simpa using (Fintype.card_congr t).symm
  have hc : (witnessAttachment m 0).card%2=0 := by
    rw [witnessAttachment_card]; omega
  have hl : x≤(witnessAttachment m 0).card+1 := by
    rw [witnessAttachment_card]; omega
  obtain ⟨xi,hxi,he,hh,hstrip⟩ := balanceEvenPrecursor_geometry hc hx hl ht hcard
  let s := canonicalTableau xi hxi
  exact ⟨xi,s,he,hh,hstrip,balanceOutputTwo_even_embedding m s he hh,
    pieri_induced_embedding s t hstrip⟩

/-- The paper's corner case c = 2, x = 3 is included; the stricter upstream
assumption x ≤ c is not needed. -/
theorem balanceEvenPrecursor_corner {nu : YoungDiagram}
    (t : Tableau ((witnessAttachment 1 0).card+3) nu) (ht : nu.colLen 0≤2) :
    ∃ (xi : YoungDiagram) (s : Tableau (witnessAttachment 1 0).card xi),
      AttachmentEvenRows xi ∧ xi.colLen 0≤2 ∧ ∃ hstrip : HorizontalStrip xi nu,
      (∃ B : Representation.IntertwiningMap (spechtRep s)
        (cyclic (wordRep (witnessAttachment 1 0).card 2)
          (balanceOutputTwoOrdered 1)).toRepresentation, Function.Injective B) ∧
      (∃ E : Representation.IntertwiningMap (spechtRep t)
        (Representation.ind (A := Specht s)
          (positionPairAmbient (tableauInclusion s t hstrip.1))
          ((spechtRep s).comp (positionPairCore (tableauInclusion s t hstrip.1)))),
        Function.Injective E) :=
  balanceEvenPrecursor_pieri 1 3 (Or.inr rfl) (by omega) t ht

end
end HSTZ
#print axioms HSTZ.balanceEvenPrecursor_geometry
#print axioms HSTZ.balanceEvenPrecursor_pieri
#print axioms HSTZ.balanceEvenPrecursor_corner
