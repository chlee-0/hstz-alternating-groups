import HSTZ.ContainedTargetCells
import OAI.RepresentationTheory.Saxl.ColumnContraction

/-! The reserved column prefix and the consecutive-column tail of the capacity
target. Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Positions are fixed explicitly; no flag existence or tensor support is proved. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def containedPathTail (h : ℕ → ℕ) (hh : Antitone h) (d K m t : ℕ) : YoungDiagram :=
  fromColumns (fun j => greedy h d K (t+j))
    (fun _ _ hij => greedy_antitone hh d K (Nat.add_le_add_left hij t)) (m-t)

def containedReservedCell {h e : ℕ → ℕ} (hh : Antitone h) {d K m t : ℕ}
    (htm : t ≤ m) (hroom : ∀ c < t, d + e c ≤ h c) (hclear : t*d+4≤K)
    (p : Fin t × Fin d) : (containedPath h hh d K m).cells :=
  ⟨(p.2.val,p.1.val),by
    apply (mem_fromColumns _ _ _ _ _).mpr
    refine ⟨p.1.isLt.trans_le htm,?_⟩
    rw [greedy_eq_depth hroom (by omega) p.1.isLt]
    exact p.2.isLt⟩

def containedTailCell (h : ℕ → ℕ) (hh : Antitone h) (d K m t : ℕ)
    (x : (containedPathTail h hh d K m t).cells) : (containedPath h hh d K m).cells :=
  ⟨(x.val.1,t+x.val.2),by
    have hx := (mem_fromColumns _ _ _ _ _).mp x.property
    apply (mem_fromColumns _ _ _ _ _).mpr
    have hc : x.val.2 < m - t := hx.1
    refine ⟨by omega,hx.2⟩⟩

def containedPathPrefixSplit {h e : ℕ → ℕ} (hh : Antitone h) {d K m t : ℕ}
    (htm : t ≤ m) (hroom : ∀ c < t, d + e c ≤ h c) (hclear : t*d+4≤K) :
    (Fin t × Fin d) ⊕ (containedPathTail h hh d K m t).cells ≃
      (containedPath h hh d K m).cells where
  toFun := Sum.elim (containedReservedCell hh htm hroom hclear) (containedTailCell h hh d K m t)
  invFun x := if hc : x.val.2 < t then .inl (⟨x.val.2,hc⟩,⟨x.val.1,by
      have hx := ((mem_fromColumns _ _ _ _ _).mp x.property).2
      rw [greedy_eq_depth hroom (by omega) hc] at hx
      exact hx⟩)
    else .inr ⟨(x.val.1,x.val.2-t),by
      have hx := (mem_fromColumns _ _ _ _ _).mp x.property
      apply (mem_fromColumns _ _ _ _ _).mpr
      have hxm : x.val.2 < m := hx.1
      refine ⟨?_,?_⟩
      · change x.val.2-t < m-t
        omega
      · change x.val.1<greedy h d K (t+(x.val.2-t))
        have ht : t≤x.val.2 := by omega
        rw [Nat.add_sub_of_le ht]
        exact hx.2⟩
  left_inv := by
    intro p
    cases p with
    | inl p =>
      dsimp only [Sum.elim,containedReservedCell]
      rw [dif_pos p.1.isLt]
    | inr x =>
      have hn : ¬t+x.val.2 < t := by omega
      dsimp only [Sum.elim,containedTailCell]
      rw [dif_neg hn]
      congr 1
      apply Subtype.ext
      simp
  right_inv := by
    intro x
    dsimp only
    split_ifs with hc
    · rfl
    · apply Subtype.ext
      change (x.val.1,t+(x.val.2-t))=x.val
      have ht : t≤x.val.2 := by omega
      simp [Nat.add_sub_of_le ht]

/-- The tail order is the existing consecutive-column tableau. -/
def containedPathTailTableau (h : ℕ → ℕ) (hh : Antitone h) (d K m t : ℕ) :
    Tableau (containedPathTail h hh d K m t).card (containedPathTail h hh d K m t) := by
  let ct := Columns.columnTableau (containedPathTail h hh d K m t)
  have hc : (containedPathTail h hh d K m t).transpose.rowLens.sum=
      (containedPathTail h hh d K m t).card := by
    have hc := Fintype.card_congr ct
    simpa using hc
  exact (finCongr hc.symm).trans ct

theorem containedPathPrefix_card {h e : ℕ → ℕ} (hh : Antitone h) {d K m t : ℕ}
    (htm : t ≤ m) (hroom : ∀ c < t, d + e c ≤ h c) (hclear : t*d+4≤K)
    (hcapacity : K≤prefixSum (capacity h d) m) :
    t*d+(containedPathTail h hh d K m t).card=K := by
  have hc := Fintype.card_congr (containedPathPrefixSplit hh htm hroom hclear)
  have hp : (containedPath h hh d K m).card=K := by
    rw [fromColumns_card,prefix_greedy,Nat.min_eq_left hcapacity]
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_coe,hp] using hc

def containedPathPrefixOrder {h e : ℕ → ℕ} (hh : Antitone h) {d K m t : ℕ}
    (htm : t ≤ m) (hroom : ∀ c < t, d + e c ≤ h c) (hclear : t*d+4≤K)
    (hcapacity : K≤prefixSum (capacity h d) m) : Tableau K (containedPath h hh d K m) :=
  (finCongr (containedPathPrefix_card hh htm hroom hclear hcapacity).symm).trans
    (finSumFinEquiv.symm.trans
      ((Equiv.sumCongr finProdFinEquiv.symm (containedPathTailTableau h hh d K m t)).trans
        (containedPathPrefixSplit hh htm hroom hclear)))

/-- The literal index `c*d+r` of every reserved cell in the path order. -/
theorem containedPathPrefixOrder_reserved {h e : ℕ → ℕ} (hh : Antitone h) {d K m t : ℕ}
    (htm : t ≤ m) (hroom : ∀ c < t, d + e c ≤ h c) (hclear : t*d+4≤K)
    (hcapacity : K≤prefixSum (capacity h d) m) (p : Fin t × Fin d) :
    ((containedPathPrefixOrder hh htm hroom hclear hcapacity).symm
      (containedReservedCell hh htm hroom hclear p)).val=p.1.val*d+p.2.val := by
  have hp : (containedPathPrefixSplit hh htm hroom hclear).symm
      (containedReservedCell hh htm hroom hclear p)=.inl p :=
    (containedPathPrefixSplit hh htm hroom hclear).symm_apply_apply (.inl p)
  simp only [containedPathPrefixOrder,Equiv.symm_trans_apply,Equiv.symm_symm,hp,
    Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl,finCongr_symm,finCongr_apply,Fin.val_cast,finSumFinEquiv_apply_left,Fin.val_castAdd,finProdFinEquiv]
  change p.2.val+d*p.1.val=p.1.val*d+p.2.val
  rw [Nat.mul_comm d p.1.val]
  omega

end
end HSTZ
#print axioms HSTZ.containedPathPrefixSplit
#print axioms HSTZ.containedPathTailTableau
#print axioms HSTZ.containedPathPrefix_card
#print axioms HSTZ.containedPathPrefixOrder
#print axioms HSTZ.containedPathPrefixOrder_reserved
