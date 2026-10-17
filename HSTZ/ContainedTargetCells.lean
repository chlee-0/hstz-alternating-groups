import HSTZ.ContainedTarget
import HSTZ.WitnessMatchedProjection

/-! Greedy cells of the contained target: the path, followed by the vertically
translated attachment. Uses geometry adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This file is geometric only; no tensor support, common flag or global shuffle
sign is derived. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev containedPath (h : ℕ → ℕ) (hh : Antitone h) (d K m : ℕ) :=
  fromColumns (greedy h d K) (greedy_antitone hh d K) m
abbrev containedAttachment (e : ℕ → ℕ) (he : Antitone e) (m : ℕ) :=
  fromColumns e he m
abbrev containedWhole (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ) :=
  fromColumns (attached h e d K) (attached_antitone hh he d K) m

def containedPathCell (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ)
    (x : (containedPath h hh d K m).cells) : (containedWhole h e hh he d K m).cells :=
  ⟨x.val, by
    obtain ⟨hc,hr⟩ := (mem_fromColumns _ _ _ _ _).mp x.property
    apply (mem_fromColumns _ _ _ _ _).mpr
    exact ⟨hc,hr.trans_le (Nat.le_add_right _ _)⟩⟩

def containedAttachmentCell (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ)
    (x : (containedAttachment e he m).cells) : (containedWhole h e hh he d K m).cells :=
  ⟨(greedy h d K x.val.2+x.val.1,x.val.2), by
    obtain ⟨hc,hr⟩ := (mem_fromColumns _ _ _ _ _).mp x.property
    exact (mem_fromColumns _ _ _ _ _).mpr ⟨hc,Nat.add_lt_add_left hr _⟩⟩

def containedCellSplit (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ) :
    ((containedPath h hh d K m).cells ⊕ (containedAttachment e he m).cells) ≃
      (containedWhole h e hh he d K m).cells where
  toFun := Sum.elim (containedPathCell h e hh he d K m) (containedAttachmentCell h e hh he d K m)
  invFun x := if hr : x.val.1<greedy h d K x.val.2 then
    .inl ⟨x.val,(mem_fromColumns _ _ _ _ _).mpr
      ⟨((mem_fromColumns _ _ _ _ _).mp x.property).1,hr⟩⟩
    else .inr ⟨(x.val.1-greedy h d K x.val.2,x.val.2), by
      have hx := (mem_fromColumns _ _ _ _ _).mp x.property
      apply (mem_fromColumns _ _ _ _ _).mpr
      refine ⟨hx.1,?_⟩
      have hxrow := hx.2
      change x.val.1<greedy h d K x.val.2+e x.val.2 at hxrow
      omega⟩
  left_inv := by
    intro p
    cases p with
    | inl x =>
      have hr := ((mem_fromColumns _ _ _ _ _).mp x.property).2
      dsimp only [Sum.elim,containedPathCell]
      rw [dif_pos hr]
    | inr x =>
      have hr : ¬greedy h d K x.val.2+x.val.1<greedy h d K x.val.2 := by omega
      dsimp only [Sum.elim,containedAttachmentCell]
      rw [dif_neg hr]
      congr 1
      apply Subtype.ext
      simp
  right_inv := by
    intro x
    dsimp only
    split_ifs with hr
    · rfl
    · apply Subtype.ext
      change (greedy h d K x.val.2+(x.val.1-greedy h d K x.val.2),x.val.2)=x.val
      have hg : greedy h d K x.val.2≤x.val.1 := by omega
      simp [Nat.add_sub_of_le hg]

theorem containedCellSplit_path (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ)
    (x : (containedPath h hh d K m).cells) :
    (containedCellSplit h e hh he d K m (.inl x)).val=x.val := rfl

theorem containedCellSplit_attachment (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ)
    (x : (containedAttachment e he m).cells) :
    (containedCellSplit h e hh he d K m (.inr x)).val=
      (greedy h d K x.val.2+x.val.1,x.val.2) := rfl

/-- Every tableau of the whole target receives the two-layer cell cut. -/
def containedCallerSplit (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ)
    {n : ℕ} (s : Tableau n (containedWhole h e hh he d K m)) :
    Fin n ≃ ((containedPath h hh d K m).cells ⊕ (containedAttachment e he m).cells) :=
  s.trans (containedCellSplit h e hh he d K m).symm

theorem containedCallerSplit_path (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ)
    {n : ℕ} (s : Tableau n (containedWhole h e hh he d K m))
    (x : (containedPath h hh d K m).cells) :
    (s ((containedCallerSplit h e hh he d K m s).symm (.inl x))).val=x.val := by
  simp only [containedCallerSplit,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

theorem containedCallerSplit_attachment (h e : ℕ → ℕ) (hh : Antitone h) (he : Antitone e) (d K m : ℕ)
    {n : ℕ} (s : Tableau n (containedWhole h e hh he d K m))
    (x : (containedAttachment e he m).cells) :
    (s ((containedCallerSplit h e hh he d K m s).symm (.inr x))).val=
      (greedy h d K x.val.2+x.val.1,x.val.2) := by
  simp only [containedCallerSplit,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

end
end HSTZ
#print axioms HSTZ.containedCellSplit
#print axioms HSTZ.containedCellSplit_path
#print axioms HSTZ.containedCellSplit_attachment
#print axioms HSTZ.containedCallerSplit_path
#print axioms HSTZ.containedCallerSplit_attachment
