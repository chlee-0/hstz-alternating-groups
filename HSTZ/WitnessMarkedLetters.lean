import HSTZ.WitnessDiagram

/-! Unequal-alphabet marked letters for the asymmetric witness, using the paper's
ordered masks; no letter permutation or selected vector is involved. -/
namespace HSTZ

def witnessRowMarked (k b a : ℕ) : Prop :=
  (2≤a ∧ a<k-1) ∨ a=k+b-1

def witnessColumnMarked (k a : ℕ) : Prop := 2≤a ∧ a<k

def witnessMarkedRowLetter (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (k-2)) : Fin (k+b+delta) :=
  ⟨if i.val=k-3 then k+b-1 else i.val+2, by
    have hi := i.isLt
    split_ifs <;> omega⟩

def witnessMarkedColumnLetter (k : ℕ) (hk : 5 ≤ k)
    (i : Fin (k-2)) : Fin k := ⟨i.val+2, by have hi := i.isLt; omega⟩

theorem witnessMarkedRowLetter_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessMarkedRowLetter k b delta hk) := by
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  have hh := congrArg Fin.val he
  change (if i.val=k-3 then k+b-1 else i.val+2)=
    (if j.val=k-3 then k+b-1 else j.val+2) at hh
  apply Fin.ext
  split_ifs at hh <;> omega

theorem witnessMarkedColumnLetter_injective (k : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessMarkedColumnLetter k hk) := by
  intro i j he
  have hh := congrArg Fin.val he
  change i.val+2=j.val+2 at hh
  apply Fin.ext
  omega

theorem witnessMarkedRowLetter_range (k b delta : ℕ) (hk : 5 ≤ k)
    (a : Fin (k+b+delta)) :
    a ∈ Set.range (witnessMarkedRowLetter k b delta hk) ↔
      witnessRowMarked k b a.val := by
  constructor
  · rintro ⟨i,rfl⟩
    have hi := i.isLt
    change witnessRowMarked k b (if i.val=k-3 then k+b-1 else i.val+2)
    unfold witnessRowMarked
    split_ifs <;> omega
  · intro ha
    unfold witnessRowMarked at ha
    rcases ha with ⟨hlo,hhi⟩ | he
    · let i : Fin (k-2) := ⟨a.val-2,by omega⟩
      refine ⟨i,Fin.ext ?_⟩
      change (if a.val-2=k-3 then k+b-1 else a.val-2+2)=a.val
      rw [if_neg (by omega)]
      omega
    · let i : Fin (k-2) := ⟨k-3,by omega⟩
      refine ⟨i,Fin.ext ?_⟩
      change (if k-3=k-3 then k+b-1 else k-3+2)=a.val
      simpa using he.symm

theorem witnessMarkedColumnLetter_range (k : ℕ) (hk : 5 ≤ k) (a : Fin k) :
    a ∈ Set.range (witnessMarkedColumnLetter k hk) ↔ witnessColumnMarked k a.val := by
  constructor
  · rintro ⟨i,rfl⟩
    have hi := i.isLt
    change witnessColumnMarked k (i.val+2)
    unfold witnessColumnMarked
    omega
  · intro ha
    unfold witnessColumnMarked at ha
    let i : Fin (k-2) := ⟨a.val-2,by omega⟩
    refine ⟨i,Fin.ext ?_⟩
    change a.val-2+2=a.val
    omega

def witnessMarkedRowEmbedding (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin (k-2) ↪ Fin (k+b+delta) :=
  ⟨witnessMarkedRowLetter k b delta hk,witnessMarkedRowLetter_injective k b delta hk⟩

def witnessMarkedColumnEmbedding (k : ℕ) (hk : 5 ≤ k) : Fin (k-2) ↪ Fin k :=
  ⟨witnessMarkedColumnLetter k hk,witnessMarkedColumnLetter_injective k hk⟩

end HSTZ
#print axioms HSTZ.witnessMarkedRowLetter_injective
#print axioms HSTZ.witnessMarkedColumnLetter_injective
#print axioms HSTZ.witnessMarkedRowLetter_range
#print axioms HSTZ.witnessMarkedColumnLetter_range
