import HSTZ.WitnessAttachmentHLetters
import HSTZ.BalanceNeighboringPositions

/-! The output-two symmetric tensor and its ordered attachment, adapted from
`Balance/BalancedPairs` in OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The existing `H`, column order and bilinear letters are used in place of the
`ShortColumns`, `SymmetricPairs` and `PairForms` modules, which are not included. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def balanceOutputTwoPair : WordSpace 2 2 :=
  Pi.single (![0,1] : Fin 2 → Fin 2) (1:ℂ)+
    Pi.single (![1,0] : Fin 2 → Fin 2) (1:ℂ)

def balanceOutputTwoPower : (m : ℕ) → WordSpace (2*m) 2
  | 0 => Pi.single (fun _ => 0) 1
  | m+1 => positionProduct (attachmentAppendColumn m)
      (balanceOutputTwoPower m) balanceOutputTwoPair

def balanceOutputTwoOrdered (m : ℕ) : WordSpace (witnessAttachment m 0).card 2 :=
  positionProduct (attachmentColumnSplit m 0) (balanceOutputTwoPower m)
    (Pi.single (fun _ : Fin 0 => (0 : Fin 2)) 1)

def balanceOutputTwoLetters : Matrix (Fin 2) (Fin 2) ℂ :=
  !![attachmentHScale,attachmentHScale;
     Complex.I*attachmentHScale,-Complex.I*attachmentHScale]

def balanceOutputTwoTargetLetters {n : ℕ} {mu : YoungDiagram}
    (_t : Tableau n mu) (ht : mu.colLen 0≤2) : Fin (mu.colLen 0) → Fin 2 → ℂ :=
  fun r => balanceOutputTwoLetters (Fin.castLE ht r)

theorem balanceOutputTwoPair_contraction {d : ℕ} (L : Fin d → Fin 2 → ℂ)
    (a b : Fin d) :
    dotProduct (wordMap L (Pi.single (![a,b] : Fin 2 → Fin d) 1))
      balanceOutputTwoPair=L a 0*L b 1+L a 1*L b 0 := by
  classical
  simp [balanceOutputTwoPair,dotProduct_add,wordMap_single,Fin.prod_univ_succ]

theorem balanceOutputTwoLetters_pair (a b : Fin 2) :
    balanceOutputTwoLetters a 0*balanceOutputTwoLetters b 1+
      balanceOutputTwoLetters a 1*balanceOutputTwoLetters b 0=
        if a=b then (1:ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [balanceOutputTwoLetters] <;> ring_nf <;>
      norm_num [attachmentHScale_sq,Complex.I_sq]

theorem balanceOutputTwoTargetLetters_pair {n : ℕ} {mu : YoungDiagram}
    (t : Tableau n mu) (ht : mu.colLen 0≤2) (a b : Fin (mu.colLen 0)) :
    dotProduct (wordMap (balanceOutputTwoTargetLetters t ht)
      (Pi.single (![a,b] : Fin 2 → Fin (mu.colLen 0)) 1)) balanceOutputTwoPair=
        if a=b then (1:ℂ) else 0 := by
  rw [balanceOutputTwoPair_contraction]
  simpa [balanceOutputTwoTargetLetters] using
    balanceOutputTwoLetters_pair (Fin.castLE ht a) (Fin.castLE ht b)

theorem balanceOutputTwoPair_real : star balanceOutputTwoPair=balanceOutputTwoPair := by
  classical
  funext w
  simp [balanceOutputTwoPair,Pi.single_apply]

theorem balanceOutputTwoPower_real (m : ℕ) :
    star (balanceOutputTwoPower m)=balanceOutputTwoPower m := by
  classical
  induction m with
  | zero => funext w; simp [balanceOutputTwoPower,Pi.single_apply]
  | succ m ih =>
    funext w
    change star (balanceOutputTwoPower m (leftWord (attachmentAppendColumn m) w)*
      balanceOutputTwoPair (rightWord (attachmentAppendColumn m) w))=_
    rw [star_mul]
    rw [show star (balanceOutputTwoPower m (leftWord (attachmentAppendColumn m) w))=_ from
      congrFun ih _,show star (balanceOutputTwoPair (rightWord (attachmentAppendColumn m) w))=_ from
        congrFun balanceOutputTwoPair_real _]
    exact mul_comm _ _

theorem balanceOutputTwoOrdered_real (m : ℕ) :
    star (balanceOutputTwoOrdered m)=balanceOutputTwoOrdered m := by
  classical
  funext w
  change star (balanceOutputTwoPower m (leftWord (attachmentColumnSplit m 0) w)*
    (Pi.single (fun _ : Fin 0 => (0 : Fin 2)) (1:ℂ) : WordSpace 0 2)
      (rightWord (attachmentColumnSplit m 0) w))=_
  rw [star_mul]
  have he := congrFun (balanceOutputTwoPower_real m) (leftWord (attachmentColumnSplit m 0) w)
  simp only [Pi.star_apply] at he
  rw [he]
  simp [balanceOutputTwoOrdered,positionProduct,Pi.single_apply,mul_comm]

def balanceOutputTwoLetter (i : Fin 2) : Fin 4 := finProdFinEquiv (i,i.rev)

theorem balanceOutputTwoPaperH (w : Fin 2 → Fin 2) :
    attachmentPaperH (balanceOutputTwoLetter ∘ w)=-balanceOutputTwoPair w := by
  have hw : w=![w 0,w 1] := by ext i; fin_cases i <;> rfl
  rw [hw]
  generalize h0 : w 0=a
  generalize h1 : w 1=b
  fin_cases a <;> fin_cases b <;>
    norm_num [attachmentPaperH,balanceOutputTwoPair,balanceOutputTwoLetter,
      finProdFinEquiv,Fin.rev,Pi.single_apply,funext_iff,Fin.forall_fin_two,Fin.ext_iff]

theorem balanceOutputTwoHPower (m : ℕ) (w : Fin (2*m) → Fin 2) :
    attachmentHPower m (balanceOutputTwoLetter ∘ w)=
      (-1:ℂ)^m*balanceOutputTwoPower m w := by
  classical
  induction m with
  | zero =>
    simp only [attachmentHPower,balanceOutputTwoPower,Pi.single_apply,pow_zero,one_mul]
    rw [if_pos (by funext i; exact Fin.elim0 i),if_pos (by funext i; exact Fin.elim0 i)]
  | succ m ih =>
    change attachmentHPower m (balanceOutputTwoLetter ∘ leftWord (attachmentAppendColumn m) w)*
      attachmentPaperH (balanceOutputTwoLetter ∘ rightWord (attachmentAppendColumn m) w)=_
    rw [ih,balanceOutputTwoPaperH,pow_succ]
    change _=((-1:ℂ)^m*(-1))*(balanceOutputTwoPower m
      (leftWord (attachmentAppendColumn m) w)*balanceOutputTwoPair (rightWord (attachmentAppendColumn m) w))
    ring

theorem balanceOutputTwoHTensor (m : ℕ) (w : Fin (witnessAttachment m 0).card → Fin 2) :
    attachmentHTensor m 0 (balanceOutputTwoLetter ∘ w)=
      (-1:ℂ)^m*balanceOutputTwoOrdered m w := by
  classical
  change attachmentHPower m (balanceOutputTwoLetter ∘ leftWord (attachmentColumnSplit m 0) w)*
    (Pi.single (fun _ : Fin 0 => (0 : Fin 4)) (1:ℂ) : WordSpace 0 4)
      (balanceOutputTwoLetter ∘ rightWord (attachmentColumnSplit m 0) w)=_
  rw [balanceOutputTwoHPower]
  simp only [balanceOutputTwoOrdered,positionProduct,Pi.single_apply]
  rw [if_pos (by funext i; exact Fin.elim0 i),if_pos (by funext i; exact Fin.elim0 i)]
  ring

end
end HSTZ
#print axioms HSTZ.balanceOutputTwoTargetLetters_pair
#print axioms HSTZ.balanceOutputTwoOrdered_real
#print axioms HSTZ.balanceOutputTwoHPower
#print axioms HSTZ.balanceOutputTwoHTensor
