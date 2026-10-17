import HSTZ.WitnessAttachmentHCyclic
import OAI.RepresentationTheory.Saxl.SpechtDuality

/-! Complex bilinear letters for the H of the paper, not a Hermitian form.
Reuses the H normalization and `wordMap` interfaces, building on
OpenAI's `math` repository (commit adc7f1241, Apache-2.0); the proofs in this file are new. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def attachmentHScale : ℂ := (Real.sqrt 2 : ℂ) / 2

theorem attachmentHScale_sq : attachmentHScale ^ 2 = (1/2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  dsimp [attachmentHScale]
  rw [div_pow, hs]
  norm_num

theorem attachmentHScale_ne_zero : attachmentHScale ≠ 0 := by
  intro hz
  have hs := attachmentHScale_sq
  rw [hz] at hs
  norm_num at hs

/-- Rows are H-orthonormal covectors; no complex conjugation occurs. -/
def attachmentHLetters : Matrix (Fin 4) (Fin 4) ℂ :=
  !![attachmentHScale, 0, 0, attachmentHScale;
     Complex.I*attachmentHScale, 0, 0, -Complex.I*attachmentHScale;
     0, attachmentHScale, -attachmentHScale, 0;
     0, Complex.I*attachmentHScale, Complex.I*attachmentHScale, 0]

theorem attachmentHLetters_orthonormal :
    attachmentHLetters * attachmentHForm * attachmentHLetters.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [attachmentHLetters, attachmentHForm, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [attachmentHScale_sq, Complex.I_sq]

theorem attachmentHLetters_singleton :
    attachmentHLetters 0 0 = attachmentHScale := rfl

theorem attachmentHLetters_singleton_ne_zero : attachmentHLetters 0 0 ≠ 0 :=
  attachmentHScale_ne_zero

/-- Permuting the orthonormal covectors puts a nonzero singleton covector
at any prescribed row, including the bottom of an odd unpaired column. -/
def attachmentHLettersAt (a : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => attachmentHLetters (Equiv.swap a 0 i) j

theorem attachmentHLettersAt_orthonormal (a : Fin 4) (i j : Fin 4) :
    ∑ x : Fin 4, ∑ y : Fin 4,
      attachmentHLettersAt a i x * attachmentHForm x y * attachmentHLettersAt a j y =
      if i = j then 1 else 0 := by
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ =>
    M (Equiv.swap a 0 i) (Equiv.swap a 0 j)) attachmentHLetters_orthonormal
  rw [Finset.sum_comm]
  simpa [attachmentHLettersAt, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, Finset.sum_mul, mul_assoc] using he

theorem attachmentHLettersAt_singleton (a : Fin 4) :
    attachmentHLettersAt a a 0 = attachmentHScale := by
  simp [attachmentHLettersAt, attachmentHLetters]

end
end HSTZ
#print axioms HSTZ.attachmentHScale_sq
#print axioms HSTZ.attachmentHScale_ne_zero
#print axioms HSTZ.attachmentHLetters_orthonormal
#print axioms HSTZ.attachmentHLetters_singleton_ne_zero
#print axioms HSTZ.attachmentHLettersAt_orthonormal
#print axioms HSTZ.attachmentHLettersAt_singleton
