import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic

/-!
# Executable Murnaghan--Nakayama recurrence

Rows and cycle lengths are positive lists; rows are in decreasing order.
The executable functions are total on arbitrary lists. Their interpretation as
Specht characters is not asserted here: `HSTZ.TauCetiFinite.Agreement` proves that
`mn` agrees with TauCeti's Specht character values for partitions of size at most 15.

A beta bead at `a` moves to the empty nonnegative position `a-r`; its leg length
is the number of intervening beads. All possible bead positions are enumerated
by the checker, never supplied by a certificate. Recursion is structural on the
cycle list, including the invalid-input cases. The definitions are meant for kernel
reduction; no `native_decide` is used.
-/
namespace HSTZ.MurnaghanNakayama

abbrev Shape := List ℕ

structure Move where
  shape : Shape
  leg : ℕ
  deriving DecidableEq, Repr

/-- A small transparent sorter, to keep kernel evaluation independent of a
sorting implementation override. Equal elements are retained. -/
def insertDesc (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: bs => if b ≤ a then a :: b :: bs else b :: insertDesc a bs

def sortDesc : List ℕ → List ℕ
  | [] => []
  | a :: as => insertDesc a (sortDesc as)

/-- Zero-based row index: beta_i = lambda_i + length(lambda) - 1 - i. -/
def beta (lam : Shape) : List ℕ :=
  lam.zipIdx.map (fun ai => ai.1 + lam.length - (ai.2 + 1))

/-- Decode decreasing beta numbers, removing zero rows. The additions precede
natural subtraction: using `b - length + i + 1` would be wrong. -/
def decodeBeta (bs : List ℕ) : Shape :=
  (bs.zipIdx.map (fun bi => bi.1 + bi.2 + 1 - bs.length)).filter
    (fun a => decide (0 < a))

def legSign (h : ℕ) : ℤ := if h % 2 = 0 then 1 else -1

def moveBead (bs : List ℕ) (r a : ℕ) : Option Move :=
  if 0 < r ∧ r ≤ a ∧ a - r ∉ bs then
    some { shape := decodeBeta (sortDesc ((a - r) :: bs.erase a))
           leg := (bs.filter (fun c => decide (a - r < c ∧ c < a))).length }
  else none

/-- Exhaust the bead list, rather than accepting a user-supplied list of summands.
On a partition, all beta numbers are distinct. -/
def moves (lam : Shape) (r : ℕ) : List Move :=
  let bs := beta lam
  bs.filterMap (moveBead bs r)

def baseValue (lam : Shape) : ℤ := if lam = [] then 1 else 0

def weightedSum (f : Shape → ℤ) : List Move → ℤ
  | [] => 0
  | m :: ms => legSign m.leg * f m.shape + weightedSum f ms

/-- Recursion on cycle lists, with the shape as a returned function argument.
This avoids well-founded-recursion proof reduction in concrete computations. -/
def mnAux : List ℕ → Shape → ℤ
  | [] => baseValue
  | r :: rho => fun lam => weightedSum (mnAux rho) (moves lam r)

def mn (lam rho : List ℕ) : ℤ := mnAux rho lam

@[simp] theorem mn_nil (lam : Shape) : mn lam [] = baseValue lam := rfl

theorem mn_cons (lam : Shape) (r : ℕ) (rho : List ℕ) :
    mn lam (r :: rho) = weightedSum (fun mu => mn mu rho) (moves lam r) := rfl

lemma weightedSum_congr (f g : Shape → ℤ) (h : ∀ lam, f lam = g lam)
    (ms : List Move) : weightedSum f ms = weightedSum g ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [weightedSum, h m.shape, ih]

/-- Uniqueness of this recurrence: any function satisfying the base case and the
recurrence step agrees with `mn`. Both properties are explicit hypotheses. -/
theorem mn_eq_of_recurrence (f : Shape → List ℕ → ℤ)
    (hbase : ∀ lam, f lam [] = baseValue lam)
    (hstep : ∀ lam r rho,
      f lam (r :: rho) = weightedSum (fun mu => f mu rho) (moves lam r)) :
    ∀ rho lam, mn lam rho = f lam rho := by
  intro rho
  induction rho with
  | nil => intro lam; exact (hbase lam).symm
  | cons r rho ih =>
      intro lam
      rw [mn_cons, hstep]
      exact weightedSum_congr _ _ ih _

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.mn_eq_of_recurrence
