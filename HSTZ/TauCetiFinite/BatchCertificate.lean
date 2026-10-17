import HSTZ.MurnaghanNakayama.Certificate

/-!
Batch lookups into the closed-world Murnaghan–Nakayama certificate. The certificate is
checked once per batch, not once per query, and a missing or mismatched requested key
makes the check fail. This proves values of the executable recurrence only; it does not
relate them to Specht characters and does not say that a list of queries is complete.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama

/-- Each query must occur in the certificate with the stated integer value. -/
def queriesPresent (cert queries : Certificate) : Bool :=
  queries.all fun e => decide (lookup cert e.shape e.cycles = some e.value)

def checkBatch (cert queries : Certificate) : Bool :=
  verify cert && queriesPresent cert queries

/-- One verified DAG supplies all queried recurrence values. -/
theorem checkBatch_sound (cert queries : Certificate)
    (h : checkBatch cert queries = true) :
    ∀ e ∈ queries, mn e.shape e.cycles = e.value := by
  have hh : verify cert = true ∧ queriesPresent cert queries = true := by
    simpa only [checkBatch, Bool.and_eq_true] using h
  have hs := verify_sound cert hh.1
  have hq : ∀ e ∈ queries,
      lookup cert e.shape e.cycles = some e.value := by
    simpa only [queriesPresent, List.all_eq_true, decide_eq_true_eq] using hh.2
  intro e he
  exact (lookup_sound hs (hq e he)).symm

end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.checkBatch_sound
