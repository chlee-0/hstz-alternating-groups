import HSTZ.EqualSubrepresentation
import OAI.RepresentationTheory.Saxl.TableauTransport

/-! Coefficient-preserving identity transport between tableau Specht spaces. -/
namespace HSTZ
noncomputable def tableauSpechtMap {n : ℕ} {mu : YoungDiagram}
    (s t : OAI.Saxl.Tableau n mu) :
    Representation.IntertwiningMap (OAI.Saxl.spechtRep s) (OAI.Saxl.spechtRep t) :=
  equalSubrepresentationMap (rho := OAI.Saxl.wordRep n (mu.colLen 0))
    (OAI.Saxl.spechtSub s) (OAI.Saxl.spechtSub t)
    (OAI.Saxl.spechtSub_tableau_independent s t)

theorem tableauSpechtMap_val {n : ℕ} {mu : YoungDiagram}
    (s t : OAI.Saxl.Tableau n mu) (x : OAI.Saxl.Specht s) :
    ((tableauSpechtMap s t) x).val = x.val :=
  equalSubrepresentationMap_val (rho := OAI.Saxl.wordRep n (mu.colLen 0))
    (OAI.Saxl.spechtSub s) (OAI.Saxl.spechtSub t)
    (OAI.Saxl.spechtSub_tableau_independent s t) x

theorem tableauSpechtMap_bijective {n : ℕ} {mu : YoungDiagram}
    (s t : OAI.Saxl.Tableau n mu) : Function.Bijective (tableauSpechtMap s t).toLinearMap :=
  equalSubrepresentationMap_bijective (rho := OAI.Saxl.wordRep n (mu.colLen 0))
    (OAI.Saxl.spechtSub s) (OAI.Saxl.spechtSub t)
    (OAI.Saxl.spechtSub_tableau_independent s t)
end HSTZ
#print axioms HSTZ.equalSubrepresentationMap_val
#print axioms HSTZ.equalSubrepresentationMap_bijective
#print axioms HSTZ.tableauSpechtMap_val
#print axioms HSTZ.tableauSpechtMap_bijective
