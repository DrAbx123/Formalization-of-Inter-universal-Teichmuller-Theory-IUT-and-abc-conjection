import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

namespace LeanFormal.IUT.Audit

open LeanFormal.IUT.InitialThetaSource

def initialThetaData_conclusion_spec
    {l : LeanFormal.IUT.PrimeGeFive} :
    ∀ S : SourceInitialThetaData l,
      InitialThetaDataConclusion S := by
  intro S
  exact InitialThetaSource.initialThetaData_conclusion S

/-!
  The Definition 3.1 endpoint has two different proof responsibilities.  The
  first is recognition: once a source tuple already carries clauses (a)--(f),
  the conclusion is recovered with the paper's original quantifiers.  The
  second is existence: an allowed arithmetic input must actually produce such
  a tuple.  These are not interchangeable, so they have separate audit ids.
-/

def initialThetaDataRecognition : Obligation :=
  { id := "IUT-I.initial-theta-data"
    source := "IUT I, Sections 3-4"
    status := VerificationStatus.interface
    note :=
      "The paper fixes initial Theta-data that already satisfy clauses (a)-(f). " ++
        "This conditional recognition theorem has the intended source-input " ++
        "quantifier: every candidate carrying clauses (a)-(f) yields the " ++
        "Definition 3.1 conclusion, with the original place, torsion, " ++
        "exact-sequence, section, q-parameter, and cusp quantifiers. It is a " ++
        "conditional theorem about the paper's fixed input, not an assertion " ++
        "that arbitrary arithmetic data satisfy Definition 3.1."
    dependsOn := ["IUT-I.initial-theta-arithmetic-data"] }

/-! Backward-compatible name for the completed recognition obligation. -/
def initialThetaData : Obligation := initialThetaDataRecognition

/-!
  This is deliberately a separate implementation route.  Definition 3.1 and
  Theorem 3.11 begin with a fixed qualified initial-Theta tuple; they do not
  quantify over the smaller `InitialThetaArithmeticData` record below.  Keeping
  this route in the ledger is useful when constructing an input from foundations,
  but it must never be used to relabel the paper theorem or to downgrade the
  completed source-input recognition theorem.
-/
def initialThetaDataArithmeticRoute : Obligation :=
  { id := "IUT-I.definition-3.1-arithmetic-realization-route"
    source := "Project extension (not a premise of IUT I Definition 3.1)"
    status := VerificationStatus.pending
    note :=
      "This stronger foundation-to-input construction is not a premise of the " ++
        "paper's fixed-input Definition 3.1 or Theorem 3.11. If the project chooses to construct " ++
        "an initial tuple from the smaller arithmetic carrier, every missing " ++
        "reduction, torsion, orbicurve, section, and cusp object must still be " ++
        "built here; no field or theorem may be treated as an implicit assumption."
    dependsOn :=
      [ "IUT-I.initial-theta-arithmetic-data",
        "IUT-I.definition-3.1-D9" ] }

/-! Historical spelling retained only for source compatibility. -/
def initialThetaDataConstruction : Obligation :=
  initialThetaDataArithmeticRoute

def hodgeTheaterHistories : Obligation :=
  { id := "IUT-I.hodge-theater-histories"
    source := "IUT I, Sections 4-5"
    status := VerificationStatus.pending
    note := "Construct distinct histories and their links; do not use an unconstrained record." }

end LeanFormal.IUT.Audit
