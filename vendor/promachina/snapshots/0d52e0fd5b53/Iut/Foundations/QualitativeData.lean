/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.TransportedRegionFamily

/-!
Structured qualitative data for algorithmic outputs.

The base records name the IPL, SHE, and APT components carried by an
algorithmic-output certificate.  The source-shaped constructions below add
typed input-prime-strip links, Hodge-theater transport permissions, forbidden
identification guards, and permitted APT transport data that can build those
base records.
-/

namespace Iut
namespace RealLineCopy

namespace QualitativeData

variable {source target : Copy} {index : Type u}
variable {newIndex : Type v}

/-- Inert identifier for a prime strip or prime-strip-like bookkeeping object. -/
structure PrimeStripId where
  label : String

/-- Which side of a Hodge-theater comparison an identifier belongs to. -/
inductive HodgeTheaterSide where
  | domain
  | codomain
  | intermediate
deriving DecidableEq, Repr

/-- Inert identifier for a Hodge theater in the qualitative bookkeeping layer. -/
structure HodgeTheaterId where
  side : HodgeTheaterSide
  label : String

/-- Inert identifier for a language/common-expression context. -/
structure CommonLanguageId where
  label : String

/-- Inert identifier for an APT-style construction mechanism. -/
structure TransportMechanismId where
  label : String

/-- Inert relation record for an IPL-style link between prime strips. -/
structure PrimeStripLink where
  source : PrimeStripId
  target : PrimeStripId
  linkLabel : String

/-- Inert record for input-prime-strip-link style data. -/
structure IPLDatum (family : TransportedRegionFamily source target index) where
  inputPrimeStrip : PrimeStripId
  outputPrimeStrip : PrimeStripId
  choicePrimeStrip : index -> PrimeStripId
  link : PrimeStripLink

/--
Source-shaped input-prime-strip-link construction.

Unlike `IPLDatum`, this record does not accept an arbitrary link source and
target.  Its associated `IPLDatum` builds the link from the recorded input and
output prime strips, so the two endpoint identifications are definitional
consequences of the construction.
-/
structure InputPrimeStripLinkConstruction
    (family : TransportedRegionFamily source target index) where
  inputPrimeStrip : PrimeStripId
  outputPrimeStrip : PrimeStripId
  choicePrimeStrip : index -> PrimeStripId
  linkLabel : String

namespace InputPrimeStripLinkConstruction

variable {family : TransportedRegionFamily source target index}

def reindex
    (construction : InputPrimeStripLinkConstruction family)
    (f : newIndex -> index) :
    InputPrimeStripLinkConstruction (family.reindex f) :=
  { inputPrimeStrip := construction.inputPrimeStrip,
    outputPrimeStrip := construction.outputPrimeStrip,
    choicePrimeStrip := fun choice => construction.choicePrimeStrip (f choice),
    linkLabel := construction.linkLabel }

def link (construction : InputPrimeStripLinkConstruction family) :
    PrimeStripLink :=
  { source := construction.inputPrimeStrip,
    target := construction.outputPrimeStrip,
    linkLabel := construction.linkLabel }

/--
The choice-wise input-prime-strip link.

This is the finite bookkeeping shadow of the IPL assertion that each possible
output prime strip is linked back to the fixed input prime strip.  The source
endpoint is the input prime strip by construction; the target endpoint is the
chosen output prime strip.
-/
def choiceLink
    (construction : InputPrimeStripLinkConstruction family)
    (choice : index) : PrimeStripLink :=
  { source := construction.inputPrimeStrip,
    target := construction.choicePrimeStrip choice,
    linkLabel := construction.linkLabel }

def toIPLDatum
    (construction : InputPrimeStripLinkConstruction family) :
    IPLDatum family :=
  { inputPrimeStrip := construction.inputPrimeStrip,
    outputPrimeStrip := construction.outputPrimeStrip,
    choicePrimeStrip := construction.choicePrimeStrip,
    link := construction.link }

theorem toIPLDatum_link_source_eq_input
    (construction : InputPrimeStripLinkConstruction family) :
    construction.toIPLDatum.link.source =
      construction.toIPLDatum.inputPrimeStrip :=
  rfl

theorem toIPLDatum_link_target_eq_output
    (construction : InputPrimeStripLinkConstruction family) :
    construction.toIPLDatum.link.target =
      construction.toIPLDatum.outputPrimeStrip :=
  rfl

theorem choiceLink_source_eq_input
    (construction : InputPrimeStripLinkConstruction family)
    (choice : index) :
    (construction.choiceLink choice).source =
      construction.toIPLDatum.inputPrimeStrip :=
  rfl

theorem choiceLink_target_eq_choice
    (construction : InputPrimeStripLinkConstruction family)
    (choice : index) :
    (construction.choiceLink choice).target =
      construction.toIPLDatum.choicePrimeStrip choice :=
  rfl

theorem toIPLDatum_endpoint
    (construction : InputPrimeStripLinkConstruction family) :
    construction.toIPLDatum.link.source =
        construction.toIPLDatum.inputPrimeStrip ∧
      construction.toIPLDatum.link.target =
        construction.toIPLDatum.outputPrimeStrip :=
  ⟨construction.toIPLDatum_link_source_eq_input,
    construction.toIPLDatum_link_target_eq_output⟩

theorem choiceLink_endpoint
    (construction : InputPrimeStripLinkConstruction family)
    (choice : index) :
    (construction.choiceLink choice).source =
        construction.toIPLDatum.inputPrimeStrip ∧
      (construction.choiceLink choice).target =
        construction.toIPLDatum.choicePrimeStrip choice :=
  ⟨construction.choiceLink_source_eq_input choice,
    construction.choiceLink_target_eq_choice choice⟩

end InputPrimeStripLinkConstruction

namespace IPLDatum

variable {family : TransportedRegionFamily source target index}

def reindex (datum : IPLDatum family) (f : newIndex -> index) :
    IPLDatum (family.reindex f) :=
  { inputPrimeStrip := datum.inputPrimeStrip,
    outputPrimeStrip := datum.outputPrimeStrip,
    choicePrimeStrip := fun choice => datum.choicePrimeStrip (f choice),
    link := datum.link }

end IPLDatum

/-- A named arithmetic holomorphic structure in the toy bookkeeping layer. -/
structure HolomorphicStructure where
  theater : HodgeTheaterId
  structureLabel : String

/-- Inert relation record for simultaneous expression in a common context. -/
structure SharedHolomorphicContext where
  domainStructure : HolomorphicStructure
  codomainStructure : HolomorphicStructure
  commonLanguage : CommonLanguageId

/-- Inert record for simultaneous-holomorphic-expressibility style data. -/
structure SHEDatum (family : TransportedRegionFamily source target index) where
  sharedContext : SharedHolomorphicContext

def HasStructuredSHE (family : TransportedRegionFamily source target index) : Prop :=
  Nonempty (SHEDatum family)

/--
Structured witness for the local validity content of simultaneous holomorphic
expression.

This still abstracts the hard analytic/arithmetic meaning of the validity
claims, but it no longer compresses all SHE validity into one undifferentiated
proposition.
-/
structure SimultaneousHolomorphicExpressionData where
  domain_expression_valid : Prop
  domain_expression_valid_holds : domain_expression_valid
  codomain_expression_valid : Prop
  codomain_expression_valid_holds : codomain_expression_valid
  q_pilot_expression_valid : Prop
  q_pilot_expression_valid_holds : q_pilot_expression_valid
  theta_pilot_expression_valid : Prop
  theta_pilot_expression_valid_holds : theta_pilot_expression_valid
  simultaneous_valid : Prop
  simultaneous_valid_holds : simultaneous_valid

namespace SimultaneousHolomorphicExpressionData

variable (expression : SimultaneousHolomorphicExpressionData)

theorem domainExpressionValid : expression.domain_expression_valid :=
  expression.domain_expression_valid_holds

theorem codomainExpressionValid : expression.codomain_expression_valid :=
  expression.codomain_expression_valid_holds

theorem qPilotExpressionValid : expression.q_pilot_expression_valid :=
  expression.q_pilot_expression_valid_holds

theorem thetaPilotExpressionValid : expression.theta_pilot_expression_valid :=
  expression.theta_pilot_expression_valid_holds

theorem simultaneousValid : expression.simultaneous_valid :=
  expression.simultaneous_valid_holds

def AllLocalValid : Prop :=
  expression.domain_expression_valid ∧
    expression.codomain_expression_valid ∧
    expression.q_pilot_expression_valid ∧
    expression.theta_pilot_expression_valid ∧
    expression.simultaneous_valid

theorem allLocalValid :
    expression.AllLocalValid :=
  ⟨expression.domainExpressionValid, expression.codomainExpressionValid,
    expression.qPilotExpressionValid, expression.thetaPilotExpressionValid,
    expression.simultaneousValid⟩

theorem allLocalValid_expanded :
    expression.domain_expression_valid ∧
      expression.codomain_expression_valid ∧
      expression.q_pilot_expression_valid ∧
      expression.theta_pilot_expression_valid ∧
      expression.simultaneous_valid :=
  expression.allLocalValid

end SimultaneousHolomorphicExpressionData

/--
First non-inert local context for simultaneous holomorphic expressibility.

This still does not produce a comparison bound or an endpoint. It records the
two holomorphic structures, the common expression language, the q- and
Theta-side pilot structures, structured validity data for simultaneous
expression, and an explicit guard that the two Hodge-theater histories are not
being identified.
-/
structure StructuredSHEContext
    (family : TransportedRegionFamily source target index) where
  domainStructure : HolomorphicStructure
  codomainStructure : HolomorphicStructure
  commonLanguage : CommonLanguageId
  qPilotStructure : HolomorphicStructure
  thetaPilotStructure : HolomorphicStructure
  q_pilot_in_codomain :
    qPilotStructure.theater = codomainStructure.theater
  theta_pilot_in_domain :
    thetaPilotStructure.theater = domainStructure.theater
  simultaneousExpression : SimultaneousHolomorphicExpressionData
  histories_not_identified :
    domainStructure.theater.side ≠ codomainStructure.theater.side

namespace StructuredSHEContext

variable {family : TransportedRegionFamily source target index}

def reindex (context : StructuredSHEContext family) (f : newIndex -> index) :
    StructuredSHEContext (family.reindex f) :=
  { domainStructure := context.domainStructure,
    codomainStructure := context.codomainStructure,
    commonLanguage := context.commonLanguage,
    qPilotStructure := context.qPilotStructure,
    thetaPilotStructure := context.thetaPilotStructure,
    q_pilot_in_codomain := context.q_pilot_in_codomain,
    theta_pilot_in_domain := context.theta_pilot_in_domain,
    simultaneousExpression := context.simultaneousExpression,
    histories_not_identified := context.histories_not_identified }

def sharedContext (context : StructuredSHEContext family) :
    SharedHolomorphicContext :=
  { domainStructure := context.domainStructure,
    codomainStructure := context.codomainStructure,
    commonLanguage := context.commonLanguage }

def sheDatum (context : StructuredSHEContext family) : SHEDatum family :=
  { sharedContext := context.sharedContext }

theorem hasStructuredSHE (context : StructuredSHEContext family) :
    HasStructuredSHE family :=
  ⟨context.sheDatum⟩

theorem qPilotTheater_eq_codomain
    (context : StructuredSHEContext family) :
    context.qPilotStructure.theater =
      context.codomainStructure.theater :=
  context.q_pilot_in_codomain

theorem thetaPilotTheater_eq_domain
    (context : StructuredSHEContext family) :
    context.thetaPilotStructure.theater =
      context.domainStructure.theater :=
  context.theta_pilot_in_domain

def simultaneous_valid (context : StructuredSHEContext family) : Prop :=
  context.simultaneousExpression.simultaneous_valid

theorem domainExpressionValid (context : StructuredSHEContext family) :
    context.simultaneousExpression.domain_expression_valid :=
  context.simultaneousExpression.domainExpressionValid

theorem codomainExpressionValid (context : StructuredSHEContext family) :
    context.simultaneousExpression.codomain_expression_valid :=
  context.simultaneousExpression.codomainExpressionValid

theorem qPilotExpressionValid (context : StructuredSHEContext family) :
    context.simultaneousExpression.q_pilot_expression_valid :=
  context.simultaneousExpression.qPilotExpressionValid

theorem thetaPilotExpressionValid (context : StructuredSHEContext family) :
    context.simultaneousExpression.theta_pilot_expression_valid :=
  context.simultaneousExpression.thetaPilotExpressionValid

theorem simultaneousValid (context : StructuredSHEContext family) :
    context.simultaneous_valid :=
  context.simultaneousExpression.simultaneousValid

theorem allLocalExpressionValid (context : StructuredSHEContext family) :
    context.simultaneousExpression.AllLocalValid :=
  context.simultaneousExpression.allLocalValid

theorem allLocalExpressionValid_expanded (context : StructuredSHEContext family) :
    context.simultaneousExpression.domain_expression_valid ∧
      context.simultaneousExpression.codomain_expression_valid ∧
      context.simultaneousExpression.q_pilot_expression_valid ∧
      context.simultaneousExpression.theta_pilot_expression_valid ∧
      context.simultaneous_valid :=
  context.simultaneousExpression.allLocalValid_expanded

theorem domainHistory_ne_codomainHistory
    (context : StructuredSHEContext family) :
    context.domainStructure.theater.side ≠
      context.codomainStructure.theater.side :=
  context.histories_not_identified

theorem sheDatum_sharedContext
    (context : StructuredSHEContext family) :
    context.sheDatum.sharedContext = context.sharedContext :=
  rfl

end StructuredSHEContext

structure HodgeTheaterTransportArrow where
  source : HodgeTheaterId
  target : HodgeTheaterId
  mechanism : TransportMechanismId

/--
Typed transport permissions between Hodge theaters.

`forbiddenIdentification` marks theater identifications that the source data
rules out.  Any explicitly allowed transport arrow is required to avoid those
forbidden identifications.
-/
structure HodgeTheaterTransportSystem where
  allowed : HodgeTheaterTransportArrow -> Prop
  forbiddenIdentification : HodgeTheaterId -> HodgeTheaterId -> Prop
  allowed_not_forbidden :
    ∀ {arrow : HodgeTheaterTransportArrow},
      allowed arrow ->
        ¬ forbiddenIdentification arrow.source arrow.target

namespace HodgeTheaterTransportSystem

def Allows
    (system : HodgeTheaterTransportSystem)
    (source target : HodgeTheaterId)
    (mechanism : TransportMechanismId) : Prop :=
  system.allowed
    { source := source,
      target := target,
      mechanism := mechanism }

theorem allowed_not_forbidden_identification
    (system : HodgeTheaterTransportSystem)
    {arrow : HodgeTheaterTransportArrow}
    (hallowed : system.allowed arrow) :
    ¬ system.forbiddenIdentification arrow.source arrow.target :=
  system.allowed_not_forbidden hallowed

end HodgeTheaterTransportSystem

structure PermittedHodgeTheaterTransport
    (system : HodgeTheaterTransportSystem) where
  arrow : HodgeTheaterTransportArrow
  permitted : system.allowed arrow

namespace PermittedHodgeTheaterTransport

variable {system : HodgeTheaterTransportSystem}

theorem not_forbidden
    (transport : PermittedHodgeTheaterTransport system) :
    ¬ system.forbiddenIdentification transport.arrow.source transport.arrow.target :=
  system.allowed_not_forbidden transport.permitted

end PermittedHodgeTheaterTransport

/--
Quotient object attached to a Hodge-theater transport system.

The setoid is supplied as source data: it records which theater histories are
identified by the permitted transport discipline.  Every allowed arrow must
become an equality in this quotient.
-/
structure HodgeTheaterTransportQuotient
    (system : HodgeTheaterTransportSystem) where
  quotientSetoid : Setoid HodgeTheaterId
  allowed_arrow_related :
    ∀ {arrow : HodgeTheaterTransportArrow},
      system.allowed arrow ->
        quotientSetoid.r arrow.source arrow.target

namespace HodgeTheaterTransportQuotient

variable {system : HodgeTheaterTransportSystem}

def quotient
    (transportQuotient : HodgeTheaterTransportQuotient system) : Type :=
  Quotient transportQuotient.quotientSetoid

def classOf
    (transportQuotient : HodgeTheaterTransportQuotient system)
    (theater : HodgeTheaterId) :
    transportQuotient.quotient :=
  Quotient.mk transportQuotient.quotientSetoid theater

theorem allowedArrowClassEq
    (transportQuotient : HodgeTheaterTransportQuotient system)
    {arrow : HodgeTheaterTransportArrow}
    (hallowed : system.allowed arrow) :
    transportQuotient.classOf arrow.source =
      transportQuotient.classOf arrow.target :=
  Quotient.sound (transportQuotient.allowed_arrow_related hallowed)

theorem permittedTransportClassEq
    (transportQuotient : HodgeTheaterTransportQuotient system)
    (transport : PermittedHodgeTheaterTransport system) :
    transportQuotient.classOf transport.arrow.source =
      transportQuotient.classOf transport.arrow.target :=
  transportQuotient.allowedArrowClassEq transport.permitted

end HodgeTheaterTransportQuotient

/--
SHE context whose history separation is expressed by the typed transport system.

The older `StructuredSHEContext` is retained as the underlying local expression
data.  This wrapper adds the source-facing guard that the domain-to-codomain
identification is forbidden by the transport system, hence no permitted
transport arrow may identify those two theaters.
-/
structure StructuredSHETransportContext
    (family : TransportedRegionFamily source target index) where
  baseContext : StructuredSHEContext family
  transportSystem : HodgeTheaterTransportSystem
  forbidden_domain_to_codomain :
    transportSystem.forbiddenIdentification
      baseContext.domainStructure.theater
      baseContext.codomainStructure.theater

namespace StructuredSHETransportContext

variable {family : TransportedRegionFamily source target index}

def reindex
    (context : StructuredSHETransportContext family)
    (f : newIndex -> index) :
    StructuredSHETransportContext (family.reindex f) :=
  { baseContext := context.baseContext.reindex f,
    transportSystem := context.transportSystem,
    forbidden_domain_to_codomain := context.forbidden_domain_to_codomain }

def sheDatum (context : StructuredSHETransportContext family) :
    SHEDatum family :=
  context.baseContext.sheDatum

theorem hasStructuredSHE (context : StructuredSHETransportContext family) :
    HasStructuredSHE family :=
  ⟨context.sheDatum⟩

theorem noAllowedDomainToCodomain
    (context : StructuredSHETransportContext family)
    {arrow : HodgeTheaterTransportArrow}
    (hsource :
      arrow.source = context.baseContext.domainStructure.theater)
    (htarget :
      arrow.target = context.baseContext.codomainStructure.theater) :
    ¬ context.transportSystem.allowed arrow := by
  intro hallowed
  exact
    (context.transportSystem.allowed_not_forbidden hallowed)
      (by
        simpa [hsource, htarget] using context.forbidden_domain_to_codomain)

theorem noAllowedDomainToCodomainWithMechanism
    (context : StructuredSHETransportContext family)
    (mechanism : TransportMechanismId) :
    ¬ context.transportSystem.Allows
        context.baseContext.domainStructure.theater
        context.baseContext.codomainStructure.theater
        mechanism := by
  intro hallowed
  exact
    (context.transportSystem.allowed_not_forbidden hallowed)
      context.forbidden_domain_to_codomain

theorem sheDatum_sharedContext
    (context : StructuredSHETransportContext family) :
    context.sheDatum.sharedContext = context.baseContext.sharedContext :=
  rfl

/--
Typed audit that the domain and codomain Hodge-theater histories are separated
by the transport system itself.

This strengthens the pointwise `¬ Allows ...` projection by keeping the
forbidden theater-pair, the all-arrow exclusion, the all-mechanism exclusion,
and the underlying side-separation guard in one reusable certificate.
-/
structure DomainCodomainForbiddenTransportAudit
    (context : StructuredSHETransportContext family) : Prop where
  forbidden_domain_to_codomain :
    context.transportSystem.forbiddenIdentification
      context.baseContext.domainStructure.theater
      context.baseContext.codomainStructure.theater
  all_allowed_arrows_blocked :
    ∀ arrow : HodgeTheaterTransportArrow,
      arrow.source = context.baseContext.domainStructure.theater ->
        arrow.target = context.baseContext.codomainStructure.theater ->
          ¬ context.transportSystem.allowed arrow
  all_mechanisms_blocked :
    ∀ mechanism : TransportMechanismId,
      ¬ context.transportSystem.Allows
        context.baseContext.domainStructure.theater
        context.baseContext.codomainStructure.theater
        mechanism
  history_sides_not_identified :
    context.baseContext.domainStructure.theater.side ≠
      context.baseContext.codomainStructure.theater.side

theorem domainCodomainForbiddenTransportAudit
    (context : StructuredSHETransportContext family) :
    DomainCodomainForbiddenTransportAudit context :=
  { forbidden_domain_to_codomain := context.forbidden_domain_to_codomain,
    all_allowed_arrows_blocked := by
      intro arrow hsource htarget
      exact context.noAllowedDomainToCodomain hsource htarget,
    all_mechanisms_blocked := context.noAllowedDomainToCodomainWithMechanism,
    history_sides_not_identified :=
      context.baseContext.domainHistory_ne_codomainHistory }

end StructuredSHETransportContext

/-- Base record for algorithmic-parallel-transport style data. -/
structure APTDatum (family : TransportedRegionFamily source target index) where
  transportSystem : HodgeTheaterTransportSystem
  transportQuotient : HodgeTheaterTransportQuotient transportSystem
  arrow : HodgeTheaterTransportArrow
  arrow_permitted : transportSystem.allowed arrow
  mechanism : TransportMechanismId
  mechanism_eq_arrow : mechanism = arrow.mechanism
  outputFamily : TransportedRegionFamily source target index
  output_eq_family : outputFamily = family

namespace APTDatum

variable {family : TransportedRegionFamily source target index}

def reindex (datum : APTDatum family) (f : newIndex -> index) :
    APTDatum (family.reindex f) :=
  { transportSystem := datum.transportSystem,
    transportQuotient := datum.transportQuotient,
    arrow := datum.arrow,
    arrow_permitted := datum.arrow_permitted,
    mechanism := datum.mechanism,
    mechanism_eq_arrow := datum.mechanism_eq_arrow,
    outputFamily := datum.outputFamily.reindex f,
    output_eq_family := by
      rw [datum.output_eq_family] }

def TransportQuotientEndpoint (datum : APTDatum family) : Prop :=
  datum.transportSystem.allowed datum.arrow ∧
    datum.transportQuotient.classOf datum.arrow.source =
      datum.transportQuotient.classOf datum.arrow.target ∧
    datum.mechanism = datum.arrow.mechanism ∧
    datum.outputFamily = family

theorem transportQuotientEndpoint
    (datum : APTDatum family) :
    datum.TransportQuotientEndpoint :=
  ⟨datum.arrow_permitted,
    datum.transportQuotient.allowedArrowClassEq datum.arrow_permitted,
    datum.mechanism_eq_arrow,
    datum.output_eq_family⟩

end APTDatum

/--
Source-shaped APT construction from a permitted Hodge-theater transport.

The transported output family is still a field, but the APT datum is now tied to
a concrete permitted theater-transport arrow, and Lean records that this arrow
cannot be one of the forbidden identifications.
-/
structure AlgorithmicParallelTransportConstruction
    (family : TransportedRegionFamily source target index) where
  transportSystem : HodgeTheaterTransportSystem
  transportQuotient : HodgeTheaterTransportQuotient transportSystem
  arrow : HodgeTheaterTransportArrow
  permitted : transportSystem.allowed arrow
  outputFamily : TransportedRegionFamily source target index
  output_eq_family : outputFamily = family

namespace AlgorithmicParallelTransportConstruction

variable {family : TransportedRegionFamily source target index}

def reindex
    (construction : AlgorithmicParallelTransportConstruction family)
    (f : newIndex -> index) :
    AlgorithmicParallelTransportConstruction (family.reindex f) :=
  { transportSystem := construction.transportSystem,
    transportQuotient := construction.transportQuotient,
    arrow := construction.arrow,
    permitted := construction.permitted,
    outputFamily := construction.outputFamily.reindex f,
    output_eq_family := by
      rw [construction.output_eq_family] }

def permittedTransport
    (construction : AlgorithmicParallelTransportConstruction family) :
    PermittedHodgeTheaterTransport construction.transportSystem :=
  { arrow := construction.arrow,
    permitted := construction.permitted }

def toAPTDatum
    (construction : AlgorithmicParallelTransportConstruction family) :
    APTDatum family :=
  { transportSystem := construction.transportSystem,
    transportQuotient := construction.transportQuotient,
    arrow := construction.arrow,
    arrow_permitted := construction.permitted,
    mechanism := construction.arrow.mechanism,
    mechanism_eq_arrow := rfl,
    outputFamily := construction.outputFamily,
    output_eq_family := construction.output_eq_family }

theorem toAPTDatum_output_eq_family
    (construction : AlgorithmicParallelTransportConstruction family) :
    construction.toAPTDatum.outputFamily = family :=
  construction.output_eq_family

theorem permittedTransport_arrow
    (construction : AlgorithmicParallelTransportConstruction family) :
    construction.permittedTransport.arrow = construction.arrow :=
  rfl

theorem toAPTDatum_mechanism_eq_arrow
    (construction : AlgorithmicParallelTransportConstruction family) :
    construction.toAPTDatum.mechanism = construction.arrow.mechanism :=
  rfl

theorem toAPTDatum_arrow_eq
    (construction : AlgorithmicParallelTransportConstruction family) :
    construction.toAPTDatum.arrow = construction.arrow :=
  rfl

theorem toAPTDatum_transportQuotientEndpoint
    (construction : AlgorithmicParallelTransportConstruction family) :
    construction.toAPTDatum.TransportQuotientEndpoint :=
  construction.toAPTDatum.transportQuotientEndpoint

theorem toAPTDatum_outputFamily_eq
    (construction : AlgorithmicParallelTransportConstruction family) :
    construction.toAPTDatum.outputFamily = construction.outputFamily :=
  rfl

theorem permitted_not_forbidden
    (construction : AlgorithmicParallelTransportConstruction family) :
    ¬ construction.transportSystem.forbiddenIdentification
        construction.arrow.source construction.arrow.target :=
  construction.permittedTransport.not_forbidden

theorem permitted_arrow_quotient_eq
    (construction : AlgorithmicParallelTransportConstruction family) :
    construction.transportQuotient.classOf construction.arrow.source =
      construction.transportQuotient.classOf construction.arrow.target :=
  construction.transportQuotient.allowedArrowClassEq construction.permitted

def APTEndpoint
    (construction : AlgorithmicParallelTransportConstruction family) : Prop :=
  construction.toAPTDatum.mechanism = construction.arrow.mechanism ∧
    construction.toAPTDatum.arrow = construction.arrow ∧
    construction.toAPTDatum.outputFamily = construction.outputFamily ∧
    construction.toAPTDatum.outputFamily = family ∧
    construction.transportSystem.allowed construction.arrow ∧
    ¬ construction.transportSystem.forbiddenIdentification
      construction.arrow.source construction.arrow.target ∧
    construction.toAPTDatum.TransportQuotientEndpoint

theorem aptEndpoint
    (construction : AlgorithmicParallelTransportConstruction family) :
    construction.APTEndpoint :=
  ⟨construction.toAPTDatum_mechanism_eq_arrow,
    construction.toAPTDatum_arrow_eq,
    construction.toAPTDatum_outputFamily_eq,
    construction.toAPTDatum_output_eq_family,
    construction.permitted,
    construction.permitted_not_forbidden,
    construction.toAPTDatum_transportQuotientEndpoint⟩

/--
Typed audit that an APT datum is realized by a permitted arrow in a named
transport quotient.

This is the quotient-facing strengthening of `APTEndpoint`: the permitted
arrow is not merely allowed and non-forbidden; its endpoints are equal in the
transport quotient carried by the APT construction.
-/
structure APTTransportQuotientAudit
    (construction : AlgorithmicParallelTransportConstruction family) :
    Prop where
  apt_arrow_permitted :
    construction.transportSystem.allowed construction.arrow
  allowed_arrow_related :
    construction.transportQuotient.quotientSetoid.r
      construction.arrow.source construction.arrow.target
  permitted_arrow_quotient_eq :
    construction.transportQuotient.classOf construction.arrow.source =
      construction.transportQuotient.classOf construction.arrow.target
  apt_endpoint :
    construction.APTEndpoint

theorem aptTransportQuotientAudit
    (construction : AlgorithmicParallelTransportConstruction family) :
    APTTransportQuotientAudit construction :=
  { apt_arrow_permitted := construction.permitted,
    allowed_arrow_related :=
      construction.transportQuotient.allowed_arrow_related
        construction.permitted,
    permitted_arrow_quotient_eq :=
      construction.permitted_arrow_quotient_eq,
    apt_endpoint := construction.aptEndpoint }

end AlgorithmicParallelTransportConstruction

def HasStructuredIPL (family : TransportedRegionFamily source target index) : Prop :=
  Nonempty (IPLDatum family)

def HasStructuredAPT (family : TransportedRegionFamily source target index) : Prop :=
  Nonempty (APTDatum family)

/-- Structured evidence for all three qualitative properties of an output family. -/
structure StructuredCertificate (family : TransportedRegionFamily source target index) where
  ipl : IPLDatum family
  she : SHEDatum family
  apt : APTDatum family

namespace StructuredCertificate

variable {family : TransportedRegionFamily source target index}

def reindex (certificate : StructuredCertificate family)
    (f : newIndex -> index) :
    StructuredCertificate (family.reindex f) :=
  { ipl := certificate.ipl.reindex f,
    she := { sharedContext := certificate.she.sharedContext },
    apt := certificate.apt.reindex f }

theorem hasStructuredIPL (certificate : StructuredCertificate family) :
    HasStructuredIPL family :=
  ⟨certificate.ipl⟩

theorem hasStructuredSHE (certificate : StructuredCertificate family) :
    HasStructuredSHE family :=
  ⟨certificate.she⟩

theorem hasStructuredAPT (certificate : StructuredCertificate family) :
    HasStructuredAPT family :=
  ⟨certificate.apt⟩

def ofConstructedIPLSHEAPT
    (iplConstruction : InputPrimeStripLinkConstruction family)
    (sheContext : StructuredSHETransportContext family)
    (aptConstruction : AlgorithmicParallelTransportConstruction family) :
    StructuredCertificate family :=
  { ipl := iplConstruction.toIPLDatum,
    she := sheContext.sheDatum,
    apt := aptConstruction.toAPTDatum }

theorem ofConstructedIPLSHEAPT_hasStructuredIPL
    (iplConstruction : InputPrimeStripLinkConstruction family)
    (sheContext : StructuredSHETransportContext family)
    (aptConstruction : AlgorithmicParallelTransportConstruction family) :
    HasStructuredIPL family :=
  (ofConstructedIPLSHEAPT iplConstruction sheContext aptConstruction).hasStructuredIPL

theorem ofConstructedIPLSHEAPT_hasStructuredSHE
    (iplConstruction : InputPrimeStripLinkConstruction family)
    (sheContext : StructuredSHETransportContext family)
    (aptConstruction : AlgorithmicParallelTransportConstruction family) :
    HasStructuredSHE family :=
  (ofConstructedIPLSHEAPT iplConstruction sheContext aptConstruction).hasStructuredSHE

theorem ofConstructedIPLSHEAPT_hasStructuredAPT
    (iplConstruction : InputPrimeStripLinkConstruction family)
    (sheContext : StructuredSHETransportContext family)
    (aptConstruction : AlgorithmicParallelTransportConstruction family) :
    HasStructuredAPT family :=
  (ofConstructedIPLSHEAPT iplConstruction sheContext aptConstruction).hasStructuredAPT

end StructuredCertificate

theorem apt_output_eq_family {family : TransportedRegionFamily source target index}
    (hapt : HasStructuredAPT family) :
    ∃ datum : APTDatum family, datum.outputFamily = family := by
  rcases hapt with ⟨datum⟩
  exact ⟨datum, datum.output_eq_family⟩

end QualitativeData

end RealLineCopy
end Iut
