import LeanFormal.IUT.IUTIII.Theorem311.MultiradialProfileKernel
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteOutput
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

local instance primeFactForSourceFiniteMultiradial (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

namespace SourceFiniteMultiradial

open ConcreteFiniteTheorem311
open MultiradialKernel
open MultiradialKernel.Core

def core (l : PrimeGeFive) :
    Core (ConcreteFiniteTheorem311.finiteLabel l)
      (ConcreteFiniteTheorem311.ProcessionChoice l) where
  base := ProcessionChoice.base
  level := fun c => c.upperSemiLevel
  ind1 := ProcessionChoice.ind1Act
  ind2 := ProcessionChoice.ind2Act
  ind3 := ProcessionChoice.ind3Lift
  ind1_zero := by
    intro c
    exact ProcessionChoice.ind1_zero c
  ind1_add := by
    intro g h c
    simpa [add_comm] using ProcessionChoice.ind1_add h g c
  ind1_inverse := by
    intro g c
    exact ProcessionChoice.ind1_inverse g c
  ind2_zero := by
    intro c
    exact ProcessionChoice.ind2_zero c
  ind2_add := by
    intro g h c
    simpa [add_comm] using ProcessionChoice.ind2_add h g c
  ind2_inverse := by
    intro g c
    exact ProcessionChoice.ind2_inverse g c
  ind3_zero := by
    intro c
    exact ProcessionChoice.ind3_zero c
  ind3_add := by
    intro m n c
    exact ProcessionChoice.ind3_add m n c
  ind1_ind2_commute := by
    intro g h c
    exact ProcessionChoice.ind1_ind2_commute g h c
  ind1_ind3_commute := by
    intro g n c
    exact ProcessionChoice.ind1_ind3_commute g n c
  ind2_ind3_commute := by
    intro g n c
    exact ProcessionChoice.ind2_ind3_commute g n c
  ind1_level := by
    intro g c
    exact ProcessionChoice.ind1_upperSemiLevel g c
  ind2_level := by
    intro g c
    exact ProcessionChoice.ind2_upperSemiLevel g c
  ind3_level := by
    intro n c
    exact Nat.le_add_right c.upperSemiLevel n

@[simp] theorem core_base (l : PrimeGeFive) :
    (core l).base = ProcessionChoice.base :=
  rfl

@[simp] theorem core_level (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (core l).level c = c.upperSemiLevel :=
  rfl

@[simp] theorem core_ind1 (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (core l).ind1 g c = ProcessionChoice.ind1Act g c :=
  rfl

@[simp] theorem core_ind2 (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (core l).ind2 g c = ProcessionChoice.ind2Act g c :=
  rfl

@[simp] theorem core_ind3 (l : PrimeGeFive)
    (n : Nat) (c : ProcessionChoice l) :
    (core l).ind3 n c = ProcessionChoice.ind3Lift n c :=
  rfl

def profile (l : PrimeGeFive) : Profile (core l) where
  logVolume := (ConcreteFiniteTheorem311.finiteOutput l).logVolume
  possibleImage := (ConcreteFiniteTheorem311.finiteOutput l).possibleImage
  ind1_invariant := by
    intro g c
    exact (ConcreteFiniteTheorem311.finiteOutput l).ind1_invariant g c
  ind2_invariant := by
    intro g c
    exact (ConcreteFiniteTheorem311.finiteOutput l).ind2_invariant g c
  ind3_upper := by
    intro n c
    exact (ConcreteFiniteTheorem311.finiteOutput l).ind3_upper n c
  possibleImage_nonempty := by
    intro c
    exact (ConcreteFiniteTheorem311.finiteOutput l).possibleImage_nonempty c
  possibleImage_ind1 := by
    intro g c
    exact (ConcreteFiniteTheorem311.finiteOutput l).possibleImage_ind1 g c
  possibleImage_ind2 := by
    intro g c
    exact (ConcreteFiniteTheorem311.finiteOutput l).possibleImage_ind2 g c
  possibleImage_ind3 := by
    intro n c z hz
    exact (ConcreteFiniteTheorem311.finiteOutput l).possibleImage_ind3 n c z hz

@[simp] theorem profile_logVolume (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (profile l).logVolume c = normalizedLogVolume l c :=
  rfl

@[simp] theorem profile_possibleImage (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (profile l).possibleImage c = possibleImage l c :=
  rfl

theorem profile_logVolume_formula (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (profile l).logVolume c = thetaLogVolume l +
      (c.upperSemiLevel : Real) := by
  change normalizedLogVolume l c = _
  rfl

theorem profile_ind1_invariant (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (profile l).logVolume ((core l).ind1 g c) =
      (profile l).logVolume c :=
  (profile l).ind1_invariant g c

theorem profile_ind2_invariant (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (profile l).logVolume ((core l).ind2 g c) =
      (profile l).logVolume c :=
  (profile l).ind2_invariant g c

theorem profile_ind3_upper (l : PrimeGeFive)
    (n : Nat) (c : ProcessionChoice l) :
    (profile l).logVolume c ≤ (profile l).logVolume ((core l).ind3 n c) :=
  (profile l).ind3_upper n c

theorem profile_possible_nonempty (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    ((profile l).possibleImage c).Nonempty :=
  (profile l).possibleImage_nonempty c

theorem profile_possible_ind1 (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (profile l).possibleImage ((core l).ind1 g c) =
      (profile l).possibleImage c :=
  (profile l).possibleImage_ind1 g c

theorem profile_possible_ind2 (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (profile l).possibleImage ((core l).ind2 g c) =
      (profile l).possibleImage c :=
  (profile l).possibleImage_ind2 g c

theorem profile_possible_ind3 (l : PrimeGeFive)
    (n : Nat) (c : ProcessionChoice l) (z : Real)
    (hz : z ∈ (profile l).possibleImage c) :
    ∃ w, w ∈ (profile l).possibleImage ((core l).ind3 n c) ∧ z ≤ w :=
  (profile l).possibleImage_ind3 n c z hz

def emptyRouteOutput (l : PrimeGeFive) :
    MultiradialKernel.Output (core l) (profile l) where
  source := ProcessionChoice.base
  route := []
  source_image_nonempty := profile_possible_nonempty l ProcessionChoice.base

theorem emptyRouteOutput_target (l : PrimeGeFive) :
    (Output.target (emptyRouteOutput l)) = ProcessionChoice.base :=
  rfl

theorem emptyRouteOutput_level (l : PrimeGeFive) :
    (core l).level (Output.target (emptyRouteOutput l)) = 0 := by
  rfl

theorem emptyRouteOutput_log_volume (l : PrimeGeFive) :
    (profile l).logVolume (Output.target (emptyRouteOutput l)) =
      thetaLogVolume l := by
  change normalizedLogVolume l ProcessionChoice.base = thetaLogVolume l
  exact normalizedLogVolume_base l

def routeOutput (l : PrimeGeFive)
    (source : ProcessionChoice l)
    (route : List (RouteStep (ConcreteFiniteTheorem311.finiteLabel l))) :
    MultiradialKernel.Output (core l) (profile l) where
  source := source
  route := route
  source_image_nonempty := profile_possible_nonempty l source

theorem routeOutput_target (l : PrimeGeFive)
    (source : ProcessionChoice l)
    (route : List (RouteStep (ConcreteFiniteTheorem311.finiteLabel l))) :
    (Output.target (routeOutput l source route)) =
      applyRoute (core l) route source :=
  rfl

theorem routeOutput_level_monotone (l : PrimeGeFive)
    (source : ProcessionChoice l)
    (route : List (RouteStep (ConcreteFiniteTheorem311.finiteLabel l))) :
    (core l).level source ≤
      (core l).level (Output.target (routeOutput l source route)) :=
  Output.target_level_ge (routeOutput l source route)

theorem routeOutput_log_volume_monotone (l : PrimeGeFive)
    (source : ProcessionChoice l)
    (route : List (RouteStep (ConcreteFiniteTheorem311.finiteLabel l))) :
    (profile l).logVolume source ≤
      (profile l).logVolume (Output.target (routeOutput l source route)) :=
  Output.source_logVolume_le_target (routeOutput l source route)

theorem routeOutput_target_image_upper (l : PrimeGeFive)
    (source : ProcessionChoice l)
    (route : List (RouteStep (ConcreteFiniteTheorem311.finiteLabel l)))
    (z : Real) (hz : z ∈ (profile l).possibleImage source) :
    ∃ w, w ∈ (profile l).possibleImage
      (Output.target (routeOutput l source route)) ∧ z ≤ w :=
  Output.target_image_upper (routeOutput l source route) z hz

def sameLevelRoute {l : PrimeGeFive}
    (a b : ProcessionChoice l) :
    List (RouteStep (ConcreteFiniteTheorem311.finiteLabel l)) :=
  [ .ind1 (-a.processionLabel),
    .ind2 (b.tensorLabel - a.tensorLabel),
    .ind1 b.processionLabel ]

theorem sameLevelRoute_horizontal {l : PrimeGeFive}
    (a b : ProcessionChoice l) (step : RouteStep
      (ConcreteFiniteTheorem311.finiteLabel l))
    (hstep : step ∈ sameLevelRoute a b) :
    horizontal step := by
  simp only [sameLevelRoute, List.mem_cons, List.not_mem_nil] at hstep
  rcases hstep with h | h
  · subst step
    exact horizontal_of_ind1 _
  rcases h with h | h
  · subst step
    exact horizontal_of_ind2 _
  rcases h with h | h
  · subst step
    exact horizontal_of_ind1 _
  exact False.elim h

theorem sameLevelRoute_apply
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    applyRoute (core l) (sameLevelRoute a b) a = b := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  dsimp at hlevel ⊢
  subst b₃
  simp [sameLevelRoute, applyRoute, applyStep, core,
    ProcessionChoice.ind1Act, ProcessionChoice.ind2Act,
    sub_eq_add_neg, add_comm]

theorem sameLevel_generated
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    GeneratedEqualityRelation (core l) a b := by
  have hroute : ∀ step ∈ sameLevelRoute a b, horizontal step := by
    intro step hstep
    exact sameLevelRoute_horizontal a b step hstep
  have hgen := generated_of_horizontal_route (core l)
    (sameLevelRoute a b) hroute a
  rw [sameLevelRoute_apply hlevel] at hgen
  exact hgen

theorem sameLevel_quotient_eq
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
  generatedQuotientMap (core l) a = generatedQuotientMap (core l) b :=
  generatedQuotientMap_eq_of_generated (core l) (sameLevel_generated hlevel)

theorem sameLevel_logVolume_eq
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (profile l).logVolume a = (profile l).logVolume b := by
  have hroute : ∀ step ∈ sameLevelRoute a b, horizontal step := by
    intro step hstep
    exact sameLevelRoute_horizontal a b step hstep
  have hlog := logVolume_applyRoute_horizontal (profile l)
    (sameLevelRoute a b) hroute a
  rw [sameLevelRoute_apply hlevel] at hlog
  exact hlog.symm

theorem sameLevel_image_eq
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (profile l).possibleImage a = (profile l).possibleImage b := by
  exact (profile l).possibleImage_respects_generated
    (sameLevel_generated hlevel)

theorem differentLevel_quotient_ne
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel ≠ b.upperSemiLevel) :
    generatedQuotientMap (core l) a ≠ generatedQuotientMap (core l) b := by
  apply generatedQuotientMap_ne_of_level_ne
  exact hlevel

theorem quotient_image_nonempty
    (l : PrimeGeFive) (q : GeneratedQuotient (core l)) :
    ((profile l).quotientPossibleImage q).Nonempty :=
  (profile l).quotientPossibleImage_nonempty q

theorem quotient_image_ind3_upper
    {l : PrimeGeFive} (a : ProcessionChoice l) (n : Nat)
    (z : Real) (hz : z ∈ (profile l).quotientPossibleImage
      (generatedQuotientMap (core l) a)) :
    ∃ w, w ∈ (profile l).quotientPossibleImage
      (generatedQuotientMap (core l) ((core l).ind3 n a)) ∧ z ≤ w :=
  (profile l).quotientPossibleImage_ind3_upper a n z hz

theorem quotient_image_ind3_upper_concrete
    {l : PrimeGeFive} (a : ProcessionChoice l) (n : Nat)
    (z : Real) (hz : z ∈ (profile l).quotientPossibleImage
      (generatedQuotientMap (core l) a)) :
    ∃ w, w ∈ (profile l).quotientPossibleImage
      (generatedQuotientMap (core l)
        (ProcessionChoice.ind3Lift n a)) ∧ z ≤ w := by
  simpa using quotient_image_ind3_upper a n z hz

theorem source_output_procession_agrees (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (profile l).logVolume c =
      (SourceFiniteTheorem311.output l).procession.logVolume c :=
  rfl

theorem source_output_ind1_agrees (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (profile l).logVolume ((core l).ind1 g c) =
      (SourceFiniteTheorem311.output l).procession.logVolume
        (ProcessionChoice.ind1Act g c) :=
  rfl

theorem source_output_ind2_agrees (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (profile l).logVolume ((core l).ind2 g c) =
      (SourceFiniteTheorem311.output l).procession.logVolume
        (ProcessionChoice.ind2Act g c) :=
  rfl

theorem source_output_ind3_agrees (l : PrimeGeFive)
    (n : Nat) (c : ProcessionChoice l) :
    (profile l).logVolume ((core l).ind3 n c) =
      (SourceFiniteTheorem311.output l).procession.logVolume
        (ProcessionChoice.ind3Lift n c) :=
  rfl

theorem source_output_image_agrees (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (profile l).possibleImage c =
      (SourceFiniteTheorem311.output l).procession.possibleImage c :=
  rfl

theorem source_output_core_base_agrees (l : PrimeGeFive) :
    (core l).base = (SourceFiniteTheorem311.output l).procession.baseChoice :=
  rfl

theorem source_output_level_agrees (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (core l).level c = c.upperSemiLevel :=
  rfl

theorem source_output_reduction_kernel (l : PrimeGeFive) :
    (ConcreteSourceEtaleThetaBridge.reduction l).ker =
      AddSubgroup.zmultiples (l.value : ℤ) :=
  ConcreteSourceEtaleThetaBridge.reduction_kernel l

theorem source_output_generator_order (l : PrimeGeFive) :
    addOrderOf (ConcreteSourceEtaleThetaBridge.generator l) = l.value :=
  ConcreteSourceEtaleThetaBridge.generator_order l

theorem source_output_root_compatibility (l : PrimeGeFive) (n : ℤ) :
    (ConcreteSourceEtaleThetaBridge.packet l).integerRoot n =
      (ConcreteSourceEtaleThetaBridge.roots l).roots (n : ℚ) :=
  ConcreteSourceEtaleThetaBridge.integer_root_compatible l n

theorem source_output_history_volume (l : PrimeGeFive) :
    (SourceFiniteTheorem311.output l).history.terminal.thetaPacket.logVolume =
      ConcreteSourceEtaleThetaBridge.thetaLogVolume l :=
  SourceFiniteTheorem311.output_history_packet_volume l

theorem source_output_determinant_log (l : PrimeGeFive) :
    Real.log (ConcreteSourceHistoryLinkBridge.sourceHistoryDeterminant l) =
      ConcreteSourceEtaleThetaBridge.thetaLogVolume l :=
  ConcreteSourceHistoryLinkBridge.sourceHistoryDeterminant_log l

theorem source_output_normalization :
    ConcreteSourceHistoryLinkBridge.sourceNormalizationPacket.weightedLogVolume =
      (ConcreteSourceHistoryLinkBridge.sourceNormalizationPacket.commonTensorDegree :
        Real) * ConcreteSourceHistoryLinkBridge.sourceNormalizationPacket.normalizedLogVolume :=
  ConcreteSourceHistoryLinkBridge.sourceNormalizationPacket_weighted_identity

end SourceFiniteMultiradial

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSourceMultiradialKernel : Obligation :=
  { id := "IUT-III.concrete-source-multiradial-kernel"
    source := "IUT III, Theorem 3.11 (finite source carrier and route kernel)"
    status := VerificationStatus.interface
    note :=
      "The generic route kernel proves quotient representative independence, " ++
        "horizontal Ind1/Ind2 invariance, vertical Ind3 upper bounds, and route " ++
        "composition. Its Q(i)-at-5 instance proves same-level generation and " ++
        "connects the result to the source algebraic theta/history output. It is " ++
        "not the arbitrary D-prime-strip multiradial algorithm."
    dependsOn :=
      [ "IUT-III.concrete-source-theorem311-output",
        "IUT-III.generic-quotient-transport",
        "IUT-III.orbit-quotient-transport",
        "IUT-III.Ind3.upper-semi-kernel" ] }

end LeanFormal.IUT.Audit
