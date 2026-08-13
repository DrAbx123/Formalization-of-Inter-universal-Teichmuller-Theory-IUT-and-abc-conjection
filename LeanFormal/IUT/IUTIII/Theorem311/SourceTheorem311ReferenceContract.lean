import LeanFormal.IUT.IUTIII.Theorem311.SourceTheorem311Assembly
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Theorem 3.11 reference-shaped output contract

  Theorem 3.11 is stated in three parts and the proof in the paper is a
  reference-to-definitions proof.  The existing typed assembly proves the
  corresponding fields from a `SourceP1P2Bundle`; this module gives that
  result a record whose fields follow the order and directions of the paper.

  This is a consumer-facing contract, not an existence shortcut.  Its only
  input is the already source-facing bundle of the cited constructions.  No
  field below is used to construct that bundle, and no finite model is used in
  place of the original source carrier.  The final audit therefore continues
  to distinguish this checked output contract from the still-open
  arithmetic-to-source construction.

  Source: IUT III, Theorem 3.11(i)--(iii), with Props. 3.2, 3.4, 3.5, 3.7,
  3.9, 3.10 and Theorem 1.5/Prop. 2.1/Cor. 2.3 as cited in the statement.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe uv upi umon ui u v w ux uy

namespace Theorem311Source

open OriginalInput
open SourceDependencyChain
open SourceHodgeTheaterBridge

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable {W : SourceInternalWiring I R P X Y}
variable {S : SourceP1P2Input (I := I) (R := R) (P := P)
  (X := X) (Y := Y) W}

/-! ## The reference-shaped record -/

structure SourceTheorem311ReferenceOutput
    (B : SourceP1P2Bundle W S) where
  output : Theorem311Output R.input
  partI : PartI R.input
  partII : PartII R.input
  partIII : PartIII R.input
  output_partI : output.part_i = partI
  output_partII : output.part_ii = partII
  output_partIII : output.part_iii = partIII
  output_eq : output = B.dependency.output

  /- H1/H2 and procession arrows used before the three parts. -/
  h1_source : W.h1.source = I.initial
  h2_h1 : W.h2.h1 = W.h1
  h2_procession_toD : W.h2.fProcession.toD = W.h2.dProcession
  h2_permutation : W.h2.permutation = P
  stage_cardinality : ∀ n, Fintype.card (Fin (n + 1)) = n + 1
  stage_inclusion_injective : ∀ {n m} (h : n ≤ m),
    Function.Injective (W.h2.fProcession.inclusion h).map

  /- Part (i): procession, packet, volume, and Ind1/Ind2 descent. -/
  t1 : partI = _root_.LeanFormal.IUT.Theorem311Source.partI R.input
  t1_source : partI.source = R.input.core.base
  t1_quotient : partI.quotient = quotientMap R.input partI.source
  t1_nonempty : (quotientImage R.input partI.quotient).Nonempty
  t1_level_bound :
    quotientLevel R.input partI.quotient ≤
      quotientLevel R.input
        (quotientMap R.input (R.input.core.ind3 0 partI.source))
  t1_volume_bound :
    quotientVolume R.input partI.quotient ≤
      quotientVolume R.input
        (quotientMap R.input (R.input.core.ind3 0 partI.source))
  t1_ind1 : ∀ g c,
    quotientVolume R.input
        (quotientMap R.input (R.input.core.ind1 g c)) =
      quotientVolume R.input (quotientMap R.input c)
  t1_ind2 : ∀ g c,
    quotientVolume R.input
        (quotientMap R.input (R.input.core.ind2 g c)) =
      quotientVolume R.input (quotientMap R.input c)
  t1_packet_alignment :
    B.proposition32.profile R.procession.base =
      R.packet.logVolume R.procession.base
  t1_volume_alignment :
    B.proposition39.logVolume R.procession.base =
      R.packet.logVolume R.procession.base

  /- Part (ii): labelled Kummer and the two upper-semi directions. -/
  t2 : partII = _root_.LeanFormal.IUT.Theorem311Source.partII R.input
  t2_vertical : partII.vertical = verticalCorrespondence R.input
  t2_siteData : partII.siteData = R.input.verticalSite
  t2_labelled_bijective : ∀ c,
    Function.Bijective (R.input.labelledKummer c).map
  t2_nonarchimedean : ∀ m c z,
    z ∈ R.input.profile.possibleImage c →
      ∃ w, w ∈ R.input.profile.possibleImage
        (R.input.core.ind3 m c) ∧ z ≤ w
  t2_archimedean : ∀ m c z,
    z ∈ R.input.profile.possibleImage
        (R.input.core.ind3 m c) →
      ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y
  t2_vertical_monotone : ∀ {m n} (h : m ≤ n) z,
    z ∈ R.vertical.vertical.image m →
      ∃ y, y ∈ R.vertical.vertical.image n ∧ z ≤ y
  t2_kummer_left : ∀ c a,
    (R.input.labelledKummer c).inverse
        ((R.input.labelledKummer c).map a) = a
  t2_kummer_right : ∀ c b,
    (R.input.labelledKummer c).map
        ((R.input.labelledKummer c).inverse b) = b

  /- Proposition 3.4/3.7/3.9 data consumed by the global part. -/
  p1_lgp : B.proposition34 = SourceP1.proposition34 S.lgp
  p1_volume : B.proposition39 = SourceP1.proposition39 R S.volume
  p1_tensor_positive : ∀ c n, 0 < B.proposition39.tensorPower c n
  p1_tensor_log : ∀ c n,
    Real.log (B.proposition39.tensorPower c n) =
      n * B.proposition39.logVolume c
  p1_lattice_bound : ∀ c,
    B.proposition39.logVolume c ≤ B.proposition39.latticeIndex c
  p2_theorem15 : B.theorem15 = SourceP2.theorem15 R
  p2_theorem15_vertical : ∀ n c,
    B.theorem15.vertical n c = R.procession.ind3 n c
  p2_theorem15_horizontal : ∀ g c,
    B.theorem15.horizontal g c = R.procession.ind1 g c
  p2_proposition21 : B.proposition21 = SourceP2.proposition21 S.kummer
  p2_proposition21_bijective :
    Function.Bijective B.proposition21.correspondence.map
  p2_corollary23 : B.proposition23 = SourceP2.corollary23 S.permutation
  p2_corollary23_permutation :
    Function.Bijective B.proposition23.permutation

  /- Proposition 3.10 and Theorem 3.11(iii). -/
  t3 : partIII = _root_.LeanFormal.IUT.Theorem311Source.partIII R.input
  t3_timesMu : partIII.timesMuLink = R.input.horizontal
  t3_environment : partIII.environmentLink = R.input.horizontal
  t3_permutation : ∀ c,
    R.input.family.link (R.input.family.permutation c)
        (R.input.family.permutation c) c =
      R.input.family.link c c c
  t3_horizontal : ∀ c,
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c)
  t3_evaluation : ∀ c,
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap
          (R.input.horizontal.lower c))
  t3_label : ∀ c,
    (R.input.labelledKummer c).label
        (R.input.horizontal.left c) =
      (R.input.labelledKummer c).label
        (R.input.horizontal.lower c)

  /- Final output and the three indeterminacy directions. -/
  output_source : output.source = R.input.core.base
  output_quotient : output.quotient = quotientMap R.input output.source
  output_labelled : ∀ c,
    Function.Bijective (R.input.labelledKummer c).map
  output_ind1 : ∀ {a b}, Ind1Relation R.input a b →
    quotientMap R.input a = quotientMap R.input b
  output_ind2 : ∀ {a b}, Ind2Relation R.input a b →
    quotientMap R.input a = quotientMap R.input b
  output_ind3 : ∀ n c z,
    z ∈ R.input.profile.possibleImage c →
      ∃ w, w ∈ R.input.profile.possibleImage
        (R.input.core.ind3 n c) ∧ z ≤ w
  output_horizontal : ∀ c,
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c)
  output_evaluation : ∀ c,
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap
          (R.input.horizontal.lower c))

namespace SourceTheorem311ReferenceOutput

variable {B : SourceP1P2Bundle W S}

def assemble (B : SourceP1P2Bundle W S) :
    SourceTheorem311ReferenceOutput B where
  output := B.dependency.output
  partI := B.dependency.output.part_i
  partII := B.dependency.output.part_ii
  partIII := B.dependency.output.part_iii
  output_partI := rfl
  output_partII := rfl
  output_partIII := rfl
  output_eq := rfl
  h1_source := W.h1_source
  h2_h1 := W.h2_h1
  h2_procession_toD := W.h2_procession_toD
  h2_permutation := W.h2_permutation
  stage_cardinality := fun n => I.h2Package_stage_cardinality P n
  stage_inclusion_injective := by
    intro n m h
    rw [W.h2_canonical]
    exact I.h2Package_stage_inclusion_injective P h
  t1 := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t1_part
        (SourceTheorem311Layers.assemble B))
  t1_source := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t1_source
        (SourceTheorem311Layers.assemble B))
  t1_quotient := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t1_source_map
        (SourceTheorem311Layers.assemble B))
  t1_nonempty := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t1_source_image_nonempty
        (SourceTheorem311Layers.assemble B))
  t1_level_bound := by
    have hq : B.dependency.output.part_i.quotient =
        quotientMap R.input B.dependency.output.part_i.source := by
      simpa [SourceTheorem311Layers.assemble] using
        (SourceTheorem311Layers.output_part_i_source_map
          (SourceTheorem311Layers.assemble B))
    rw [hq]
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t1_level_source_bound
        (SourceTheorem311Layers.assemble B))
  t1_volume_bound := by
    have hq : B.dependency.output.part_i.quotient =
        quotientMap R.input B.dependency.output.part_i.source := by
      simpa [SourceTheorem311Layers.assemble] using
        (SourceTheorem311Layers.output_part_i_source_map
          (SourceTheorem311Layers.assemble B))
    rw [hq]
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t1_volume_source_bound
        (SourceTheorem311Layers.assemble B))
  t1_ind1 := by
    intro g c
    exact SourceTheorem311Layers.t1_ind1_volume
      (SourceTheorem311Layers.assemble B) g c
  t1_ind2 := by
    intro g c
    exact SourceTheorem311Layers.t1_ind2_volume
      (SourceTheorem311Layers.assemble B) g c
  t1_packet_alignment := by
    exact SourceTheorem311Layers.t1_packet_alignment
      (SourceTheorem311Layers.assemble B)
  t1_volume_alignment := by
    rw [B.proposition39_eq]
    exact SourceP1.proposition39_log_volume R S.volume R.procession.base
  t2 := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t2_part
        (SourceTheorem311Layers.assemble B))
  t2_vertical := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t2_vertical
        (SourceTheorem311Layers.assemble B))
  t2_siteData := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t2_siteData
        (SourceTheorem311Layers.assemble B))
  t2_labelled_bijective := by
    intro c
    exact SourceTheorem311Layers.output_part_ii_kummer_bijective
      (SourceTheorem311Layers.assemble B) c
  t2_nonarchimedean := by
    intro m c z hz
    exact SourceTheorem311Layers.output_part_ii_nonarchimedean
      (SourceTheorem311Layers.assemble B) m c z hz
  t2_archimedean := by
    intro m c z hz
    exact SourceTheorem311Layers.output_part_ii_archimedean
      (SourceTheorem311Layers.assemble B) m c z hz
  t2_vertical_monotone := by
    intro m n h z hz
    exact SourceProposition35Vertical.vertical_monotone_at
      (SourceP1.proposition35 R) m n h z hz
  t2_kummer_left := by
    intro c a
    exact SourceP1.proposition35_kummer_left R c a
  t2_kummer_right := by
    intro c b
    exact SourceP1.proposition35_kummer_right R c b
  p1_lgp := B.proposition34_eq
  p1_volume := B.proposition39_eq
  p1_tensor_positive := by
    intro c n
    exact B.proposition39.tensor_power_positive c n
  p1_tensor_log := by
    intro c n
    exact B.proposition39.tensor_power_log c n
  p1_lattice_bound := by
    intro c
    exact B.proposition39.lattice_bound_at c
  p2_theorem15 := B.theorem15_eq
  p2_theorem15_vertical := by
    intro n c
    exact B.theorem15.vertical_eq_ind3 n c
  p2_theorem15_horizontal := by
    intro g c
    exact B.theorem15.horizontal_eq_ind1 g c
  p2_proposition21 := B.proposition21_eq
  p2_proposition21_bijective := B.proposition21.map_bijective
  p2_corollary23 := B.proposition23_eq
  p2_corollary23_permutation := B.proposition23.permutation_bijective
  t3 := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t3_part
        (SourceTheorem311Layers.assemble B))
  t3_timesMu := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t3_timesMu
        (SourceTheorem311Layers.assemble B))
  t3_environment := by
    simpa [SourceTheorem311Layers.assemble] using
      (SourceTheorem311Layers.t3_environment
        (SourceTheorem311Layers.assemble B))
  t3_permutation := by
    intro c
    exact SourceTheorem311Layers.output_part_iii_permutation
      (SourceTheorem311Layers.assemble B) c
  t3_horizontal := by
    intro c
    exact SourceTheorem311Layers.output_horizontal
      (SourceTheorem311Layers.assemble B) c
  t3_evaluation := by
    intro c
    exact SourceTheorem311Layers.output_evaluation
      (SourceTheorem311Layers.assemble B) c
  t3_label := by
    intro c
    exact SourceTheorem311Layers.output_part_iii_label
      (SourceTheorem311Layers.assemble B) c
  output_source := by
    exact SourceTheorem311Layers.output_source
      (SourceTheorem311Layers.assemble B)
  output_quotient := by
    exact SourceTheorem311Layers.output_quotient
      (SourceTheorem311Layers.assemble B)
  output_labelled := by
    intro c
    exact SourceTheorem311Layers.output_labelled
      (SourceTheorem311Layers.assemble B) c
  output_ind1 := by
    intro a b h
    exact SourceTheorem311Layers.output_ind1_descent
      (SourceTheorem311Layers.assemble B) h
  output_ind2 := by
    intro a b h
    exact SourceTheorem311Layers.output_ind2_descent
      (SourceTheorem311Layers.assemble B) h
  output_ind3 := by
    intro n c z hz
    exact SourceTheorem311Layers.output_ind3
      (SourceTheorem311Layers.assemble B) n c z hz
  output_horizontal := by
    intro c
    exact SourceTheorem311Layers.output_horizontal
      (SourceTheorem311Layers.assemble B) c
  output_evaluation := by
    intro c
    exact SourceTheorem311Layers.output_evaluation
      (SourceTheorem311Layers.assemble B) c

theorem output_recovered (C : SourceTheorem311ReferenceOutput B) :
    C.output = B.dependency.output := by
  exact C.output_eq

theorem partI_recovered (C : SourceTheorem311ReferenceOutput B) :
    C.partI = _root_.LeanFormal.IUT.Theorem311Source.partI R.input :=
  C.t1

theorem partII_recovered (C : SourceTheorem311ReferenceOutput B) :
    C.partII = _root_.LeanFormal.IUT.Theorem311Source.partII R.input :=
  C.t2

theorem partIII_recovered (C : SourceTheorem311ReferenceOutput B) :
    C.partIII = _root_.LeanFormal.IUT.Theorem311Source.partIII R.input :=
  C.t3

theorem source_recovered (C : SourceTheorem311ReferenceOutput B) :
    C.output.source = R.input.core.base :=
  C.output_source

theorem quotient_recovered (C : SourceTheorem311ReferenceOutput B) :
    C.output.quotient = quotientMap R.input C.output.source :=
  C.output_quotient

theorem labelled_recovered (C : SourceTheorem311ReferenceOutput B)
    (c : Choice) : Function.Bijective
      (R.input.labelledKummer c).map :=
  C.output_labelled c

theorem ind1_recovered (C : SourceTheorem311ReferenceOutput B)
    {a b : Choice} (h : Ind1Relation R.input a b) :
    quotientMap R.input a = quotientMap R.input b :=
  C.output_ind1 h

theorem ind2_recovered (C : SourceTheorem311ReferenceOutput B)
    {a b : Choice} (h : Ind2Relation R.input a b) :
    quotientMap R.input a = quotientMap R.input b :=
  C.output_ind2 h

theorem ind3_recovered (C : SourceTheorem311ReferenceOutput B)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 n c) ∧ z ≤ w :=
  C.output_ind3 n c z hz

theorem horizontal_recovered (C : SourceTheorem311ReferenceOutput B)
    (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) :=
  C.output_horizontal c

theorem evaluation_recovered (C : SourceTheorem311ReferenceOutput B)
    (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  C.output_evaluation c

theorem arrow_chain (C : SourceTheorem311ReferenceOutput B) :
    W.h1.source = I.initial ∧ W.h2.h1 = W.h1 ∧
      W.h2.fProcession.toD = W.h2.dProcession ∧
      W.h2.permutation = P ∧
      C.output.source = R.input.core.base ∧
      C.output.quotient = quotientMap R.input C.output.source :=
  by
    exact And.intro C.h1_source (And.intro C.h2_h1
      (And.intro C.h2_procession_toD (And.intro C.h2_permutation
        (And.intro C.output_source C.output_quotient))))

theorem three_parts (C : SourceTheorem311ReferenceOutput B) :
    C.partI = _root_.LeanFormal.IUT.Theorem311Source.partI R.input ∧
      C.partII = _root_.LeanFormal.IUT.Theorem311Source.partII R.input ∧
      C.partIII = _root_.LeanFormal.IUT.Theorem311Source.partIII R.input :=
  ⟨partI_recovered C, partII_recovered C, partIII_recovered C⟩

theorem upper_semi_directions (C : SourceTheorem311ReferenceOutput B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c) ∧ z ≤ w :=
  C.t2_nonarchimedean m c z hz

theorem upper_semi_reverse (C : SourceTheorem311ReferenceOutput B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c)) :
    ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y :=
  C.t2_archimedean m c z hz

theorem horizontal_evaluation_pair
    (C : SourceTheorem311ReferenceOutput B) (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
        R.input.horizontal.right (R.input.horizontal.lower c) ∧
      R.input.evaluation.localMap (R.input.horizontal.left c) =
        R.input.horizontal.right
          (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  ⟨C.t3_horizontal c, C.t3_evaluation c⟩

theorem source_reference_output_status : True := by
  trivial

end SourceTheorem311ReferenceOutput

def canonicalReferenceOutput
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    SourceTheorem311ReferenceOutput
      (SourceP1P2Bundle.canonical A P K S) :=
  SourceTheorem311ReferenceOutput.assemble
    (SourceP1P2Bundle.canonical A P K S)

theorem canonical_reference_parts
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    let C := canonicalReferenceOutput A P K S
    C.partI = _root_.LeanFormal.IUT.Theorem311Source.partI R.input ∧
      C.partII = _root_.LeanFormal.IUT.Theorem311Source.partII R.input ∧
      C.partIII = _root_.LeanFormal.IUT.Theorem311Source.partIII R.input := by
  dsimp [canonicalReferenceOutput]
  exact SourceTheorem311ReferenceOutput.three_parts
    (SourceTheorem311ReferenceOutput.assemble
      (SourceP1P2Bundle.canonical A P K S))

end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311ReferenceOutputContract : Obligation :=
  { id := "IUT-III.theorem-3.11-reference-output-contract"
    source := "IUT III, Theorem 3.11(i)--(iii)"
    status := VerificationStatus.interface
    note :=
      "SourceTheorem311ReferenceOutput mirrors the three source parts and " ++
        "their upper-semi, Kummer, volume, permutation, and evaluation " ++
        "directions. It is constructed from SourceP1P2Bundle, so it closes " ++
        "the output arrow contract but does not claim arithmetic-to-source " ++
        "existence."
    dependsOn := ["IUT-III.theorem-3.11-internal-wiring",
      "IUT-III.theorem-3.11-conditional-T1-T3-assembly"] }

end LeanFormal.IUT.Audit
