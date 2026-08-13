import LeanFormal.IUT.IUTIII.Theorem311.SourceInternalWiring

/-!
  # T1/T2/T3 assembly for Theorem 3.11

  `SourceInternalWiring` closes the arrows through the cited Proposition 3.x
  boundaries, but the three theorem parts were previously visible only through
  the undifferentiated dependency package.  This module gives each part its
  own typed node and records the recovery equations all the way back to the
  `OriginalInput`.

  The construction consumes a `SourceP1P2Bundle`.  That bundle is the explicit
  source-facing boundary for the cited IUT I--III constructions; this file does
  not manufacture it from arithmetic data and therefore does not change the
  source-faithful status of Theorem 3.11.
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
variable {B : SourceP1P2Bundle W S}

/-! ## The three typed theorem layers -/

structure SourceTheorem311Layers
    (B : SourceP1P2Bundle W S) where
  t1 : PartI R.input
  t2 : PartII R.input
  t3 : PartIII R.input
  output : Theorem311Output R.input
  t1_eq : t1 = B.dependency.output.part_i
  t2_eq : t2 = B.dependency.output.part_ii
  t3_eq : t3 = B.dependency.output.part_iii
  output_eq : output = B.dependency.output

namespace SourceTheorem311Layers

def assemble (B : SourceP1P2Bundle W S) : SourceTheorem311Layers B where
  t1 := B.dependency.output.part_i
  t2 := B.dependency.output.part_ii
  t3 := B.dependency.output.part_iii
  output := B.dependency.output
  t1_eq := rfl
  t2_eq := rfl
  t3_eq := rfl
  output_eq := rfl

def canonical
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    SourceTheorem311Layers
      (SourceP1P2Bundle.canonical A P K S) :=
  assemble (SourceP1P2Bundle.canonical A P K S)

theorem t1_recovered (L : SourceTheorem311Layers B) :
    L.t1 = B.dependency.output.part_i :=
  L.t1_eq

theorem t2_recovered (L : SourceTheorem311Layers B) :
    L.t2 = B.dependency.output.part_ii :=
  L.t2_eq

theorem t3_recovered (L : SourceTheorem311Layers B) :
    L.t3 = B.dependency.output.part_iii :=
  L.t3_eq

theorem output_recovered (L : SourceTheorem311Layers B) :
    L.output = B.dependency.output :=
  L.output_eq

theorem dependency_part_i (B : SourceP1P2Bundle W S) :
    B.dependency.output.part_i = partI R.input := by
  exact (B.dependency.output_parts).1

theorem dependency_part_ii (B : SourceP1P2Bundle W S) :
    B.dependency.output.part_ii = partII R.input := by
  exact (B.dependency.output_parts).2.1

theorem dependency_part_iii (B : SourceP1P2Bundle W S) :
    B.dependency.output.part_iii = partIII R.input := by
  exact (B.dependency.output_parts).2.2

theorem t1_part (L : SourceTheorem311Layers B) :
    L.t1 = partI R.input := by
  rw [L.t1_eq]
  exact dependency_part_i B

theorem t2_part (L : SourceTheorem311Layers B) :
    L.t2 = partII R.input := by
  rw [L.t2_eq]
  exact dependency_part_ii B

theorem t3_part (L : SourceTheorem311Layers B) :
    L.t3 = partIII R.input := by
  rw [L.t3_eq]
  exact dependency_part_iii B

/-! ## T1: multiradial representation -/

theorem t1_source (L : SourceTheorem311Layers B) :
    L.t1.source = R.input.core.base := by
  rw [L.t1_part]
  exact partI_source R.input

theorem t1_quotient (L : SourceTheorem311Layers B) :
    L.t1.quotient = quotientMap R.input R.input.core.base := by
  rw [L.t1_part]
  exact partI_quotient R.input

theorem t1_source_map (L : SourceTheorem311Layers B) :
    L.t1.quotient = quotientMap R.input L.t1.source := by
  rw [L.t1_part]
  exact partI_source_map R.input

theorem t1_source_image_nonempty (L : SourceTheorem311Layers B) :
    (quotientImage R.input L.t1.quotient).Nonempty := by
  rw [L.t1_part]
  exact partI_nonempty R.input

theorem t1_level_bound (L : SourceTheorem311Layers B) :
    quotientLevel R.input L.t1.quotient ≤
      quotientLevel R.input
        (quotientMap R.input (R.input.core.ind3 0 R.input.core.base)) := by
  rw [L.t1_part]
  exact partI_level_bound R.input

theorem t1_volume_bound (L : SourceTheorem311Layers B) :
    quotientVolume R.input L.t1.quotient ≤
      quotientVolume R.input
        (quotientMap R.input (R.input.core.ind3 0 R.input.core.base)) := by
  rw [L.t1_part]
  exact partI_volume_bound R.input

theorem t1_ind1_invariant (_L : SourceTheorem311Layers B)
    (g : Label) (c : Choice) :
    quotientVolume R.input
        (quotientMap R.input (R.input.core.ind1 g c)) =
      quotientVolume R.input (quotientMap R.input c) := by
  exact partI_ind1 R.input g c

theorem t1_ind2_invariant (_L : SourceTheorem311Layers B)
    (g : Label) (c : Choice) :
    quotientVolume R.input
        (quotientMap R.input (R.input.core.ind2 g c)) =
      quotientVolume R.input (quotientMap R.input c) := by
  exact partI_ind2 R.input g c

theorem t1_level_source_bound (L : SourceTheorem311Layers B) :
    quotientLevel R.input (quotientMap R.input L.t1.source) ≤
      quotientLevel R.input
        (quotientMap R.input (R.input.core.ind3 0 L.t1.source)) := by
  rw [L.t1_part]
  exact (partI R.input).level_bound

theorem t1_volume_source_bound (L : SourceTheorem311Layers B) :
    quotientVolume R.input (quotientMap R.input L.t1.source) ≤
      quotientVolume R.input
        (quotientMap R.input (R.input.core.ind3 0 L.t1.source)) := by
  rw [L.t1_part]
  exact (partI R.input).volume_bound

theorem t1_source_image_nonempty_at (L : SourceTheorem311Layers B)
    (q : IndeterminacyQuotient R.input)
    (hq : q = L.t1.quotient) :
    (quotientImage R.input q).Nonempty := by
  rw [hq]
  exact L.t1_source_image_nonempty

theorem t1_quotient_level_eq
    {q r : IndeterminacyQuotient R.input} (h : q = r) :
    quotientLevel R.input q = quotientLevel R.input r := by
  exact quotientLevel_eq_of_eq R.input h

theorem t1_quotient_volume_eq
    {q r : IndeterminacyQuotient R.input} (h : q = r) :
    quotientVolume R.input q = quotientVolume R.input r := by
  exact quotientVolume_eq_of_eq R.input h

theorem t1_quotient_image_eq
    {q r : IndeterminacyQuotient R.input} (h : q = r) :
    quotientImage R.input q = quotientImage R.input r := by
  exact quotientImage_eq_of_eq R.input h

/-! ## T2: labelled vertical log-Kummer correspondence -/

theorem t2_vertical (L : SourceTheorem311Layers B) :
    L.t2.vertical = verticalCorrespondence R.input := by
  rw [L.t2_part]
  exact partII_vertical R.input

theorem t2_siteData (L : SourceTheorem311Layers B) :
    L.t2.siteData = R.input.verticalSite := by
  rw [L.t2_part]
  exact partII_siteData R.input

theorem t2_labelled_inverse (_L : SourceTheorem311Layers B)
    (a : Choice) :
    (verticalCorrespondence R.input).kummer 0 a =
      R.input.profile.logVolume a := by
  exact partII_kummer R.input a

theorem t2_nonarchimedean_direction (_L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c) ∧ z ≤ w := by
  exact partII_nonarchimedean R.input m c z hz

theorem t2_archimedean_direction (_L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c)) :
    ∃ w, w ∈ R.input.profile.possibleImage c ∧ z ≤ w := by
  exact partII_archimedean R.input m c z hz

theorem t2_nonarchimedean_inclusion (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    z ∈ L.t2.siteData.nonarchimedeanImage m
      (R.input.profile.possibleImage c) := by
  rw [L.t2_siteData]
  exact partII_nonarchimedean_inclusion R.input m c z hz

theorem t2_archimedean_surjection (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ L.t2.siteData.archimedeanImage m
      (R.input.profile.possibleImage c)) :
    ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y := by
  rw [L.t2_siteData] at hz
  exact partII_archimedean_surjection R.input m c z hz

theorem t2_nonarchimedean_profile (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) :
    L.t2.siteData.nonarchimedeanImage m
        (R.input.profile.possibleImage c) =
      R.input.profile.possibleImage (R.input.core.ind3 m c) := by
  rw [L.t2_siteData]
  exact partII_nonarchimedean_profile R.input m c

theorem t2_archimedean_profile (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) :
    L.t2.siteData.archimedeanImage m
        (R.input.profile.possibleImage c) =
      R.input.profile.possibleImage (R.input.core.ind3 m c) := by
  rw [L.t2_siteData]
  exact partII_archimedean_profile R.input m c

theorem t2_archimedean_target (_L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c)) :
    ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y := by
  exact partII_archimedean_target R.input m c z hz

theorem t2_labelled_kummer_bijective (_L : SourceTheorem311Layers B)
    (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map := by
  exact partII_labelled_kummer R.input c

theorem t2_vertical_upper_semi (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c) ∧ z ≤ w :=
  L.t2_nonarchimedean_direction m c z hz

theorem t2_vertical_target_lift (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c)) :
    ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y :=
  L.t2_archimedean_direction m c z hz

/-! ## T3: Theta-times-mu horizontal compatibility -/

theorem t3_timesMu (L : SourceTheorem311Layers B) :
    L.t3.timesMuLink = R.input.horizontal := by
  rw [L.t3_part]
  exact partIII_timesMu_is_input R.input

theorem t3_environment (L : SourceTheorem311Layers B) :
    L.t3.environmentLink = R.input.horizontal := by
  rw [L.t3_part]
  exact partIII_environment_is_input R.input

theorem t3_timesMu_square (L : SourceTheorem311Layers B) (c : Choice) :
    L.t3.timesMuLink.upper (L.t3.timesMuLink.left c) =
      L.t3.timesMuLink.right (L.t3.timesMuLink.lower c) := by
  rw [L.t3_part]
  exact partIII_timesMu_square R.input c

theorem t3_environment_square (L : SourceTheorem311Layers B) (c : Choice) :
    L.t3.environmentLink.upper (L.t3.environmentLink.left c) =
      L.t3.environmentLink.right (L.t3.environmentLink.lower c) := by
  rw [L.t3_part]
  exact partIII_environment_square R.input c

theorem t3_permutation_stable (_L : SourceTheorem311Layers B) (c : Choice) :
    R.input.family.link (R.input.family.permutation c)
        (R.input.family.permutation c) c =
      R.input.family.link c c c := by
  exact partIII_permutation_stable R.input c

theorem t3_kappa_compatible (_L : SourceTheorem311Layers B) (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) := by
  exact partIII_kappa_compatible R.input c

theorem t3_labelled_compatible (_L : SourceTheorem311Layers B) (c : Choice) :
    (R.input.labelledKummer c).label (R.input.horizontal.left c) =
      (R.input.labelledKummer c).label (R.input.horizontal.lower c) := by
  exact partIII_labelled_compatible R.input c

theorem t3_square_both (L : SourceTheorem311Layers B) (c : Choice) :
    L.t3.timesMuLink.upper (L.t3.timesMuLink.left c) =
        L.t3.timesMuLink.right (L.t3.timesMuLink.lower c) ∧
      L.t3.environmentLink.upper (L.t3.environmentLink.left c) =
        L.t3.environmentLink.right (L.t3.environmentLink.lower c) :=
  ⟨L.t3_timesMu_square c, L.t3_environment_square c⟩

theorem t3_kummer_evaluation_both (L : SourceTheorem311Layers B)
    (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
        R.input.horizontal.right
          (R.input.evaluation.localMap (R.input.horizontal.lower c)) ∧
      (R.input.labelledKummer c).label (R.input.horizontal.left c) =
        (R.input.labelledKummer c).label (R.input.horizontal.lower c) :=
  ⟨L.t3_kappa_compatible c, L.t3_labelled_compatible c⟩

/-! ## Final output and all typed arrows -/

theorem output_part_i (L : SourceTheorem311Layers B) :
    L.output.part_i = L.t1 := by
  rw [L.output_eq, L.t1_eq]

theorem output_part_ii (L : SourceTheorem311Layers B) :
    L.output.part_ii = L.t2 := by
  rw [L.output_eq, L.t2_eq]

theorem output_part_iii (L : SourceTheorem311Layers B) :
    L.output.part_iii = L.t3 := by
  rw [L.output_eq, L.t3_eq]

theorem output_source (L : SourceTheorem311Layers B) :
    L.output.source = R.input.core.base := by
  rw [L.output_eq]
  exact B.dependency.output_source

theorem output_quotient (L : SourceTheorem311Layers B) :
    L.output.quotient = quotientMap R.input L.output.source := by
  rw [L.output_eq]
  exact B.dependency.output_quotient

theorem output_labelled (_L : SourceTheorem311Layers B) (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map := by
  exact B.dependency.output_labelled c

theorem output_ind3 (_L : SourceTheorem311Layers B)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 n c) ∧ z ≤ w := by
  exact B.dependency.output_ind3 n c z hz

theorem output_horizontal (_L : SourceTheorem311Layers B) (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) := by
  exact B.dependency.output_horizontal c

theorem output_evaluation (_L : SourceTheorem311Layers B) (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) := by
  exact B.dependency.output_evaluation c

theorem output_parts (L : SourceTheorem311Layers B) :
    L.output.part_i = partI R.input ∧
      L.output.part_ii = partII R.input ∧
      L.output.part_iii = partIII R.input := by
  rw [L.output_eq]
  exact B.dependency.output_parts

theorem arrow_h1_h2 (_L : SourceTheorem311Layers B) :
    W.h2.h1 = W.h1 :=
  B.arrow_h1_to_h2

theorem arrow_h2_realization (_L : SourceTheorem311Layers B) :
    HEq R.procession.hodge.source I.initial :=
  B.arrow_h2_to_realization_source

theorem arrow_realization_k1 (_L : SourceTheorem311Layers B) :
    W.k1 = k1OfRealization R :=
  B.arrow_realization_to_k1

theorem arrow_k1_k2 (_L : SourceTheorem311Layers B) :
    W.k2.upperSemi = W.k1.vertical :=
  B.arrow_k1_to_k2

theorem arrow_k2_t2 (_L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage
      (R.procession.ind3 m c) ∧ z ≤ y :=
  B.arrow_k2_to_prop35 m c z hz

theorem arrow_p1_p2_dependency (_L : SourceTheorem311Layers B) :
    B.dependency.proposition310 = W.k2.comparison := by
  exact B.dependency_proposition310

theorem arrow_dependency_output (L : SourceTheorem311Layers B) :
    L.output = R.output := by
  rw [L.output_eq]
  rfl

theorem arrow_dependency_parts (L : SourceTheorem311Layers B) :
    L.t1 = partI R.input ∧
      L.t2 = partII R.input ∧
      L.t3 = partIII R.input :=
  ⟨L.t1_part, L.t2_part, L.t3_part⟩

theorem arrow_t1_t2_t3 (L : SourceTheorem311Layers B) :
    L.output.part_i = L.t1 ∧
      L.output.part_ii = L.t2 ∧
      L.output.part_iii = L.t3 := by
  exact ⟨L.output_part_i, L.output_part_ii, L.output_part_iii⟩

theorem arrow_t1_source (L : SourceTheorem311Layers B) :
    L.output.part_i.source = R.input.core.base := by
  rw [L.output_part_i]
  exact L.t1_source

theorem arrow_t2_nonarchimedean (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c) ∧ z ≤ w :=
  L.t2_nonarchimedean_direction m c z hz

theorem arrow_t2_archimedean (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c)) :
    ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y :=
  L.t2_archimedean_direction m c z hz

theorem arrow_t3_evaluation (L : SourceTheorem311Layers B) (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  L.t3_kappa_compatible c

theorem arrow_t3_labelled (L : SourceTheorem311Layers B) (c : Choice) :
    (R.input.labelledKummer c).label (R.input.horizontal.left c) =
      (R.input.labelledKummer c).label (R.input.horizontal.lower c) :=
  L.t3_labelled_compatible c

theorem arrow_t1_t2_t3_output (L : SourceTheorem311Layers B) :
    L.output = B.dependency.output ∧
      L.output.part_i = L.t1 ∧
      L.output.part_ii = L.t2 ∧
      L.output.part_iii = L.t3 :=
  ⟨L.output_eq, L.output_part_i, L.output_part_ii, L.output_part_iii⟩

/-! ## P1/P2 field arrows consumed by T1/T2/T3 -/

theorem p1_theorem15 (_L : SourceTheorem311Layers B) :
    B.theorem15 = SourceP2.theorem15 R :=
  B.theorem15_eq

theorem p1_proposition32 (_L : SourceTheorem311Layers B) :
    B.proposition32 = SourceP1.proposition32 R :=
  B.proposition32_eq

theorem p1_proposition34 (_L : SourceTheorem311Layers B) :
    B.proposition34 = SourceP1.proposition34 S.lgp :=
  B.proposition34_eq

theorem p1_proposition35 (_L : SourceTheorem311Layers B) :
    B.proposition35 = SourceP1.proposition35 R :=
  B.proposition35_eq

theorem p1_proposition39 (_L : SourceTheorem311Layers B) :
    B.proposition39 = SourceP1.proposition39 R S.volume :=
  B.proposition39_eq

theorem p2_proposition21 (_L : SourceTheorem311Layers B) :
    B.proposition21 = SourceP2.proposition21 S.kummer :=
  B.proposition21_eq

theorem p2_proposition23 (_L : SourceTheorem311Layers B) :
    B.proposition23 = SourceP2.corollary23 S.permutation :=
  B.proposition23_eq

theorem p2_local_frobenioid (_L : SourceTheorem311Layers B) :
    B.proposition37Local = W.k2.localFrobenioid :=
  B.proposition37Local_eq

theorem p2_global_frobenioid (_L : SourceTheorem311Layers B) :
    B.proposition37Global = W.k2.globalFrobenioid :=
  B.proposition37Global_eq

theorem p2_proposition310 (_L : SourceTheorem311Layers B) :
    B.proposition310 = W.k2.comparison :=
  B.proposition310_eq

theorem dependency_theorem15 (_L : SourceTheorem311Layers B) :
    B.dependency.theorem15 = SourceP2.theorem15 R :=
  B.dependency_theorem15_eq

theorem dependency_proposition21 (_L : SourceTheorem311Layers B) :
    B.dependency.proposition21 = SourceP2.proposition21 S.kummer :=
  B.dependency_proposition21_eq

theorem dependency_proposition23 (_L : SourceTheorem311Layers B) :
    B.dependency.proposition23 = SourceP2.corollary23 S.permutation :=
  B.dependency_proposition23_eq

theorem dependency_proposition32 (_L : SourceTheorem311Layers B) :
    B.dependency.proposition32 = SourceP1.proposition32 R :=
  B.dependency_proposition32_eq

theorem dependency_vertical35 (_L : SourceTheorem311Layers B) :
    B.dependency.vertical35 = SourceP1.proposition35 R :=
  B.dependency_vertical35_eq

theorem dependency_proposition39 (_L : SourceTheorem311Layers B) :
    B.dependency.proposition39 = SourceP1.proposition39 R S.volume :=
  B.dependency_proposition39_eq

theorem dependency_proposition310 (_L : SourceTheorem311Layers B) :
    B.dependency.proposition310 = W.k2.comparison :=
  B.dependency_proposition310_eq

theorem dependency_source_alignment (_L : SourceTheorem311Layers B) :
    B.dependency.theorem15.vertical 0 R.procession.base =
      R.procession.base :=
  B.dependency_source_alignment

theorem dependency_packet_alignment (_L : SourceTheorem311Layers B) :
    B.dependency.proposition32.profile R.procession.base =
      R.packet.logVolume R.procession.base :=
  B.dependency_packet_alignment

theorem dependency_volume_alignment (_L : SourceTheorem311Layers B) :
    B.dependency.proposition39.logVolume R.procession.base =
      R.packet.logVolume R.procession.base :=
  B.dependency_volume_alignment

theorem dependency_horizontal_alignment (_L : SourceTheorem311Layers B) :
    B.dependency.proposition310.localMap R.procession.base =
      B.dependency.proposition310.globalMap R.procession.base :=
  B.dependency_horizontal_alignment

theorem t1_packet_alignment (L : SourceTheorem311Layers B) :
    B.proposition32.profile R.procession.base =
      R.packet.logVolume R.procession.base := by
  rw [L.p1_proposition32]
  exact SourceP1.proposition32_profile (R := R) R.procession.base

theorem t3_horizontal_alignment (L : SourceTheorem311Layers B) :
    B.proposition310.localMap R.procession.base =
      B.proposition310.globalMap R.procession.base := by
  rw [L.p2_proposition310]
  exact W.k2.comparison.localEqGlobal R.procession.base

theorem t1_t2_alignment (L : SourceTheorem311Layers B) :
    B.dependency.theorem15.vertical 0 R.procession.base =
      R.procession.base ∧
      B.dependency.proposition32.profile R.procession.base =
        R.packet.logVolume R.procession.base :=
  ⟨L.dependency_source_alignment, L.dependency_packet_alignment⟩

theorem t2_t3_alignment (L : SourceTheorem311Layers B) :
    B.dependency.proposition39.logVolume R.procession.base =
        R.packet.logVolume R.procession.base ∧
      B.dependency.proposition310.localMap R.procession.base =
        B.dependency.proposition310.globalMap R.procession.base :=
  ⟨L.dependency_volume_alignment, L.dependency_horizontal_alignment⟩

/-! ## Explicit arrow ledger -/

structure SourceTheorem311ArrowLedger
    (L : SourceTheorem311Layers B) where
  h1_to_h2 : W.h2.h1 = W.h1
  h2_to_realization : HEq R.procession.hodge.source I.initial
  realization_to_k1 : W.k1 = k1OfRealization R
  k1_to_k2 : W.k2.upperSemi = W.k1.vertical
  k2_to_p1 : B.proposition35 = SourceP1.proposition35 R
  p1_to_t1 : L.t1 = partI R.input
  p2_to_t2 : L.t2 = partII R.input
  p2_to_t3 : L.t3 = partIII R.input
  t1_to_output : L.output.part_i = L.t1
  t2_to_output : L.output.part_ii = L.t2
  t3_to_output : L.output.part_iii = L.t3
  output_source : L.output.source = R.input.core.base
  output_quotient : L.output.quotient =
    quotientMap R.input L.output.source
  output_labelled : ∀ c, Function.Bijective
    (R.input.labelledKummer c).map
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
        (R.input.evaluation.localMap (R.input.horizontal.lower c))

namespace SourceTheorem311ArrowLedger

variable {L : SourceTheorem311Layers B}

theorem assemble (L : SourceTheorem311Layers B) :
    SourceTheorem311ArrowLedger L where
  h1_to_h2 := L.arrow_h1_h2
  h2_to_realization := L.arrow_h2_realization
  realization_to_k1 := L.arrow_realization_k1
  k1_to_k2 := L.arrow_k1_k2
  k2_to_p1 := B.proposition35_eq
  p1_to_t1 := L.t1_part
  p2_to_t2 := L.t2_part
  p2_to_t3 := L.t3_part
  t1_to_output := L.output_part_i
  t2_to_output := L.output_part_ii
  t3_to_output := L.output_part_iii
  output_source := L.output_source
  output_quotient := L.output_quotient
  output_labelled := L.output_labelled
  output_ind3 := L.output_ind3
  output_horizontal := L.output_horizontal
  output_evaluation := L.output_evaluation

theorem h1_to_h2_recovered (A : SourceTheorem311ArrowLedger L) :
    W.h2.h1 = W.h1 :=
  A.h1_to_h2

theorem h2_to_realization_recovered
    (A : SourceTheorem311ArrowLedger L) :
    HEq R.procession.hodge.source I.initial :=
  A.h2_to_realization

theorem realization_to_k1_recovered
    (A : SourceTheorem311ArrowLedger L) :
    W.k1 = k1OfRealization R :=
  A.realization_to_k1

theorem k1_to_k2_recovered (A : SourceTheorem311ArrowLedger L) :
    W.k2.upperSemi = W.k1.vertical :=
  A.k1_to_k2

theorem k2_to_p1_recovered (A : SourceTheorem311ArrowLedger L) :
    B.proposition35 = SourceP1.proposition35 R :=
  A.k2_to_p1

theorem p1_to_t1_recovered (A : SourceTheorem311ArrowLedger L) :
    L.t1 = partI R.input :=
  A.p1_to_t1

theorem p2_to_t2_recovered (A : SourceTheorem311ArrowLedger L) :
    L.t2 = partII R.input :=
  A.p2_to_t2

theorem p2_to_t3_recovered (A : SourceTheorem311ArrowLedger L) :
    L.t3 = partIII R.input :=
  A.p2_to_t3

theorem t1_to_output_recovered (A : SourceTheorem311ArrowLedger L) :
    L.output.part_i = L.t1 :=
  A.t1_to_output

theorem t2_to_output_recovered (A : SourceTheorem311ArrowLedger L) :
    L.output.part_ii = L.t2 :=
  A.t2_to_output

theorem t3_to_output_recovered (A : SourceTheorem311ArrowLedger L) :
    L.output.part_iii = L.t3 :=
  A.t3_to_output

theorem output_source_recovered (A : SourceTheorem311ArrowLedger L) :
    L.output.source = R.input.core.base :=
  A.output_source

theorem output_quotient_recovered (A : SourceTheorem311ArrowLedger L) :
    L.output.quotient = quotientMap R.input L.output.source :=
  A.output_quotient

theorem output_labelled_recovered
    (A : SourceTheorem311ArrowLedger L) (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map :=
  A.output_labelled c

theorem output_ind3_recovered
    (A : SourceTheorem311ArrowLedger L)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 n c) ∧ z ≤ w :=
  A.output_ind3 n c z hz

theorem output_horizontal_recovered
    (A : SourceTheorem311ArrowLedger L) (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) :=
  A.output_horizontal c

theorem output_evaluation_recovered
    (A : SourceTheorem311ArrowLedger L) (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  A.output_evaluation c

theorem ledger_chain (A : SourceTheorem311ArrowLedger L) :
    W.h2.h1 = W.h1 ∧
      HEq R.procession.hodge.source I.initial ∧
      W.k1 = k1OfRealization R ∧
      W.k2.upperSemi = W.k1.vertical ∧
      L.t1 = partI R.input ∧
      L.t2 = partII R.input ∧
      L.t3 = partIII R.input ∧
      L.output.part_i = L.t1 ∧
      L.output.part_ii = L.t2 ∧
      L.output.part_iii = L.t3 := by
  exact ⟨A.h1_to_h2, A.h2_to_realization, A.realization_to_k1,
    A.k1_to_k2, A.p1_to_t1, A.p2_to_t2, A.p2_to_t3,
    A.t1_to_output, A.t2_to_output, A.t3_to_output⟩

end SourceTheorem311ArrowLedger

theorem canonical_layers_recover_t1
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonical A P K S).t1 = partI R.input := by
  exact (canonical A P K S).t1_part

theorem canonical_layers_recover_t2
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonical A P K S).t2 = partII R.input := by
  exact (canonical A P K S).t2_part

theorem canonical_layers_recover_t3
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonical A P K S).t3 = partIII R.input := by
  exact (canonical A P K S).t3_part

theorem canonical_layers_arrow_chain
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    let L := canonical A P K S
    L.t1 = partI R.input ∧
      L.t2 = partII R.input ∧
      L.t3 = partIII R.input := by
  dsimp
  exact ⟨canonical_layers_recover_t1 A P K S,
    canonical_layers_recover_t2 A P K S,
    canonical_layers_recover_t3 A P K S⟩

/-! ## Ind1/Ind2 descent and Ind3 output arrows -/

theorem t1_ind1_descent (_L : SourceTheorem311Layers B)
    {a b : Choice} (h : Ind1Relation R.input a b) :
    quotientMap R.input a = quotientMap R.input b :=
  quotientMap_respects_ind1 R.input h

theorem t1_ind2_descent (_L : SourceTheorem311Layers B)
    {a b : Choice} (h : Ind2Relation R.input a b) :
    quotientMap R.input a = quotientMap R.input b :=
  quotientMap_respects_ind2 R.input h

theorem t1_ind1_level (_L : SourceTheorem311Layers B)
    {a b : Choice} (h : Ind1Relation R.input a b) :
    R.input.core.level a = R.input.core.level b :=
  ind1_level_respects R.input h

theorem t1_ind2_level (_L : SourceTheorem311Layers B)
    {a b : Choice} (h : Ind2Relation R.input a b) :
    R.input.core.level a = R.input.core.level b :=
  ind2_level_respects R.input h

theorem t1_ind1_volume (L : SourceTheorem311Layers B)
    (g : Label) (c : Choice) :
    quotientVolume R.input
        (quotientMap R.input (R.input.core.ind1 g c)) =
      quotientVolume R.input (quotientMap R.input c) :=
  L.t1_ind1_invariant g c

theorem t1_ind2_volume (L : SourceTheorem311Layers B)
    (g : Label) (c : Choice) :
    quotientVolume R.input
        (quotientMap R.input (R.input.core.ind2 g c)) =
      quotientVolume R.input (quotientMap R.input c) :=
  L.t1_ind2_invariant g c

theorem t1_ind3_upper (L : SourceTheorem311Layers B)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 n c) ∧ z ≤ w :=
  L.output_ind3 n c z hz

theorem output_ind1_descent (L : SourceTheorem311Layers B)
    {a b : Choice} (h : Ind1Relation R.input a b) :
    quotientMap R.input a = quotientMap R.input b :=
  L.t1_ind1_descent h

theorem output_ind2_descent (L : SourceTheorem311Layers B)
    {a b : Choice} (h : Ind2Relation R.input a b) :
    quotientMap R.input a = quotientMap R.input b :=
  L.t1_ind2_descent h

theorem output_source_map (L : SourceTheorem311Layers B) :
    L.output.quotient = quotientMap R.input L.output.source :=
  L.output_quotient

theorem output_source_eq_base (L : SourceTheorem311Layers B) :
    L.output.source = R.input.core.base :=
  L.output_source

theorem output_part_i_source_eq_base (L : SourceTheorem311Layers B) :
    L.output.part_i.source = R.input.core.base :=
  L.arrow_t1_source

theorem output_part_i_quotient_eq_base (L : SourceTheorem311Layers B) :
    L.output.part_i.quotient = quotientMap R.input R.input.core.base := by
  rw [L.output_part_i, L.t1_part]
  exact partI_quotient R.input

theorem output_part_i_source_map (L : SourceTheorem311Layers B) :
    L.output.part_i.quotient =
      quotientMap R.input L.output.part_i.source := by
  rw [L.output_part_i, L.t1_part]
  exact partI_source_map R.input

theorem output_part_i_nonempty (L : SourceTheorem311Layers B) :
    (quotientImage R.input L.output.part_i.quotient).Nonempty := by
  rw [L.output_part_i, L.t1_part]
  exact partI_nonempty R.input

theorem output_part_i_level_bound (L : SourceTheorem311Layers B) :
    quotientLevel R.input L.output.part_i.quotient ≤
      quotientLevel R.input
        (quotientMap R.input (R.input.core.ind3 0 R.input.core.base)) := by
  rw [L.output_part_i, L.t1_part]
  exact partI_level_bound R.input

theorem output_part_i_volume_bound (L : SourceTheorem311Layers B) :
    quotientVolume R.input L.output.part_i.quotient ≤
      quotientVolume R.input
        (quotientMap R.input (R.input.core.ind3 0 R.input.core.base)) := by
  rw [L.output_part_i, L.t1_part]
  exact partI_volume_bound R.input

theorem output_part_ii_vertical_eq (L : SourceTheorem311Layers B) :
    L.output.part_ii.vertical = verticalCorrespondence R.input := by
  rw [L.output_part_ii, L.t2_part]
  exact partII_vertical R.input

theorem output_part_ii_site_eq (L : SourceTheorem311Layers B) :
    L.output.part_ii.siteData = R.input.verticalSite := by
  rw [L.output_part_ii, L.t2_part]
  exact partII_siteData R.input

theorem output_part_ii_nonarchimedean (_L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c) ∧ z ≤ w := by
  exact partII_nonarchimedean R.input m c z hz

theorem output_part_ii_archimedean (_L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c)) :
    ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y := by
  exact partII_archimedean R.input m c z hz

theorem output_part_ii_kummer_bijective (L : SourceTheorem311Layers B)
    (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map :=
  L.output_labelled c

theorem output_part_iii_timesMu_eq (L : SourceTheorem311Layers B) :
    L.output.part_iii.timesMuLink = R.input.horizontal := by
  rw [L.output_part_iii, L.t3_part]
  exact partIII_timesMu_is_input R.input

theorem output_part_iii_environment_eq (L : SourceTheorem311Layers B) :
    L.output.part_iii.environmentLink = R.input.horizontal := by
  rw [L.output_part_iii, L.t3_part]
  exact partIII_environment_is_input R.input

theorem output_part_iii_permutation (_L : SourceTheorem311Layers B)
    (c : Choice) :
    R.input.family.link (R.input.family.permutation c)
        (R.input.family.permutation c) c =
      R.input.family.link c c c := by
  exact partIII_permutation_stable R.input c

theorem output_part_iii_evaluation (L : SourceTheorem311Layers B)
    (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  L.output_evaluation c

theorem output_part_iii_label (L : SourceTheorem311Layers B)
    (c : Choice) :
    (R.input.labelledKummer c).label (R.input.horizontal.left c) =
      (R.input.labelledKummer c).label (R.input.horizontal.lower c) :=
  L.t3_labelled_compatible c

/-! ## Reusable projection package for downstream layers -/

structure SourceTheorem311Projection
    (L : SourceTheorem311Layers B) where
  source : Choice
  source_eq : source = R.input.core.base
  quotient : IndeterminacyQuotient R.input
  quotient_eq : quotient = quotientMap R.input source
  t1 : PartI R.input
  t2 : PartII R.input
  t3 : PartIII R.input
  t1_eq : t1 = L.t1
  t2_eq : t2 = L.t2
  t3_eq : t3 = L.t3
  labelled : ∀ c, Function.Bijective (R.input.labelledKummer c).map
  ind3 : ∀ n c z,
    z ∈ R.input.profile.possibleImage c →
      ∃ w, w ∈ R.input.profile.possibleImage
        (R.input.core.ind3 n c) ∧ z ≤ w
  horizontal : ∀ c,
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c)
  evaluation : ∀ c,
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c))

namespace SourceTheorem311Projection

variable {L : SourceTheorem311Layers B}

def assemble (L : SourceTheorem311Layers B) :
    SourceTheorem311Projection L where
  source := L.output.source
  source_eq := L.output_source
  quotient := L.output.quotient
  quotient_eq := L.output_quotient
  t1 := L.t1
  t2 := L.t2
  t3 := L.t3
  t1_eq := rfl
  t2_eq := rfl
  t3_eq := rfl
  labelled := L.output_labelled
  ind3 := L.output_ind3
  horizontal := L.output_horizontal
  evaluation := L.output_evaluation

theorem source_recovered (Q : SourceTheorem311Projection L) :
    Q.source = R.input.core.base :=
  Q.source_eq

theorem quotient_recovered (Q : SourceTheorem311Projection L) :
    Q.quotient = quotientMap R.input Q.source :=
  Q.quotient_eq

theorem t1_recovered (Q : SourceTheorem311Projection L) :
    Q.t1 = L.t1 :=
  Q.t1_eq

theorem t2_recovered (Q : SourceTheorem311Projection L) :
    Q.t2 = L.t2 :=
  Q.t2_eq

theorem t3_recovered (Q : SourceTheorem311Projection L) :
    Q.t3 = L.t3 :=
  Q.t3_eq

theorem labelled_recovered (Q : SourceTheorem311Projection L) (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map :=
  Q.labelled c

theorem ind3_recovered (Q : SourceTheorem311Projection L)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 n c) ∧ z ≤ w :=
  Q.ind3 n c z hz

theorem horizontal_recovered
    (Q : SourceTheorem311Projection L) (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) :=
  Q.horizontal c

theorem evaluation_recovered
    (Q : SourceTheorem311Projection L) (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  Q.evaluation c

theorem recover_all (Q : SourceTheorem311Projection L) :
    Q.source = R.input.core.base ∧
      Q.quotient = quotientMap R.input Q.source ∧
      Q.t1 = L.t1 ∧ Q.t2 = L.t2 ∧ Q.t3 = L.t3 := by
  exact ⟨Q.source_eq, Q.quotient_eq, Q.t1_eq, Q.t2_eq, Q.t3_eq⟩

end SourceTheorem311Projection

/-! ## Canonical projection and downstream-facing recovery -/

def canonicalProjection
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    SourceTheorem311Projection (canonical A P K S) :=
  SourceTheorem311Projection.assemble (canonical A P K S)

theorem canonical_projection_source
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonicalProjection A P K S).source = R.input.core.base :=
  (canonicalProjection A P K S).source_eq

theorem canonical_projection_quotient
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonicalProjection A P K S).quotient =
      quotientMap R.input (canonicalProjection A P K S).source :=
  (canonicalProjection A P K S).quotient_eq

theorem canonical_projection_t1
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonicalProjection A P K S).t1 =
      (canonical A P K S).t1 :=
  (canonicalProjection A P K S).t1_eq

theorem canonical_projection_t2
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonicalProjection A P K S).t2 =
      (canonical A P K S).t2 :=
  (canonicalProjection A P K S).t2_eq

theorem canonical_projection_t3
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonicalProjection A P K S).t3 =
      (canonical A P K S).t3 :=
  (canonicalProjection A P K S).t3_eq

theorem canonical_projection_labelled
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K))
    (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map :=
  (canonicalProjection A P K S).labelled c

theorem canonical_projection_ind3
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K))
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 n c) ∧ z ≤ w :=
  (canonicalProjection A P K S).ind3 n c z hz

theorem canonical_projection_horizontal
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K))
    (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) :=
  (canonicalProjection A P K S).horizontal c

theorem canonical_projection_evaluation
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K))
    (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  (canonicalProjection A P K S).evaluation c

theorem canonical_arrow_ledger
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    SourceTheorem311ArrowLedger
      (canonical A P K S) :=
  SourceTheorem311ArrowLedger.assemble (canonical A P K S)

theorem canonical_arrow_ledger_chain
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (SourceInternalWiring.canonical
      (I := I) (R := R) (X := X) (Y := Y) A P K).h2.h1 =
        (SourceInternalWiring.canonical
          (I := I) (R := R) (X := X) (Y := Y) A P K).h1 ∧
      HEq R.procession.hodge.source I.initial ∧
      (SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K).k1 =
          k1OfRealization R ∧
      (SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K).k2.upperSemi =
          (SourceInternalWiring.canonical
            (I := I) (R := R) (X := X) (Y := Y) A P K).k1.vertical := by
  have h := SourceTheorem311ArrowLedger.ledger_chain
    (canonical_arrow_ledger A P K S)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem output_t1_t2_t3_recovery (L : SourceTheorem311Layers B) :
    L.output.part_i = partI R.input ∧
      L.output.part_ii = partII R.input ∧
      L.output.part_iii = partIII R.input :=
  L.output_parts

theorem output_ind1_ind2_ind3_recovery
    (L : SourceTheorem311Layers B)
    {a b : Choice} (h₁ : Ind1Relation R.input a b)
    {c : Choice} (h₂ : Ind2Relation R.input a c)
    (n : Nat) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage a) :
    quotientMap R.input a = quotientMap R.input b ∧
      quotientMap R.input a = quotientMap R.input c ∧
      ∃ w, w ∈ R.input.profile.possibleImage
        (R.input.core.ind3 n a) ∧ z ≤ w := by
  exact ⟨L.t1_ind1_descent h₁, L.t1_ind2_descent h₂,
    L.t1_ind3_upper n a z hz⟩

theorem output_horizontal_evaluation_recovery
    (L : SourceTheorem311Layers B) (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
        R.input.horizontal.right (R.input.horizontal.lower c) ∧
      R.input.evaluation.localMap (R.input.horizontal.left c) =
        R.input.horizontal.right
          (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  ⟨L.output_horizontal c, L.output_evaluation c⟩

theorem output_vertical_directions_recovery
    (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    (∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c) ∧ z ≤ w) ∧
      Function.Bijective (R.input.labelledKummer c).map :=
  ⟨L.output_ind3 m c z hz, L.output_labelled c⟩

/-! ## A single downstream package with no hidden arrows -/

structure SourceTheorem311Completion
    (B : SourceP1P2Bundle W S) where
  layers : SourceTheorem311Layers B
  ledger : SourceTheorem311ArrowLedger layers
  projection : SourceTheorem311Projection layers

namespace SourceTheorem311Completion

def assemble (B : SourceP1P2Bundle W S) :
    SourceTheorem311Completion B where
  layers := SourceTheorem311Layers.assemble B
  ledger := SourceTheorem311ArrowLedger.assemble
    (SourceTheorem311Layers.assemble B)
  projection := SourceTheorem311Projection.assemble
    (SourceTheorem311Layers.assemble B)

theorem t1 (C : SourceTheorem311Completion B) :
    C.layers.t1 = partI R.input :=
  C.layers.t1_part

theorem t2 (C : SourceTheorem311Completion B) :
    C.layers.t2 = partII R.input :=
  C.layers.t2_part

theorem t3 (C : SourceTheorem311Completion B) :
    C.layers.t3 = partIII R.input :=
  C.layers.t3_part

theorem output (C : SourceTheorem311Completion B) :
    C.layers.output = B.dependency.output :=
  C.layers.output_eq

theorem source (C : SourceTheorem311Completion B) :
    C.layers.output.source = R.input.core.base :=
  C.layers.output_source

theorem quotient (C : SourceTheorem311Completion B) :
    C.layers.output.quotient =
      quotientMap R.input C.layers.output.source :=
  C.layers.output_quotient

theorem labelled (C : SourceTheorem311Completion B) (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map :=
  C.layers.output_labelled c

theorem ind3 (C : SourceTheorem311Completion B)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 n c) ∧ z ≤ w :=
  C.layers.output_ind3 n c z hz

theorem horizontal (C : SourceTheorem311Completion B) (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) :=
  C.layers.output_horizontal c

theorem evaluation (C : SourceTheorem311Completion B) (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  C.layers.output_evaluation c

theorem arrow_chain (C : SourceTheorem311Completion B) :
    W.h2.h1 = W.h1 ∧
      HEq R.procession.hodge.source I.initial ∧
      W.k1 = k1OfRealization R ∧
      W.k2.upperSemi = W.k1.vertical ∧
      C.layers.t1 = partI R.input ∧
      C.layers.t2 = partII R.input ∧
      C.layers.t3 = partIII R.input ∧
      C.layers.output.part_i = C.layers.t1 ∧
      C.layers.output.part_ii = C.layers.t2 ∧
      C.layers.output.part_iii = C.layers.t3 := by
  exact SourceTheorem311ArrowLedger.ledger_chain C.ledger

theorem projection_chain (C : SourceTheorem311Completion B) :
    C.projection.source = R.input.core.base ∧
      C.projection.quotient = quotientMap R.input C.projection.source ∧
      C.projection.t1 = C.layers.t1 ∧
      C.projection.t2 = C.layers.t2 ∧
      C.projection.t3 = C.layers.t3 := by
  exact SourceTheorem311Projection.recover_all C.projection

theorem theorem311_parts (C : SourceTheorem311Completion B) :
    C.layers.output.part_i = partI R.input ∧
      C.layers.output.part_ii = partII R.input ∧
      C.layers.output.part_iii = partIII R.input :=
  C.layers.output_parts

theorem theorem311_part_i_source (C : SourceTheorem311Completion B) :
    C.layers.output.part_i.source = R.input.core.base :=
  C.layers.output_part_i_source_eq_base

theorem theorem311_part_i_volume (C : SourceTheorem311Completion B) :
    quotientVolume R.input C.layers.output.part_i.quotient ≤
      quotientVolume R.input
        (quotientMap R.input (R.input.core.ind3 0 R.input.core.base)) :=
  C.layers.output_part_i_volume_bound

theorem theorem311_part_ii_nonarchimedean
    (C : SourceTheorem311Completion B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c) ∧ z ≤ w :=
  C.layers.output_part_ii_nonarchimedean m c z hz

theorem theorem311_part_ii_archimedean
    (C : SourceTheorem311Completion B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c)) :
    ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y :=
  C.layers.output_part_ii_archimedean m c z hz

theorem theorem311_part_iii_square
    (C : SourceTheorem311Completion B) (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
        R.input.horizontal.right (R.input.horizontal.lower c) ∧
      R.input.evaluation.localMap (R.input.horizontal.left c) =
        R.input.horizontal.right
          (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  C.layers.output_horizontal_evaluation_recovery c

end SourceTheorem311Completion

def canonicalCompletion
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    SourceTheorem311Completion
      (SourceP1P2Bundle.canonical A P K S) :=
  SourceTheorem311Completion.assemble
    (SourceP1P2Bundle.canonical A P K S)

theorem canonical_completion_chain
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonicalCompletion A P K S).layers.t1 = partI R.input ∧
      (canonicalCompletion A P K S).layers.t2 = partII R.input ∧
      (canonicalCompletion A P K S).layers.t3 = partIII R.input := by
  exact ⟨(canonicalCompletion A P K S).t1,
    (canonicalCompletion A P K S).t2,
    (canonicalCompletion A P K S).t3⟩

theorem canonical_completion_output
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input
      (W := SourceInternalWiring.canonical
        (I := I) (R := R) (X := X) (Y := Y) A P K)) :
    (canonicalCompletion A P K S).layers.output =
      (SourceP1P2Bundle.canonical A P K S).dependency.output :=
  (canonicalCompletion A P K S).output

theorem final_t1_t2_t3_arrow_package
    (L : SourceTheorem311Layers B) :
    L.t1 = partI R.input ∧
      L.t2 = partII R.input ∧
      L.t3 = partIII R.input ∧
      L.output.part_i = L.t1 ∧
      L.output.part_ii = L.t2 ∧
      L.output.part_iii = L.t3 ∧
      L.output.source = R.input.core.base := by
  exact ⟨L.t1_part, L.t2_part, L.t3_part,
    L.output_part_i, L.output_part_ii, L.output_part_iii,
    L.output_source⟩

theorem final_t2_t3_direction_package
    (L : SourceTheorem311Layers B)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    (∃ w, w ∈ R.input.profile.possibleImage
      (R.input.core.ind3 m c) ∧ z ≤ w) ∧
      R.input.horizontal.upper (R.input.horizontal.left c) =
        R.input.horizontal.right (R.input.horizontal.lower c) :=
  ⟨L.t2_nonarchimedean_direction m c z hz, L.output_horizontal c⟩

theorem final_output_evaluation_package
    (L : SourceTheorem311Layers B) (c : Choice) :
    L.output.source = R.input.core.base ∧
      Function.Bijective (R.input.labelledKummer c).map ∧
      R.input.evaluation.localMap (R.input.horizontal.left c) =
        R.input.horizontal.right
          (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  ⟨L.output_source, L.output_labelled c, L.output_evaluation c⟩

theorem final_output_source_quotient_package
    (L : SourceTheorem311Layers B) :
    L.output.quotient = quotientMap R.input L.output.source :=
  L.output_quotient

theorem source_theorem311_layers_status : True := by
  trivial

end SourceTheorem311Layers

end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311ConditionalAssembly : Obligation :=
  { id := "IUT-III.theorem-3.11-conditional-T1-T3-assembly"
    source :=
      "IUT III Theorem 3.11(i)--(iii), after Props. 3.2, 3.4, 3.5, " ++
        "3.7, 3.9, 3.10 and Theorem 1.5/Prop. 2.1/Cor. 2.3"
    status := VerificationStatus.interface
    note :=
      "SourceTheorem311Layers separates T1, T2, and T3 and proves their " ++
        "field recovery and arrows from SourceP1P2Bundle. The bundle remains " ++
        "an explicit source-facing prerequisite; this declaration does not " ++
        "construct the cited IUT objects from arithmetic data."
    dependsOn :=
      [ "IUT-III.theorem-3.11-internal-wiring",
        "IUT-III.theorem-3.11-explicit-prerequisite-boundary" ] }

end LeanFormal.IUT.Audit
