import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteIntegralHodgeTheaterExample

/-!
  Dependent finite histories of Hodge-theater carriers.

  The endpoint and composite link are constructed from the actual link
  algebra.  A reflexive example is supplied for the finite integral carrier;
  it is deliberately not presented as the source's distinct-history
  existence theorem.
-/

namespace LeanFormal.IUT

universe ua uv upi umon

noncomputable section

inductive HodgeTheaterHistory (l : PrimeGeFive) (V : Type uv) :
    HodgeTheater.{ua, uv, upi, umon} l V →
      Type (max (max (max ua uv) upi) umon + 2)
  | singleton (theater : HodgeTheater.{ua, uv, upi, umon} l V) :
      HodgeTheaterHistory l V theater
  | cons {source target : HodgeTheater.{ua, uv, upi, umon} l V}
      (link : HodgeTheaterLink source target)
      (rest : HodgeTheaterHistory l V target) :
      HodgeTheaterHistory l V source

namespace HodgeTheaterHistory

variable {l : PrimeGeFive} {V : Type uv}

def terminal {source : HodgeTheater.{ua, uv, upi, umon} l V} :
    HodgeTheaterHistory l V source → HodgeTheater.{ua, uv, upi, umon} l V
  | .singleton theater => theater
  | .cons _ rest => rest.terminal

@[simp] theorem terminal_singleton
    (theater : HodgeTheater.{ua, uv, upi, umon} l V) :
    (HodgeTheaterHistory.singleton theater).terminal = theater := rfl

@[simp] theorem terminal_cons
    {source target : HodgeTheater.{ua, uv, upi, umon} l V}
    (link : HodgeTheaterLink source target)
    (rest : HodgeTheaterHistory l V target) :
    (HodgeTheaterHistory.cons link rest).terminal = rest.terminal := rfl

def length {source : HodgeTheater.{ua, uv, upi, umon} l V} :
    HodgeTheaterHistory l V source → Nat
  | .singleton _ => 1
  | .cons _ rest => rest.length + 1

@[simp] theorem length_singleton
    (theater : HodgeTheater.{ua, uv, upi, umon} l V) :
    (HodgeTheaterHistory.singleton theater).length = 1 := rfl

@[simp] theorem length_cons
    {source target : HodgeTheater.{ua, uv, upi, umon} l V}
    (link : HodgeTheaterLink source target)
    (rest : HodgeTheaterHistory l V target) :
    (HodgeTheaterHistory.cons link rest).length = rest.length + 1 := rfl

def composite {source : HodgeTheater.{ua, uv, upi, umon} l V}
    (history : HodgeTheaterHistory l V source) :
    HodgeTheaterLink source history.terminal
  := match history with
    | .singleton theater => HodgeTheaterLink.refl theater
    | .cons link rest => HodgeTheaterLink.trans link rest.composite

@[simp] theorem composite_singleton
    (theater : HodgeTheater.{ua, uv, upi, umon} l V) :
    (HodgeTheaterHistory.singleton theater).composite =
      HodgeTheaterLink.refl theater := rfl

@[simp] theorem composite_cons
    {source target : HodgeTheater.{ua, uv, upi, umon} l V}
    (link : HodgeTheaterLink source target)
    (rest : HodgeTheaterHistory l V target) :
    (HodgeTheaterHistory.cons link rest).composite =
      HodgeTheaterLink.trans link rest.composite := rfl

theorem length_pos {source : HodgeTheater.{ua, uv, upi, umon} l V}
    (history : HodgeTheaterHistory l V source) :
    0 < history.length := by
  induction history with
  | singleton => simp [length]
  | cons link rest ih => simp [length]

theorem composite_q {source : HodgeTheater.{ua, uv, upi, umon} l V}
    (history : HodgeTheaterHistory l V source) :
    source.thetaPacket.q = history.terminal.thetaPacket.q := by
  exact history.composite.theta_q_eq

theorem composite_scale {source : HodgeTheater.{ua, uv, upi, umon} l V}
    (history : HodgeTheaterHistory l V source)
    (j : SignedLabel l.value) :
    source.thetaPacket.scale j = history.terminal.thetaPacket.scale j := by
  exact history.composite.theta_scale_eq j

end HodgeTheaterHistory

def gaussianFiniteIntegralHistory (l : PrimeGeFive) :
    HodgeTheaterHistory l (FinitePrimePlace 2 7)
      (gaussianFiniteIntegralHodgeTheater l) :=
  .cons (HodgeTheaterLink.refl (gaussianFiniteIntegralHodgeTheater l))
    (.cons (HodgeTheaterLink.refl (gaussianFiniteIntegralHodgeTheater l))
      (.singleton (gaussianFiniteIntegralHodgeTheater l)))

theorem gaussianFiniteIntegralHistory_terminal (l : PrimeGeFive) :
    (gaussianFiniteIntegralHistory l).terminal =
      gaussianFiniteIntegralHodgeTheater l := by
  rfl

theorem gaussianFiniteIntegralHistory_q (l : PrimeGeFive) :
    (gaussianFiniteIntegralHistory l).terminal.thetaPacket.q =
      (gaussianFiniteIntegralHodgeTheater l).thetaPacket.q := by
  rfl

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def hodgeTheaterHistoryAlgebra : Obligation :=
  { id := "IUT-I.hodge-theater-history-composition"
    source := "IUT I, Sections 4--5; history/link composition"
    status := VerificationStatus.proved
    note :=
      "Finite dependent histories, their terminal theater, composite link, " ++
        "positive length, and q/scale transport are constructed from the " ++
        "proved HodgeTheaterLink algebra."
    dependsOn := ["IUT-I.hodge-theater-carrier-and-links"] }

def concreteFiniteIntegralHodgeTheaterHistory : Obligation :=
  { id := "IUT-I.concrete-finite-integral-hodge-history"
    source := "IUT I, Sections 4--5 (finite carrier test history)"
    status := VerificationStatus.interface
    note :=
      "A three-step reflexive history is a concrete carrier test. It does " ++
        "not assert the paper's distinct histories, anabelian links, or " ++
        "Hodge-Arakelov existence theorem."
    dependsOn := ["IUT-I.hodge-theater-history-composition",
      "IUT-I-II.concrete-finite-integral-hodge-carrier"] }

end LeanFormal.IUT.Audit
