/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceCombinatorialUniversalCover
import Iut.Foundations.SourceFiniteSheetSemiGraphCover
import Iut.Foundations.SourceReducedWordFiniteSeparation

/-!
# Finite separation of semi-graph deck loops

The faithful incidence graph has two kinds of geometric edges for every total
branch: edge-to-branch and branch-to-compact-vertex.  Recording those two
kinds separately turns every reduced incidence walk into a reduced signed
word without discarding steps.  Prefix permutations for that word then give
the finite-sheet voltage cover used to separate a nontrivial deck loop.
-/

namespace Iut

universe u

namespace SourceSemiGraphResidualSeparation

open SourceCombinatorialUniversalCover

variable (semiGraph : SourceSemiGraph.{u})

/-- The two barycentric incidence-edge kinds belonging to a total branch. -/
inductive IncidenceEdge
  | edgeBranch (branch : semiGraph.TotalBranch)
  | branchVertex (branch : semiGraph.TotalBranch)

/-- A directed incidence step, expressed as an unoriented generator and an
orientation bit. -/
def signedStep
    {first second : IncidenceNode semiGraph}
    (adjacent : (IncidenceNode.incidenceGraph semiGraph).Adj first second) :
    IncidenceEdge semiGraph × Bool := by
  cases first with
  | vertex vertex =>
      cases second with
      | vertex other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | edge edge =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | branch branch => exact ⟨.branchVertex branch, false⟩
  | edge edge =>
      cases second with
      | vertex vertex =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | edge other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | branch branch => exact ⟨.edgeBranch branch, true⟩
  | branch branch =>
      cases second with
      | vertex vertex => exact ⟨.branchVertex branch, true⟩
      | edge edge => exact ⟨.edgeBranch branch, false⟩
      | branch other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent

/-- Reversing an incidence step retains its generator and reverses its sign. -/
theorem signedStep_reverse
    {first second : IncidenceNode semiGraph}
    (adjacent : (IncidenceNode.incidenceGraph semiGraph).Adj first second) :
    signedStep semiGraph adjacent.symm =
      ((signedStep semiGraph adjacent).1, !(signedStep semiGraph adjacent).2) := by
  cases first <;> cases second <;>
    simp [signedStep, IncidenceNode.incidenceGraph,
      IncidenceNode.incidenceRel, SimpleGraph.fromRel_adj] at adjacent ⊢

/-- The signed generator determines the directed endpoints of an incidence
edge.  Thus equal generators with opposite signs are reverse steps. -/
theorem endpoints_eq_of_generator_eq_of_sign_ne
    {first middle last : IncidenceNode semiGraph}
    (firstAdjacent :
      (IncidenceNode.incidenceGraph semiGraph).Adj first middle)
    (secondAdjacent :
      (IncidenceNode.incidenceGraph semiGraph).Adj middle last)
    (generatorEquality :
      (signedStep semiGraph firstAdjacent).1 =
        (signedStep semiGraph secondAdjacent).1)
    (signDifferent :
      (signedStep semiGraph firstAdjacent).2 ≠
        (signedStep semiGraph secondAdjacent).2) :
    first = last := by
  cases first with
  | vertex firstVertex =>
      cases middle with
      | vertex middleVertex =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | edge middleEdge =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | branch middleBranch =>
          cases last with
          | vertex lastVertex =>
              have firstCoincidence :=
                (IncidenceNode.vertex_branch_adj semiGraph
                  firstVertex middleBranch).mp firstAdjacent
              have lastCoincidence :=
                (IncidenceNode.branch_vertex_adj semiGraph
                  middleBranch lastVertex).mp secondAdjacent
              exact congrArg IncidenceNode.vertex <|
                Option.some.inj (firstCoincidence.symm.trans lastCoincidence)
          | edge lastEdge => simp [signedStep] at generatorEquality
          | branch lastBranch =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at secondAdjacent
  | edge firstEdge =>
      cases middle with
      | vertex middleVertex =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | edge middleEdge =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | branch middleBranch =>
          cases last with
          | vertex lastVertex => simp [signedStep] at generatorEquality
          | edge lastEdge =>
              have firstSupport :=
                (IncidenceNode.edge_branch_adj semiGraph
                  firstEdge middleBranch).mp firstAdjacent
              have lastSupport :=
                (IncidenceNode.branch_edge_adj semiGraph
                  middleBranch lastEdge).mp secondAdjacent
              exact congrArg IncidenceNode.edge <| firstSupport.symm.trans lastSupport
          | branch lastBranch =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at secondAdjacent
  | branch firstBranch =>
      cases middle with
      | vertex middleVertex =>
          cases last with
          | vertex lastVertex =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at secondAdjacent
          | edge lastEdge =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at secondAdjacent
          | branch lastBranch =>
              have branchEquality : firstBranch = lastBranch :=
                IncidenceEdge.branchVertex.inj generatorEquality
              cases branchEquality
              rfl
      | edge middleEdge =>
          cases last with
          | vertex lastVertex =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at secondAdjacent
          | edge lastEdge =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at secondAdjacent
          | branch lastBranch =>
              have branchEquality : firstBranch = lastBranch :=
                IncidenceEdge.edgeBranch.inj generatorEquality
              cases branchEquality
              rfl
      | branch middleBranch =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent

/-- The signed incidence word read from a based reduced walk. -/
def incidenceWord
    {root : IncidenceNode semiGraph} :
    {previous : Option (IncidenceNode semiGraph)} →
      {current : IncidenceNode semiGraph} →
      ReducedWalk (IncidenceNode.incidenceGraph semiGraph) root previous current →
        List (IncidenceEdge semiGraph × Bool)
  | _, _, .nil => []
  | _, _, .step walk adjacent _ =>
      incidenceWord walk ++ [signedStep semiGraph adjacent]

@[simp]
theorem incidenceWord_nil (root : IncidenceNode semiGraph) :
    incidenceWord semiGraph
      (ReducedWalk.nil
        (graph := IncidenceNode.incidenceGraph semiGraph) (root := root)) = [] :=
  rfl

@[simp]
theorem incidenceWord_step
    {root : IncidenceNode semiGraph}
    {previous : Option (IncidenceNode semiGraph)}
    {current next : IncidenceNode semiGraph}
    (walk : ReducedWalk
      (IncidenceNode.incidenceGraph semiGraph) root previous current)
    (adjacent : (IncidenceNode.incidenceGraph semiGraph).Adj current next)
    (notBacktrack : previous ≠ some next) :
    incidenceWord semiGraph (.step walk adjacent notBacktrack) =
      incidenceWord semiGraph walk ++ [signedStep semiGraph adjacent] :=
  rfl

/-- No cancellation is introduced when the no-backtracking incidence walk is
read as a signed word. -/
theorem incidenceWord_isReduced
    {root : IncidenceNode semiGraph}
    {previous : Option (IncidenceNode semiGraph)}
    {current : IncidenceNode semiGraph}
    (walk : ReducedWalk
      (IncidenceNode.incidenceGraph semiGraph) root previous current) :
    FreeGroup.IsReduced (incidenceWord semiGraph walk) := by
  induction walk with
  | nil => exact FreeGroup.IsReduced.nil
  | @step previous current next walk adjacent notBacktrack inductionHypothesis =>
      rw [incidenceWord_step]
      apply inductionHypothesis.append (List.isChain_singleton _)
      intro firstLetter firstMem lastLetter lastMem
      simp only [List.head?_singleton, Option.mem_def] at lastMem
      replace lastMem := Option.some.inj lastMem
      subst lastLetter
      cases walk with
      | nil => simp at firstMem
      | @step before prior current parentWalk priorAdjacent priorNotBacktrack =>
          simp only [incidenceWord_step, List.getLast?_append,
            List.getLast?_singleton, Option.some_or, Option.mem_def] at firstMem
          replace firstMem := Option.some.inj firstMem
          subst firstLetter
          intro generatorEquality
          by_contra signEquality
          have endpointEquality :=
            endpoints_eq_of_generator_eq_of_sign_ne semiGraph
              priorAdjacent adjacent generatorEquality signEquality
          apply notBacktrack
          exact congrArg some endpointEquality

/-- The signed word has exactly one letter per incidence step. -/
theorem incidenceWord_length
    {root : IncidenceNode semiGraph}
    {previous : Option (IncidenceNode semiGraph)}
    {current : IncidenceNode semiGraph}
    (walk : ReducedWalk
      (IncidenceNode.incidenceGraph semiGraph) root previous current) :
    (incidenceWord semiGraph walk).length = walk.length := by
  induction walk with
  | nil => rfl
  | step walk adjacent notBacktrack inductionHypothesis =>
      simp [incidenceWord_step, ReducedWalk.length, inductionHypothesis]

/-- A nontrivial incidence walk has a nonempty signed word. -/
theorem incidenceWord_ne_nil_of_length_ne_zero
    {root : IncidenceNode semiGraph}
    {previous : Option (IncidenceNode semiGraph)}
    {current : IncidenceNode semiGraph}
    (walk : ReducedWalk
      (IncidenceNode.incidenceGraph semiGraph) root previous current)
    (nontrivial : walk.length ≠ 0) :
    incidenceWord semiGraph walk ≠ [] := by
  intro empty
  have := incidenceWord_length semiGraph walk
  rw [empty] at this
  exact nontrivial this.symm

section SeparationCover

variable {rootNode : IncidenceNode semiGraph}
    {previous : Option (IncidenceNode semiGraph)}
    {current : IncidenceNode semiGraph}
    (walk : ReducedWalk
      (IncidenceNode.incidenceGraph semiGraph) rootNode previous current)

abbrev SeparationWord := incidenceWord semiGraph walk

abbrev SeparationState :=
  SourceReducedWordFiniteSeparation.State (SeparationWord semiGraph walk)

/-- The finite prefix-state set, lifted into the universe of the semi-graph. -/
abbrev SeparationSheet := ULift.{u} (SeparationState semiGraph walk)

/-- Conjugate a finite prefix-state permutation across the universe lift. -/
def liftPermutation
    (permutation : Equiv.Perm (SeparationState semiGraph walk)) :
    Equiv.Perm (SeparationSheet semiGraph walk) :=
  Equiv.ulift.trans (permutation.trans Equiv.ulift.symm)

/-- The prefix permutation assigned to every barycentric incidence edge. -/
noncomputable def incidencePermutation
    (generator : IncidenceEdge semiGraph) :
    Equiv.Perm (SeparationSheet semiGraph walk) :=
  liftPermutation semiGraph walk <|
    SourceReducedWordFiniteSeparation.generatorPerm
      (SeparationWord semiGraph walk)
      (incidenceWord_isReduced semiGraph walk) generator

/-- The total transport across a branch is the edge-to-branch prefix
permutation followed by the branch-to-vertex prefix permutation. -/
noncomputable def branchTransport
    (edge : semiGraph.Edge) (branch : semiGraph.Branch edge) :
    Equiv.Perm (SeparationSheet semiGraph walk) :=
  (incidencePermutation semiGraph walk (.edgeBranch ⟨edge, branch⟩)).trans
    (incidencePermutation semiGraph walk (.branchVertex ⟨edge, branch⟩))

/-- The finite-sheet semi-graph cover selected by the reduced loop. -/
noncomputable abbrev separationCover : SourceSemiGraph.{u} :=
  SourceFiniteSheetSemiGraphCover.cover semiGraph
    (SeparationSheet semiGraph walk) (branchTransport semiGraph walk)

/-- Projection of the selected finite-sheet cover. -/
noncomputable abbrev separationProjection :
    (separationCover semiGraph walk).Hom semiGraph :=
  SourceFiniteSheetSemiGraphCover.projection semiGraph
    (SeparationSheet semiGraph walk) (branchTransport semiGraph walk)

/-- The selected projection is a graph covering. -/
theorem separationProjection_isGraphCovering :
    (separationProjection semiGraph walk).IsGraphCovering :=
  SourceFiniteSheetSemiGraphCover.projection_isGraphCovering semiGraph
    (SeparationSheet semiGraph walk) (branchTransport semiGraph walk)

/-- A sheet coordinate at each kind of barycentric node.  At a branch node
the coordinate is measured after the edge-to-branch permutation; at a
compactified vertex it is measured after the complete branch transport. -/
noncomputable def liftIncidenceNode :
    IncidenceNode semiGraph → SeparationSheet semiGraph walk →
      IncidenceNode (separationCover semiGraph walk)
  | .vertex (.inl vertex), sheet =>
      .vertex (.inl (vertex, sheet))
  | .vertex (.inr branch), sheet =>
      .vertex (.inr ⟨
        ⟨(branch.1.1,
          (branchTransport semiGraph walk branch.1.1 branch.1.2).symm sheet),
          branch.1.2⟩,
        by
          have branchNone :
              semiGraph.coincidence branch.1.1 branch.1.2 = none :=
            branch.2
          change Option.map _
            (semiGraph.coincidence branch.1.1 branch.1.2) = none
          rw [branchNone]
          rfl⟩)
  | .edge edge, sheet =>
      .edge (edge, sheet)
  | .branch branch, sheet =>
      .branch ⟨
        (branch.1,
          (incidencePermutation semiGraph walk (.edgeBranch branch)).symm sheet),
        branch.2⟩

/-- Forgetting the sheet of a lifted incidence node recovers the original
node. -/
@[simp]
theorem properMap_liftIncidenceNode
    (node : IncidenceNode semiGraph)
    (sheet : SeparationSheet semiGraph walk) :
    IncidenceNode.properMap (separationCover semiGraph walk)
        (separationProjection semiGraph walk)
        (separationProjection_isGraphCovering semiGraph walk).1
        (liftIncidenceNode semiGraph walk node sheet) = node := by
  cases node with
  | vertex vertex =>
      cases vertex with
      | inl vertex => rfl
      | inr branch =>
          rw [liftIncidenceNode]
          rw [IncidenceNode.properMap_vertex_boundary]
          congr 3
  | edge edge => rfl
  | branch branch => rfl

instance separationCover_vertex_finite [Finite semiGraph.Vertex] :
    Finite (separationCover semiGraph walk).Vertex :=
  inferInstance

instance separationCover_edge_finite [Finite semiGraph.Edge] :
    Finite (separationCover semiGraph walk).Edge :=
  inferInstance

@[simp]
theorem branchTransport_apply
    (edge : semiGraph.Edge) (branch : semiGraph.Branch edge)
    (sheet : SeparationSheet semiGraph walk) :
    branchTransport semiGraph walk edge branch sheet =
      incidencePermutation semiGraph walk (.branchVertex ⟨edge, branch⟩)
        (incidencePermutation semiGraph walk (.edgeBranch ⟨edge, branch⟩)
          sheet) :=
  rfl

@[simp]
theorem branchTransport_symm_apply
    (edge : semiGraph.Edge) (branch : semiGraph.Branch edge)
    (sheet : SeparationSheet semiGraph walk) :
    (branchTransport semiGraph walk edge branch).symm sheet =
      (incidencePermutation semiGraph walk (.edgeBranch ⟨edge, branch⟩)).symm
        ((incidencePermutation semiGraph walk
          (.branchVertex ⟨edge, branch⟩)).symm sheet) :=
  rfl

/-- The signed-step permutation is definitionally the finite word evaluator. -/
noncomputable def incidenceStepPermutation
    {first second : IncidenceNode semiGraph}
    (adjacent : (IncidenceNode.incidenceGraph semiGraph).Adj first second) :
    Equiv.Perm (SeparationSheet semiGraph walk) :=
  if (signedStep semiGraph adjacent).2 then
    incidencePermutation semiGraph walk (signedStep semiGraph adjacent).1
  else
    (incidencePermutation semiGraph walk
      (signedStep semiGraph adjacent).1).symm

theorem incidenceStepPermutation_eq_lift_letterPerm
    {first second : IncidenceNode semiGraph}
    (adjacent : (IncidenceNode.incidenceGraph semiGraph).Adj first second) :
    incidenceStepPermutation semiGraph walk adjacent =
      liftPermutation semiGraph walk
        (SourceReducedWordFiniteSeparation.letterPerm
          (SeparationWord semiGraph walk)
          (incidenceWord_isReduced semiGraph walk)
          (signedStep semiGraph adjacent)) := by
  simp only [incidenceStepPermutation, incidencePermutation,
    SourceReducedWordFiniteSeparation.letterPerm]
  split <;> rfl

/-- Reversing an incidence step inverts its sheet permutation. -/
theorem incidenceStepPermutation_reverse
    {first second : IncidenceNode semiGraph}
    (adjacent : (IncidenceNode.incidenceGraph semiGraph).Adj first second) :
    incidenceStepPermutation semiGraph walk adjacent.symm =
      (incidenceStepPermutation semiGraph walk adjacent).symm := by
  cases first <;> cases second <;>
    simp [incidenceStepPermutation, signedStep,
      IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
      SimpleGraph.fromRel_adj] at adjacent ⊢

/-- The positive edge-to-branch half-step has the advertised lift. -/
theorem liftIncidenceNode_edge_branch_adj
    (branch : semiGraph.TotalBranch)
    (sheet : SeparationSheet semiGraph walk) :
    (IncidenceNode.incidenceGraph (separationCover semiGraph walk)).Adj
      (liftIncidenceNode semiGraph walk (.edge branch.1) sheet)
      (liftIncidenceNode semiGraph walk (.branch branch)
        (incidencePermutation semiGraph walk (.edgeBranch branch) sheet)) := by
  simp only [liftIncidenceNode]
  rw [IncidenceNode.edge_branch_adj]
  change
    (branch.1,
      (incidencePermutation semiGraph walk (.edgeBranch branch)).symm
        (incidencePermutation semiGraph walk (.edgeBranch branch) sheet)) =
      (branch.1, sheet)
  rw [Equiv.symm_apply_apply]

/-- The chosen compact endpoint of an open branch is its appended boundary
vertex. -/
theorem compactEndpoint_of_none
    {edge : semiGraph.Edge} {branch : semiGraph.Branch edge}
    (coincidence : semiGraph.coincidence edge branch = none) :
    SourceSemiGraphUniversalCover.compactEndpoint semiGraph edge branch =
      Sum.inr ⟨⟨edge, branch⟩, coincidence⟩ := by
  apply Option.some.inj
  rw [← SourceSemiGraphUniversalCover.compactEndpoint_spec]
  exact semiGraph.compactification_coincidence_of_none coincidence

/-- The positive branch-to-vertex half-step has the advertised lift. -/
theorem liftIncidenceNode_branch_vertex_adj
    (branch : semiGraph.TotalBranch)
    (sheet : SeparationSheet semiGraph walk) :
    (IncidenceNode.incidenceGraph (separationCover semiGraph walk)).Adj
      (liftIncidenceNode semiGraph walk (.branch branch) sheet)
      (liftIncidenceNode semiGraph walk
        (.vertex (SourceSemiGraphUniversalCover.compactEndpoint
          semiGraph branch.1 branch.2))
        (incidencePermutation semiGraph walk (.branchVertex branch) sheet)) := by
  cases coincidence : semiGraph.coincidence branch.1 branch.2 with
  | some vertex =>
      rw [SourceSemiGraphUniversalCover.compactEndpoint_of_some
        semiGraph coincidence]
      simp only [liftIncidenceNode]
      rw [IncidenceNode.branch_vertex_adj]
      apply (separationCover semiGraph walk).compactification_coincidence_of_some
      change Option.map
          (fun target => (target,
            branchTransport semiGraph walk branch.1 branch.2
              ((incidencePermutation semiGraph walk
                (.edgeBranch branch)).symm sheet)))
          (semiGraph.coincidence branch.1 branch.2) =
        some (vertex,
          incidencePermutation semiGraph walk (.branchVertex branch) sheet)
      rw [coincidence]
      simp [branchTransport]
  | none =>
      rw [compactEndpoint_of_none semiGraph coincidence]
      simp only [liftIncidenceNode]
      rw [IncidenceNode.branch_vertex_adj]
      have sheetEquality :
          (branchTransport semiGraph walk branch.1 branch.2).symm
              (incidencePermutation semiGraph walk
                (.branchVertex branch) sheet) =
            (incidencePermutation semiGraph walk
              (.edgeBranch branch)).symm sheet := by
        apply (branchTransport semiGraph walk branch.1 branch.2).injective
        simp [branchTransport]
      have coverNone :
          (separationCover semiGraph walk).coincidence
              (branch.1,
                (incidencePermutation semiGraph walk
                  (.edgeBranch branch)).symm sheet)
              branch.2 = none := by
        change Option.map _ (semiGraph.coincidence branch.1 branch.2) = none
        rw [coincidence]
        rfl
      rw [(separationCover semiGraph walk).compactification_coincidence_of_none
        coverNone]
      congr 4
      exact congrArg (fun value => (branch.1, value)) sheetEquality.symm

/-- Every base incidence step lifts to the node with the sheet coordinate
advanced by its signed prefix permutation. -/
theorem liftIncidenceNode_adj
    {first second : IncidenceNode semiGraph}
    (adjacent : (IncidenceNode.incidenceGraph semiGraph).Adj first second)
    (sheet : SeparationSheet semiGraph walk) :
    (IncidenceNode.incidenceGraph (separationCover semiGraph walk)).Adj
      (liftIncidenceNode semiGraph walk first sheet)
      (liftIncidenceNode semiGraph walk second
        (incidenceStepPermutation semiGraph walk adjacent sheet)) := by
  cases first with
  | vertex point =>
      cases second with
      | vertex other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | edge edge =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | branch branch =>
          have endpoint :=
            (IncidenceNode.vertex_branch_adj semiGraph point branch).mp adjacent
          have pointEquality : point =
              SourceSemiGraphUniversalCover.compactEndpoint
                semiGraph branch.1 branch.2 :=
            Option.some.inj <| endpoint.symm.trans
              (SourceSemiGraphUniversalCover.compactEndpoint_spec
                semiGraph branch.1 branch.2)
          subst point
          simpa only [incidenceStepPermutation, signedStep, Bool.false_eq_true,
            ↓reduceIte, Equiv.apply_symm_apply] using
              (liftIncidenceNode_branch_vertex_adj semiGraph walk branch
                ((incidencePermutation semiGraph walk
                  (.branchVertex branch)).symm sheet)).symm
  | edge edge =>
      cases second with
      | vertex point =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | edge other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | branch branch =>
          have support :=
            (IncidenceNode.edge_branch_adj semiGraph edge branch).mp adjacent
          rcases branch with ⟨branchEdge, branch⟩
          change branchEdge = edge at support
          subst edge
          simpa only [incidenceStepPermutation, signedStep, ↓reduceIte] using
            liftIncidenceNode_edge_branch_adj semiGraph walk
              (⟨branchEdge, branch⟩ : semiGraph.TotalBranch) sheet
  | branch branch =>
      cases second with
      | vertex point =>
          have endpoint :=
            (IncidenceNode.branch_vertex_adj semiGraph branch point).mp adjacent
          have pointEquality : point =
              SourceSemiGraphUniversalCover.compactEndpoint
                semiGraph branch.1 branch.2 :=
            Option.some.inj <| endpoint.symm.trans
              (SourceSemiGraphUniversalCover.compactEndpoint_spec
                semiGraph branch.1 branch.2)
          subst point
          simpa only [incidenceStepPermutation, signedStep, ↓reduceIte] using
            liftIncidenceNode_branch_vertex_adj semiGraph walk branch sheet
      | edge edge =>
          have support :=
            (IncidenceNode.branch_edge_adj semiGraph branch edge).mp adjacent
          rcases branch with ⟨branchEdge, branch⟩
          change branchEdge = edge at support
          subst edge
          simpa only [incidenceStepPermutation, signedStep, Bool.false_eq_true,
            ↓reduceIte, Equiv.apply_symm_apply] using
              (liftIncidenceNode_edge_branch_adj semiGraph walk
                (⟨branchEdge, branch⟩ : semiGraph.TotalBranch)
                ((incidencePermutation semiGraph walk
                  (.edgeBranch ⟨branchEdge, branch⟩)).symm sheet)).symm
      | branch other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent

/-- Evaluate the signed incidence word of a path on a chosen lifted sheet,
using the permutations selected by the complete separating walk. -/
noncomputable def walkSheet
    {pathRoot : IncidenceNode semiGraph}
    {pathPrevious : Option (IncidenceNode semiGraph)}
    {pathCurrent : IncidenceNode semiGraph}
    (path : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      pathRoot pathPrevious pathCurrent)
    (initial : SeparationSheet semiGraph walk) :
    SeparationSheet semiGraph walk :=
  (incidenceWord semiGraph path).foldl
    (fun sheet value =>
      liftPermutation semiGraph walk
        (SourceReducedWordFiniteSeparation.letterPerm
          (SeparationWord semiGraph walk)
          (incidenceWord_isReduced semiGraph walk) value) sheet)
    initial

@[simp]
theorem walkSheet_nil
    (pathRoot : IncidenceNode semiGraph)
    (initial : SeparationSheet semiGraph walk) :
    walkSheet semiGraph walk
      (ReducedWalk.nil
        (graph := IncidenceNode.incidenceGraph semiGraph)
        (root := pathRoot)) initial = initial :=
  rfl

@[simp]
theorem walkSheet_step
    {pathRoot : IncidenceNode semiGraph}
    {pathPrevious : Option (IncidenceNode semiGraph)}
    {pathCurrent pathNext : IncidenceNode semiGraph}
    (path : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      pathRoot pathPrevious pathCurrent)
    (adjacent :
      (IncidenceNode.incidenceGraph semiGraph).Adj pathCurrent pathNext)
    (notBacktrack : pathPrevious ≠ some pathNext)
    (initial : SeparationSheet semiGraph walk) :
    walkSheet semiGraph walk (.step path adjacent notBacktrack) initial =
      incidenceStepPermutation semiGraph walk adjacent
        (walkSheet semiGraph walk path initial) := by
  simp only [walkSheet, incidenceWord_step, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [incidenceStepPermutation_eq_lift_letterPerm]

/-- The explicit walk in the finite cover obtained by lifting each incidence
step with its current sheet coordinate. -/
noncomputable def liftWalk :
    {pathRoot : IncidenceNode semiGraph} →
    {pathPrevious : Option (IncidenceNode semiGraph)} →
    {pathCurrent : IncidenceNode semiGraph} →
    (path : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      pathRoot pathPrevious pathCurrent) →
    (initial : SeparationSheet semiGraph walk) →
    (IncidenceNode.incidenceGraph (separationCover semiGraph walk)).Walk
      (liftIncidenceNode semiGraph walk pathRoot initial)
      (liftIncidenceNode semiGraph walk pathCurrent
        (walkSheet semiGraph walk path initial))
  | _, _, _, .nil, initial => .nil
  | _, _, _, .step path adjacent notBacktrack, initial =>
      (liftWalk path initial).concat (by
        rw [walkSheet_step]
        exact liftIncidenceNode_adj semiGraph walk adjacent
          (walkSheet semiGraph walk path initial))

/-- Lift a reduced base walk to the universal incidence tree of the finite
separator, starting at a prescribed sheet. -/
noncomputable def liftUniversalVertexAux :
    {pathRoot : IncidenceNode semiGraph} →
    {pathPrevious : Option (IncidenceNode semiGraph)} →
    {pathCurrent : IncidenceNode semiGraph} →
    (path : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      pathRoot pathPrevious pathCurrent) →
    (initial : SeparationSheet semiGraph walk) →
    {point : UniversalVertex
        (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
        (liftIncidenceNode semiGraph walk pathRoot initial) //
      point.endpoint =
        liftIncidenceNode semiGraph walk pathCurrent
          (walkSheet semiGraph walk path initial)}
  | pathRoot, _, _, .nil, initial =>
      ⟨UniversalVertex.base
        (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
        (liftIncidenceNode semiGraph walk pathRoot initial), rfl⟩
  | pathRoot, _, pathNext, .step path adjacent notBacktrack, initial => by
      let lifted := liftUniversalVertexAux path initial
      let nextNode := liftIncidenceNode semiGraph walk pathNext
        (walkSheet semiGraph walk (.step path adjacent notBacktrack) initial)
      have liftedAdjacent :
          (IncidenceNode.incidenceGraph
            (separationCover semiGraph walk)).Adj lifted.1.endpoint nextNode := by
        rw [lifted.2]
        dsimp only [nextNode]
        rw [walkSheet_step]
        exact liftIncidenceNode_adj semiGraph walk adjacent
          (walkSheet semiGraph walk path initial)
      exact ⟨UniversalVertex.liftNeighbor
          (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
          (liftIncidenceNode semiGraph walk pathRoot initial)
          lifted.1 nextNode liftedAdjacent,
        UniversalVertex.liftNeighbor_endpoint _ _ _ _ _⟩

/-- The universal-tree vertex selected by the explicit separator lift. -/
noncomputable def liftUniversalVertex
    {pathRoot : IncidenceNode semiGraph}
    {pathPrevious : Option (IncidenceNode semiGraph)}
    {pathCurrent : IncidenceNode semiGraph}
    (path : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      pathRoot pathPrevious pathCurrent)
    (initial : SeparationSheet semiGraph walk) :
    UniversalVertex
      (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
      (liftIncidenceNode semiGraph walk pathRoot initial) :=
  (liftUniversalVertexAux semiGraph walk path initial).1

@[simp]
theorem liftUniversalVertex_nil
    (pathRoot : IncidenceNode semiGraph)
    (initial : SeparationSheet semiGraph walk) :
    liftUniversalVertex semiGraph walk
        (ReducedWalk.nil
          (graph := IncidenceNode.incidenceGraph semiGraph)
          (root := pathRoot)) initial =
      UniversalVertex.base
        (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
        (liftIncidenceNode semiGraph walk pathRoot initial) := by
  simp [liftUniversalVertex, liftUniversalVertexAux]

@[simp]
theorem liftUniversalVertex_endpoint
    {pathRoot : IncidenceNode semiGraph}
    {pathPrevious : Option (IncidenceNode semiGraph)}
    {pathCurrent : IncidenceNode semiGraph}
    (path : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      pathRoot pathPrevious pathCurrent)
    (initial : SeparationSheet semiGraph walk) :
    (liftUniversalVertex semiGraph walk path initial).endpoint =
      liftIncidenceNode semiGraph walk pathCurrent
        (walkSheet semiGraph walk path initial) :=
  (liftUniversalVertexAux semiGraph walk path initial).2

/-- Successive canonical lifts are adjacent in the separator's universal
tree. -/
theorem liftUniversalVertex_step_adjacent
    {pathRoot : IncidenceNode semiGraph}
    {pathPrevious : Option (IncidenceNode semiGraph)}
    {pathCurrent pathNext : IncidenceNode semiGraph}
    (path : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      pathRoot pathPrevious pathCurrent)
    (adjacent : (IncidenceNode.incidenceGraph semiGraph).Adj
      pathCurrent pathNext)
    (notBacktrack : pathPrevious ≠ some pathNext)
    (initial : SeparationSheet semiGraph walk) :
    (UniversalVertex.tree
      (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
      (liftIncidenceNode semiGraph walk pathRoot initial)).Adj
        (liftUniversalVertex semiGraph walk path initial)
        (liftUniversalVertex semiGraph walk
          (.step path adjacent notBacktrack) initial) := by
  unfold liftUniversalVertex
  simp only [liftUniversalVertexAux]
  exact UniversalVertex.adjacent_liftNeighbor _ _ _ _ _

/-- Project the separator's universal incidence tree back to the universal
tree of the original semi-graph. -/
noncomputable def separationTreeProjection
    (pathRoot : IncidenceNode semiGraph)
    (initial : SeparationSheet semiGraph walk) :
    UniversalVertex
        (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
        (liftIncidenceNode semiGraph walk pathRoot initial) →
      UniversalVertex (IncidenceNode.incidenceGraph semiGraph) pathRoot :=
  fun point => UniversalVertex.castRoot
    (IncidenceNode.incidenceGraph semiGraph)
    (properMap_liftIncidenceNode semiGraph walk pathRoot initial)
    (UniversalVertex.mapHom
      (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
      (liftIncidenceNode semiGraph walk pathRoot initial)
      (IncidenceNode.incidenceGraph semiGraph)
      (IncidenceNode.properIncidenceGraphHom
        (separationCover semiGraph walk)
        (separationProjection semiGraph walk)
        (separationProjection_isGraphCovering semiGraph walk).1)
      point)

@[simp]
theorem separationTreeProjection_endpoint
    (pathRoot : IncidenceNode semiGraph)
    (initial : SeparationSheet semiGraph walk)
    (point : UniversalVertex
      (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
      (liftIncidenceNode semiGraph walk pathRoot initial)) :
    (separationTreeProjection semiGraph walk pathRoot initial point).endpoint =
      IncidenceNode.properMap
        (separationCover semiGraph walk)
        (separationProjection semiGraph walk)
        (separationProjection_isGraphCovering semiGraph walk).1
        point.endpoint := by
  unfold separationTreeProjection
  rw [UniversalVertex.castRoot_endpoint]
  simpa only [IncidenceNode.properIncidenceGraphHom_apply] using
    UniversalVertex.mapHom_endpoint
      (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
      (liftIncidenceNode semiGraph walk pathRoot initial)
      (IncidenceNode.incidenceGraph semiGraph)
      (IncidenceNode.properIncidenceGraphHom
        (separationCover semiGraph walk)
        (separationProjection semiGraph walk)
        (separationProjection_isGraphCovering semiGraph walk).1)
      point

@[simp]
theorem separationTreeProjection_base
    (pathRoot : IncidenceNode semiGraph)
    (initial : SeparationSheet semiGraph walk) :
    separationTreeProjection semiGraph walk pathRoot initial
        (UniversalVertex.base
          (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
          (liftIncidenceNode semiGraph walk pathRoot initial)) =
      UniversalVertex.base (IncidenceNode.incidenceGraph semiGraph) pathRoot := by
  unfold separationTreeProjection
  rw [UniversalVertex.mapHom_base]
  exact UniversalVertex.castRoot_base
    (IncidenceNode.incidenceGraph semiGraph)
    (properMap_liftIncidenceNode semiGraph walk pathRoot initial)

/-- The separator universal-tree projection preserves adjacency. -/
theorem separationTreeProjection_adj
    (pathRoot : IncidenceNode semiGraph)
    (initial : SeparationSheet semiGraph walk)
    {first second : UniversalVertex
      (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
      (liftIncidenceNode semiGraph walk pathRoot initial)}
    (adjacent :
      (UniversalVertex.tree
        (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
        (liftIncidenceNode semiGraph walk pathRoot initial)).Adj first second) :
    (UniversalVertex.tree (IncidenceNode.incidenceGraph semiGraph) pathRoot).Adj
      (separationTreeProjection semiGraph walk pathRoot initial first)
      (separationTreeProjection semiGraph walk pathRoot initial second) := by
  unfold separationTreeProjection
  apply UniversalVertex.castRoot_adj
  exact UniversalVertex.mapHom_adj _ _ _ _ adjacent

/-- The finite separator projection induces an injective map of universal
incidence trees.  This is the global path-lifting uniqueness supplied by the
local covering law. -/
theorem separationTreeProjection_injective
    (pathRoot : IncidenceNode semiGraph)
    (initial : SeparationSheet semiGraph walk) :
    Function.Injective
      (separationTreeProjection semiGraph walk pathRoot initial) := by
  intro first second projectedEquality
  unfold separationTreeProjection at projectedEquality
  have mappedEquality := UniversalVertex.castRoot_injective
    (IncidenceNode.incidenceGraph semiGraph)
    (properMap_liftIncidenceNode semiGraph walk pathRoot initial)
    projectedEquality
  exact UniversalVertex.mapHom_injective_of_locallyInjective
    (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
    (liftIncidenceNode semiGraph walk pathRoot initial)
    (IncidenceNode.incidenceGraph semiGraph)
    (IncidenceNode.properIncidenceGraphHom
      (separationCover semiGraph walk)
      (separationProjection semiGraph walk)
      (separationProjection_isGraphCovering semiGraph walk).1)
    (IncidenceNode.properIncidenceGraphHom_isLocallyInjective
      (separationProjection semiGraph walk)
      (separationProjection_isGraphCovering semiGraph walk)) mappedEquality

/-- Projection of the canonical separator lift recovers the original reduced
walk vertex.  This is the path-lifting uniqueness statement used by the
tempered-to-profinite injectivity proof. -/
theorem separationTreeProjection_liftUniversalVertex
    {pathRoot : IncidenceNode semiGraph}
    {pathPrevious : Option (IncidenceNode semiGraph)}
    {pathCurrent : IncidenceNode semiGraph}
    (path : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      pathRoot pathPrevious pathCurrent)
    (initial : SeparationSheet semiGraph walk) :
    separationTreeProjection semiGraph walk pathRoot initial
        (liftUniversalVertex semiGraph walk path initial) =
      ⟨pathPrevious, pathCurrent, path⟩ := by
  induction path with
  | nil =>
      simpa only [liftUniversalVertex_nil] using
        separationTreeProjection_base semiGraph walk pathRoot initial
  | @step pathPrevious pathCurrent pathNext path adjacent notBacktrack
      inductionHypothesis =>
      let liftedParent := liftUniversalVertex semiGraph walk path initial
      let liftedChild := liftUniversalVertex semiGraph walk
        (.step path adjacent notBacktrack) initial
      let projectedParent := separationTreeProjection semiGraph walk
        pathRoot initial liftedParent
      let projectedChild := separationTreeProjection semiGraph walk
        pathRoot initial liftedChild
      let expectedParent : UniversalVertex
          (IncidenceNode.incidenceGraph semiGraph) pathRoot :=
        ⟨pathPrevious, pathCurrent, path⟩
      let expectedChild : UniversalVertex
          (IncidenceNode.incidenceGraph semiGraph) pathRoot :=
        ⟨some pathCurrent, pathNext, .step path adjacent notBacktrack⟩
      have liftedAdjacent :
          (UniversalVertex.tree
            (IncidenceNode.incidenceGraph (separationCover semiGraph walk))
            (liftIncidenceNode semiGraph walk pathRoot initial)).Adj
              liftedParent liftedChild := by
        exact liftUniversalVertex_step_adjacent semiGraph walk path
          adjacent notBacktrack initial
      have projectedAdjacent :
          (UniversalVertex.tree (IncidenceNode.incidenceGraph semiGraph)
            pathRoot).Adj projectedParent projectedChild := by
        exact separationTreeProjection_adj semiGraph walk pathRoot initial
          liftedAdjacent
      have parentEquality : projectedParent = expectedParent :=
        inductionHypothesis
      have projectedAdjacentFromExpected :
          (UniversalVertex.tree (IncidenceNode.incidenceGraph semiGraph)
            pathRoot).Adj expectedParent projectedChild := by
        rw [← parentEquality]
        exact projectedAdjacent
      have expectedAdjacent :
          (UniversalVertex.tree (IncidenceNode.incidenceGraph semiGraph)
            pathRoot).Adj expectedParent expectedChild := by
        rw [UniversalVertex.tree_adj_iff]
        constructor
        · intro equality
          have endpointEquality := congrArg
            (UniversalVertex.endpoint
              (IncidenceNode.incidenceGraph semiGraph) pathRoot) equality
          exact adjacent.ne endpointEquality
        · left
          rfl
      have endpointEquality : projectedChild.endpoint = expectedChild.endpoint := by
        change projectedChild.endpoint = pathNext
        rw [separationTreeProjection_endpoint,
          liftUniversalVertex_endpoint,
          properMap_liftIncidenceNode]
      exact UniversalVertex.neighbor_eq_of_endpoint_eq
        (IncidenceNode.incidenceGraph semiGraph) pathRoot
        projectedAdjacentFromExpected expectedAdjacent endpointEquality

/-- Fold evaluation commutes with the transparent lift of the finite state
set into the semi-graph universe. -/
theorem foldl_liftPermutation
    (values : List (IncidenceEdge semiGraph × Bool))
    (state : SeparationState semiGraph walk) :
    values.foldl
        (fun sheet value =>
          liftPermutation semiGraph walk
            (SourceReducedWordFiniteSeparation.letterPerm
              (SeparationWord semiGraph walk)
              (incidenceWord_isReduced semiGraph walk) value) sheet)
        (ULift.up state) =
      ULift.up
        (values.foldl
          (fun currentState value =>
            SourceReducedWordFiniteSeparation.letterPerm
              (SeparationWord semiGraph walk)
              (incidenceWord_isReduced semiGraph walk) value currentState)
          state) := by
  induction values generalizing state with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.foldl_cons, liftPermutation, Equiv.trans_apply,
        Equiv.ulift_apply, Equiv.ulift_symm_apply]
      exact inductionHypothesis _

/-- The initial sheet of the prefix-state separator. -/
abbrev initialSheet : SeparationSheet semiGraph walk :=
  ULift.up <| SourceReducedWordFiniteSeparation.prefixState
    (SeparationWord semiGraph walk) 0 (Nat.zero_le _)

/-- The sheet reached after evaluating the complete separating walk. -/
noncomputable abbrev finalSheet : SeparationSheet semiGraph walk :=
  ULift.up <| SourceReducedWordFiniteSeparation.run
    (SeparationWord semiGraph walk) (incidenceWord_isReduced semiGraph walk)

/-- Lifting the complete walk from its initial prefix state reaches exactly
the final prefix state. -/
theorem walkSheet_initial_eq_final :
    walkSheet semiGraph walk walk (initialSheet semiGraph walk) =
      finalSheet semiGraph walk := by
  exact foldl_liftPermutation semiGraph walk
    (SeparationWord semiGraph walk)
    (SourceReducedWordFiniteSeparation.prefixState
      (SeparationWord semiGraph walk) 0 (Nat.zero_le _))

/-- The canonical universal-tree lift of the complete separating walk ends
on the separator's final sheet. -/
theorem liftUniversalVertex_initial_endpoint_eq_final :
    (liftUniversalVertex semiGraph walk walk
      (initialSheet semiGraph walk)).endpoint =
      liftIncidenceNode semiGraph walk current
        (finalSheet semiGraph walk) := by
  rw [liftUniversalVertex_endpoint,
    walkSheet_initial_eq_final]

/-- A nontrivial reduced walk sends the initial lifted sheet to a distinct
final sheet. -/
theorem finalSheet_ne_initialSheet (nontrivial : walk.length ≠ 0) :
    finalSheet semiGraph walk ≠ initialSheet semiGraph walk := by
  intro equality
  apply SourceReducedWordFiniteSeparation.run_ne_initial
    (SeparationWord semiGraph walk) (incidenceWord_isReduced semiGraph walk)
    (incidenceWord_ne_nil_of_length_ne_zero semiGraph walk nontrivial)
  exact congrArg ULift.down equality

/-- For a nontrivial loop based at an original vertex, the canonical lifted
universal-tree endpoint is not its starting vertex. -/
theorem liftUniversalVertex_loop_endpoint_ne_base
    {root : semiGraph.Vertex}
    {loopPrevious : Option (IncidenceNode semiGraph)}
    (loop : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      (.vertex (.inl root)) loopPrevious (.vertex (.inl root)))
    (nontrivial : loop.length ≠ 0) :
    (liftUniversalVertex semiGraph loop loop
        (initialSheet semiGraph loop)).endpoint ≠
      liftIncidenceNode semiGraph loop (.vertex (.inl root))
        (initialSheet semiGraph loop) := by
  rw [liftUniversalVertex_initial_endpoint_eq_final]
  intro endpointEquality
  have pairEquality :
      (root, finalSheet semiGraph loop) =
        (root, initialSheet semiGraph loop) :=
    Sum.inl.inj (IncidenceNode.vertex.inj endpointEquality)
  exact finalSheet_ne_initialSheet semiGraph loop nontrivial
    (congrArg Prod.snd pairEquality)

/-- A nontrivial closed reduced incidence walk at an original vertex lifts
to a walk between two distinct points of the same finite vertex fiber. -/
theorem exists_liftWalk_between_distinct_fiber_points
    {root : semiGraph.Vertex}
    {loopPrevious : Option (IncidenceNode semiGraph)}
    (loop : ReducedWalk (IncidenceNode.incidenceGraph semiGraph)
      (.vertex (.inl root)) loopPrevious (.vertex (.inl root)))
    (nontrivial : loop.length ≠ 0) :
    ∃ _lifted :
        (IncidenceNode.incidenceGraph (separationCover semiGraph loop)).Walk
          (.vertex (.inl (root, initialSheet semiGraph loop)))
          (.vertex (.inl (root, finalSheet semiGraph loop))),
      (root, finalSheet semiGraph loop) ≠
        (root, initialSheet semiGraph loop) := by
  refine ⟨?_, ?_⟩
  · rw [← walkSheet_initial_eq_final semiGraph loop]
    exact liftWalk semiGraph loop loop (initialSheet semiGraph loop)
  · intro equality
    exact finalSheet_ne_initialSheet semiGraph loop nontrivial
      (congrArg Prod.snd equality)

/-- The complete loop evaluator is the final prefix state. -/
theorem separationRun_eq_finalState :
    SourceReducedWordFiniteSeparation.run
        (SeparationWord semiGraph walk)
        (incidenceWord_isReduced semiGraph walk) =
      SourceReducedWordFiniteSeparation.prefixState
        (SeparationWord semiGraph walk)
        (SeparationWord semiGraph walk).length (le_refl _) :=
  SourceReducedWordFiniteSeparation.run_eq_finalState
    (SeparationWord semiGraph walk) (incidenceWord_isReduced semiGraph walk)

/-- A nontrivial reduced walk moves the initial sheet of its selected finite
cover. -/
theorem separationRun_ne_initial (nontrivial : walk.length ≠ 0) :
    SourceReducedWordFiniteSeparation.run
        (SeparationWord semiGraph walk)
        (incidenceWord_isReduced semiGraph walk) ≠
      SourceReducedWordFiniteSeparation.prefixState
        (SeparationWord semiGraph walk) 0 (Nat.zero_le _) :=
  SourceReducedWordFiniteSeparation.run_ne_initial
    (SeparationWord semiGraph walk) (incidenceWord_isReduced semiGraph walk)
    (incidenceWord_ne_nil_of_length_ne_zero semiGraph walk nontrivial)

end SeparationCover

end SourceSemiGraphResidualSeparation

end Iut
