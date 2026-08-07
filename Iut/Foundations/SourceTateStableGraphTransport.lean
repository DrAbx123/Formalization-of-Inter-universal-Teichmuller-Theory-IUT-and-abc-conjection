import Iut.Foundations.SourceTateStableGraph

namespace Iut

/-!
Transport facts for the concrete inclusion of the one-node dual graph into
the compact graph with one additional marked open edge.  The proofs are kept
at the concrete carrier level so that no generic covering axiom is smuggled
into the source boundary.
-/

theorem inclusion_map_branch_abuts
    (branch : SourceTateStableBranch) :
    sourceTateStableCompactSemiGraph.BranchAbuts
      (sourceTateStableGraphInclusion.branchEquiv .node branch)
      (sourceTateStableGraphInclusion.vertexMap .component) := by
  exact sourceTateStableGraphInclusion.map_branch_abuts rfl

theorem inclusion_isProper :
    sourceTateStableGraphInclusion.IsProper := by
  intro edge branch
  cases edge
  cases branch <;> rfl

theorem inclusion_incidentBranchMap_injective :
    Function.Injective
      (sourceTateStableGraphInclusion.incidentBranchMap .component) := by
  intro first second equality
  rcases first with ⟨⟨edgeFirst, branchFirst⟩, firstAbuts⟩
  rcases second with ⟨⟨edgeSecond, branchSecond⟩, secondAbuts⟩
  cases edgeFirst
  cases edgeSecond
  cases branchFirst <;> cases branchSecond <;> cases equality <;> rfl

theorem inclusion_isImmersion :
    sourceTateStableGraphInclusion.IsImmersion := by
  intro vertex
  cases vertex
  exact inclusion_incidentBranchMap_injective

theorem inclusion_not_isExcision :
    ¬sourceTateStableGraphInclusion.IsExcision := by
  intro excision
  have surjective := (excision .component).2
  let target : sourceTateStableCompactSemiGraph.IncidentBranch .component :=
    ⟨⟨.marked, .first⟩, rfl⟩
  obtain ⟨source, equality⟩ := surjective target
  rcases source with ⟨⟨edge, branch⟩, sourceAbuts⟩
  have edgeEquality := congrArg
    (fun incident => incident.1.1) equality
  cases edge
  cases branch
  · change SourceTateStableCompactEdge.node = .marked at edgeEquality
    cases edgeEquality
  · change SourceTateStableCompactEdge.node = .marked at edgeEquality
    cases edgeEquality

theorem inclusion_isGraphCovering_false :
    ¬sourceTateStableGraphInclusion.IsGraphCovering := by
  intro covering
  exact inclusion_not_isExcision covering.2

theorem inclusion_vertexMap_surjective :
    Function.Surjective sourceTateStableGraphInclusion.vertexMap := by
  intro vertex
  cases vertex
  exact ⟨.component, rfl⟩

theorem inclusion_edgeMap_injective :
    Function.Injective sourceTateStableGraphInclusion.edgeMap := by
  intro first second equality
  cases first
  cases second
  rfl

theorem inclusion_edgeMap_not_surjective :
    ¬Function.Surjective sourceTateStableGraphInclusion.edgeMap := by
  intro surjective
  obtain ⟨edge, equality⟩ := surjective .marked
  cases edge
  cases equality

theorem inclusion_node_isClosed :
    sourceTateStableCompactSemiGraph.IsClosed
      (sourceTateStableGraphInclusion.edgeMap .node) := by
  exact SourceTateStableCompactSemiGraph.node_isClosed

theorem inclusion_node_branch_count_preserved :
    Fintype.card (sourceTateStableDualGraph.Branch .node) =
      Fintype.card
        (sourceTateStableCompactSemiGraph.Branch
          (sourceTateStableGraphInclusion.edgeMap .node)) := by
  decide

structure InclusionAudit where
  proper : sourceTateStableGraphInclusion.{0}.IsProper
  immersion : sourceTateStableGraphInclusion.{0}.IsImmersion
  notExcision : ¬sourceTateStableGraphInclusion.{0}.IsExcision
  vertexSurjective : Function.Surjective
    sourceTateStableGraphInclusion.{0}.vertexMap
  edgeInjective : Function.Injective
    sourceTateStableGraphInclusion.{0}.edgeMap
  edgeNotSurjective : ¬Function.Surjective
    sourceTateStableGraphInclusion.{0}.edgeMap

set_option linter.defProp false in
def inclusionAudit : InclusionAudit where
  proper := inclusion_isProper
  immersion := inclusion_isImmersion
  notExcision := inclusion_not_isExcision
  vertexSurjective := inclusion_vertexMap_surjective
  edgeInjective := inclusion_edgeMap_injective
  edgeNotSurjective := inclusion_edgeMap_not_surjective

theorem inclusionAudit_proper : sourceTateStableGraphInclusion.IsProper :=
  inclusion_isProper
theorem inclusionAudit_immersion : sourceTateStableGraphInclusion.IsImmersion :=
  inclusion_isImmersion
theorem inclusionAudit_notExcision : ¬sourceTateStableGraphInclusion.IsExcision :=
  inclusion_not_isExcision

theorem inclusionAudit_vertexSurjective :
    Function.Surjective sourceTateStableGraphInclusion.{0}.vertexMap :=
  inclusion_vertexMap_surjective

theorem inclusionAudit_edgeInjective :
    Function.Injective sourceTateStableGraphInclusion.{0}.edgeMap :=
  inclusion_edgeMap_injective

theorem inclusionAudit_edgeNotSurjective :
    ¬Function.Surjective sourceTateStableGraphInclusion.{0}.edgeMap :=
  inclusion_edgeMap_not_surjective

theorem compact_marked_first_isVerticial :
    SourceTateStableBranch.first ∈
      sourceTateStableCompactSemiGraph.verticialPortion .marked := by
  exact ⟨.component, rfl⟩

theorem compact_marked_second_notVerticial :
    SourceTateStableBranch.second ∉
      sourceTateStableCompactSemiGraph.verticialPortion .marked := by
  intro h
  obtain ⟨vertex, equality⟩ := h
  cases equality

theorem compact_node_verticialPortion_eq_univ :
    sourceTateStableCompactSemiGraph.verticialPortion .node = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro branch
  exact ⟨.component, rfl⟩

theorem compact_graph_has_one_closed_edge :
    ∃ edge : SourceTateStableCompactEdge,
      sourceTateStableCompactSemiGraph.IsClosed edge :=
  ⟨.node, SourceTateStableCompactSemiGraph.node_isClosed⟩

theorem compact_graph_has_one_open_edge :
    ∃ edge : SourceTateStableCompactEdge,
      sourceTateStableCompactSemiGraph.IsOpen edge :=
  ⟨.marked, SourceTateStableCompactSemiGraph.marked_isOpen⟩

theorem inclusion_certificate_dual_connected :
    sourceTateStableDualGraph.IsConnected :=
  sourceTateStableGraphCertificate_dual_connected

theorem inclusion_certificate_dual_finite :
    sourceTateStableDualGraph.IsFinite :=
  sourceTateStableGraphCertificate_dual_finite

theorem inclusion_certificate_compact_connected :
    sourceTateStableCompactSemiGraph.IsConnected :=
  sourceTateStableGraphCertificate_compact_connected

theorem inclusion_certificate_node_closed :
    sourceTateStableCompactSemiGraph.IsClosed .node :=
  sourceTateStableGraphCertificate_node_closed

theorem inclusion_certificate_marked_open :
    sourceTateStableCompactSemiGraph.IsOpen .marked :=
  sourceTateStableGraphCertificate_marked_open

end Iut
