import Iut.Foundations.SourceSemiGraph

namespace Iut

universe u

inductive SourceTateStableComponent : Type u where
  | component
  deriving DecidableEq

instance : Fintype SourceTateStableComponent :=
  ⟨{.component}, by intro vertex; cases vertex; simp⟩

inductive SourceTateStableNode : Type u where
  | node
  deriving DecidableEq

instance : Fintype SourceTateStableNode :=
  ⟨{.node}, by intro edge; cases edge; simp⟩

inductive SourceTateStableCompactEdge : Type u where
  | node
  | marked
  deriving DecidableEq

instance : Fintype SourceTateStableCompactEdge :=
  ⟨{.node, .marked}, by intro edge; cases edge <;> simp⟩

inductive SourceTateStableBranch : Type u where
  | first
  | second
  deriving DecidableEq

instance : Fintype SourceTateStableBranch :=
  ⟨{.first, .second}, by intro branch; cases branch <;> simp⟩

def sourceTateStableDualGraph : SourceSemiGraph.{u} where
  Vertex := SourceTateStableComponent
  Edge := SourceTateStableNode
  Branch := fun _ => SourceTateStableBranch
  branchFintype := fun _ => inferInstance
  branch_card := by
    intro edge
    cases edge
    decide
  coincidence := fun _ _ => some .component

def sourceTateStableCompactSemiGraph : SourceSemiGraph.{u} where
  Vertex := SourceTateStableComponent
  Edge := SourceTateStableCompactEdge
  Branch := fun _ => SourceTateStableBranch
  branchFintype := fun _ => inferInstance
  branch_card := by
    intro edge
    cases edge <;> decide
  coincidence
    | .node, _ => some .component
    | .marked, .first => some .component
    | .marked, .second => none

namespace SourceTateStableDualGraph

theorem isConnected : sourceTateStableDualGraph.IsConnected := by
  left
  refine ⟨⟨.component⟩, ?_, ?_⟩
  · intro edge
    exact ⟨.component, .first, rfl⟩
  · intro first second
    cases first
    cases second
    exact Relation.ReflTransGen.refl

theorem isFinite : sourceTateStableDualGraph.IsFinite := by
  change Finite SourceTateStableComponent ∧ Finite SourceTateStableNode
  exact ⟨inferInstance, inferInstance⟩

theorem isCountable : sourceTateStableDualGraph.IsCountable := by
  change Countable SourceTateStableComponent ∧ Countable SourceTateStableNode
  exact ⟨inferInstance, inferInstance⟩

theorem isGraph : sourceTateStableDualGraph.IsGraph := by
  intro edge branch
  exact ⟨.component, rfl⟩

theorem node_abuts_component :
    sourceTateStableDualGraph.EdgeAbuts .node .component := by
  exact ⟨.first, rfl⟩

theorem node_joins_component :
    sourceTateStableDualGraph.Joins .node .component .component := by
  exact ⟨.first, .second, by simp, rfl, rfl⟩

theorem node_isClosed :
    sourceTateStableDualGraph.IsClosed .node :=
  isGraph .node

theorem node_verticialCardinality :
    sourceTateStableDualGraph.verticialCardinality .node = 2 := by
  exact (sourceTateStableDualGraph.isClosed_iff_verticialCardinality_eq_two
    .node).mp node_isClosed

theorem component_unique (vertex : SourceTateStableComponent) :
    vertex = .component := by
  cases vertex
  rfl

theorem node_branch_coincidence (branch : SourceTateStableBranch) :
    sourceTateStableDualGraph.coincidence .node branch = some .component :=
  rfl

theorem node_branch_abuts (branch : SourceTateStableBranch) :
    sourceTateStableDualGraph.BranchAbuts (edge := .node) branch .component :=
  rfl

theorem node_edge_card : Fintype.card SourceTateStableNode = 1 := by
  decide

theorem component_card : Fintype.card SourceTateStableComponent = 1 := by
  decide

theorem branch_card (edge : sourceTateStableDualGraph.Edge) :
    Fintype.card (sourceTateStableDualGraph.Branch edge) = 2 := by
  exact sourceTateStableDualGraph.branch_card edge

end SourceTateStableDualGraph

namespace SourceTateStableCompactSemiGraph

theorem isConnected : sourceTateStableCompactSemiGraph.IsConnected := by
  left
  refine ⟨⟨.component⟩, ?_, ?_⟩
  · intro edge
    cases edge with
    | node => exact ⟨.component, .first, rfl⟩
    | marked => exact ⟨.component, .first, rfl⟩
  · intro first second
    cases first
    cases second
    exact Relation.ReflTransGen.refl

theorem isFinite : sourceTateStableCompactSemiGraph.IsFinite := by
  change Finite SourceTateStableComponent ∧
    Finite SourceTateStableCompactEdge
  exact ⟨inferInstance, inferInstance⟩

theorem isCountable : sourceTateStableCompactSemiGraph.IsCountable := by
  change Countable SourceTateStableComponent ∧
    Countable SourceTateStableCompactEdge
  exact ⟨inferInstance, inferInstance⟩

theorem node_isClosed :
    sourceTateStableCompactSemiGraph.IsClosed .node := by
  intro branch
  exact ⟨.component, rfl⟩

theorem marked_isOpen :
    sourceTateStableCompactSemiGraph.IsOpen .marked := by
  rw [sourceTateStableCompactSemiGraph.isOpen_iff_not_isClosed]
  intro closed
  obtain ⟨vertex, hvertex⟩ := closed .second
  cases hvertex

theorem node_isNotOpen :
    ¬sourceTateStableCompactSemiGraph.IsOpen .node := by
  rw [sourceTateStableCompactSemiGraph.isOpen_iff_not_isClosed]
  exact not_not_intro node_isClosed

theorem marked_isNotClosed :
    ¬sourceTateStableCompactSemiGraph.IsClosed .marked := by
  rw [← sourceTateStableCompactSemiGraph.isOpen_iff_not_isClosed]
  exact marked_isOpen

theorem node_verticialCardinality :
    sourceTateStableCompactSemiGraph.verticialCardinality .node = 2 := by
  exact (sourceTateStableCompactSemiGraph.isClosed_iff_verticialCardinality_eq_two
    .node).mp node_isClosed

theorem marked_verticialCardinality_lt_two :
    sourceTateStableCompactSemiGraph.verticialCardinality .marked < 2 := by
  exact marked_isOpen

theorem node_abuts_component :
    sourceTateStableCompactSemiGraph.EdgeAbuts .node .component := by
  exact ⟨.first, rfl⟩

theorem marked_abuts_component :
    sourceTateStableCompactSemiGraph.EdgeAbuts .marked .component := by
  exact ⟨.first, rfl⟩

theorem marked_second_isNonVerticial :
    sourceTateStableCompactSemiGraph.coincidence .marked .second = none :=
  rfl

theorem node_branch_coincidence (branch : SourceTateStableBranch) :
    sourceTateStableCompactSemiGraph.coincidence .node branch = some .component :=
  rfl

theorem marked_first_coincidence :
    sourceTateStableCompactSemiGraph.coincidence .marked .first = some .component :=
  rfl

theorem marked_second_coincidence :
    sourceTateStableCompactSemiGraph.coincidence .marked .second = none :=
  rfl

theorem edge_card : Fintype.card SourceTateStableCompactEdge = 2 := by
  decide

theorem branch_card (edge : SourceTateStableCompactEdge) :
    Fintype.card (sourceTateStableCompactSemiGraph.Branch edge) = 2 := by
  exact sourceTateStableCompactSemiGraph.branch_card edge

theorem every_edge_is_node_or_marked (edge : SourceTateStableCompactEdge) :
    edge = .node ∨ edge = .marked := by
  cases edge <;> simp

end SourceTateStableCompactSemiGraph

def sourceTateStableGraphInclusion :
    sourceTateStableDualGraph.Hom sourceTateStableCompactSemiGraph where
  vertexMap := id
  edgeMap := fun _ => .node
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro edge branch vertex coincidence
    cases edge
    exact coincidence

@[simp] theorem sourceTateStableGraphInclusion_vertexMap
    (vertex : SourceTateStableComponent) :
    sourceTateStableGraphInclusion.vertexMap vertex = vertex :=
  rfl

@[simp] theorem sourceTateStableGraphInclusion_edgeMap
    (edge : SourceTateStableNode) :
    sourceTateStableGraphInclusion.edgeMap edge = .node :=
  rfl

@[simp] theorem sourceTateStableGraphInclusion_branchMap
    (edge : SourceTateStableNode) (branch : SourceTateStableBranch) :
    sourceTateStableGraphInclusion.branchEquiv edge branch = branch :=
  rfl

theorem sourceTateStableGraphInclusion_preserves_node :
    sourceTateStableGraphInclusion.edgeMap .node = .node :=
  rfl

theorem sourceTateStableGraphInclusion_preserves_incidence
    (branch : SourceTateStableBranch) :
    sourceTateStableCompactSemiGraph.coincidence .node branch =
      some (sourceTateStableGraphInclusion.vertexMap .component) := by
  rfl

structure SourceTateStableGraphCertificate : Type u where
  dual_connected : sourceTateStableDualGraph.{u}.IsConnected
  dual_finite : sourceTateStableDualGraph.{u}.IsFinite
  compact_connected : sourceTateStableCompactSemiGraph.{u}.IsConnected
  node_closed : sourceTateStableCompactSemiGraph.{u}.IsClosed .node
  marked_open : sourceTateStableCompactSemiGraph.{u}.IsOpen .marked
  inclusion : sourceTateStableDualGraph.{u}.Hom
    sourceTateStableCompactSemiGraph.{u}

def sourceTateStableGraphCertificate : SourceTateStableGraphCertificate where
  dual_connected := SourceTateStableDualGraph.isConnected
  dual_finite := SourceTateStableDualGraph.isFinite
  compact_connected := SourceTateStableCompactSemiGraph.isConnected
  node_closed := SourceTateStableCompactSemiGraph.node_isClosed
  marked_open := SourceTateStableCompactSemiGraph.marked_isOpen
  inclusion := sourceTateStableGraphInclusion

theorem sourceTateStableGraphCertificate_dual_connected :
    sourceTateStableDualGraph.IsConnected :=
  sourceTateStableGraphCertificate.dual_connected

theorem sourceTateStableGraphCertificate_dual_finite :
    sourceTateStableDualGraph.IsFinite :=
  sourceTateStableGraphCertificate.dual_finite

theorem sourceTateStableGraphCertificate_compact_connected :
    sourceTateStableCompactSemiGraph.IsConnected :=
  sourceTateStableGraphCertificate.compact_connected

theorem sourceTateStableGraphCertificate_node_closed :
    sourceTateStableCompactSemiGraph.IsClosed .node :=
  sourceTateStableGraphCertificate.node_closed

theorem sourceTateStableGraphCertificate_marked_open :
    sourceTateStableCompactSemiGraph.IsOpen .marked :=
  sourceTateStableGraphCertificate.marked_open

theorem sourceTateStableGraphCertificate_inclusion_vertex
    (vertex : SourceTateStableComponent) :
    sourceTateStableGraphInclusion.vertexMap vertex = vertex :=
  rfl

theorem sourceTateStableGraphCertificate_inclusion_node :
    sourceTateStableGraphInclusion.edgeMap .node = .node :=
  rfl

end Iut
