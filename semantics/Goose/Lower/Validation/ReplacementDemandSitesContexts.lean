import Goose.Lower.Validation.ReplacementDemandSitesLocation
import Goose.Core.Sound.Context

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

private theorem primary_phase (node : DemandNode) : DemandNodeHasPhase node node.primaryPhase := by
  cases node <;> simp [DemandNodeHasPhase, DemandNode.primaryPhase, DemandNode.phaseMatches]

private theorem context_descend {module : Core.Module} {plans : Array (Array DemandPoint)}
    {pc : PlanContext module plans} {parent node : DemandNode} {suffix : List Nat}
    (source : DemandNodeAt parent suffix node) :
    ∀ front, NodeContext pc front parent parent.primaryPhase →
      Nonempty (NodeContext pc (front ++ suffix) node node.primaryPhase) := by
  induction source with
  | here parent => intro front context; simpa using (Nonempty.intro context)
  | @child parent middle node index suffix row source ih =>
    intro front context
    let child := context.child rfl index middle middle.primaryPhase row (primary_phase middle)
    have selected := ih (front ++ [index]) child.context
    simpa [List.append_assoc] using selected

noncomputable def ReplacementDemandLocation.context {module : Core.Module}
    {plans : Array (Array DemandPoint)} {root node : DemandNode}
    (location : ReplacementDemandLocation root node) (pc : PlanContext module plans)
    (rootAt : demandRoot? module pc.owner = some root) :
    NodeContext pc location.path node node.primaryPhase :=
  Classical.choice (by simpa using context_descend location.source [] (NodeContext.atRoot pc root rootAt))

structure ReplacementDemandContext (module : Core.Module) (owner : Nat) (path : List Nat)
    (place : Place) (rhs : Expr) (origin : OriginId) where
  plans : Array (Array DemandPoint)
  planContext : PlanContext module plans
  owner_eq : planContext.owner = owner
  shrink : module.profile = .shrink
  statement : NodeContext planContext path (.statement (.assignWhole place rhs origin)) .statement

noncomputable def ReplacementDemandContext.statementContext {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin) :
    EvaluationContext module context.plans path (.statement (.assignWhole place rhs origin)) .statement :=
  .shrink context.shrink context.statement

noncomputable def ReplacementDemandContext.rhsTransition {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin) :
    NodeChildContext context.statement 1 (.expression rhs) .expression :=
  context.statement.child rfl 1 (.expression rhs) .expression
    (by simp [DemandNode.child?, DemandNode.children]) (primary_phase (.expression rhs))

noncomputable def ReplacementDemandContext.rhsContext {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin) :
    EvaluationContext module context.plans (path ++ [1]) (.expression rhs) .expression :=
  .shrink context.shrink context.rhsTransition.context

theorem ReplacementDemandContext.rhs_owner_forbidden {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin)
    {target : DemandOwner} (lookup : context.planContext.approvals.access.owner place = .ok target) :
    target ∈ context.rhsContext.forbiddenOwners :=
  context.rhsTransition.assignWholeOwner place rhs origin rfl rfl target lookup

#print axioms ReplacementDemandLocation.context
#print axioms ReplacementDemandContext.rhs_owner_forbidden

end Goose.Lower.Validation
