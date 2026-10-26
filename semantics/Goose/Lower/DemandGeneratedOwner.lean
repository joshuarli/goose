import Goose.Lower.DemandGeneratedOccurrence

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedDemandRootSelection (module : Core.Module) : Func → LEnv → DemandNode → Nat → Prop
  | context {contextId : ContextId} {context : Context} {implementation : Impl}
      (contextAt : module.contexts[contextId]? = some context)
      (implementationAt : module.impls[context.impl]? = some implementation) :
      GeneratedDemandRootSelection module (lowerContextAt module context implementation)
        (lowerEnv module implementation.vars implementation.results.toList) (.block implementation.body) contextId
  | global {globalId : GlobalId} {global : Core.Global}
      (globalAt : module.globals[globalId]? = some global) :
      GeneratedDemandRootSelection module (lowerGlobal module global).init (lowerEnv module #[] [global.ty])
        (.expression global.init) (module.contexts.size + globalId)

theorem GeneratedDemandRootSelection.source {module : Core.Module} {function : Func} {le : LEnv}
    {root : DemandNode} {owner : Nat} (selected : GeneratedDemandRootSelection module function le root owner) :
    demandRoot? module owner = some root := by
  cases selected with
  | context contextAt implementationAt =>
    have bound := (Array.getElem?_eq_some_iff.mp contextAt).1
    simp only [demandRoot?, bound, ite_true, contextAt, Option.bind_some, implementationAt, Option.map_some]
  | @global globalId global globalAt =>
    have bound : ¬ module.contexts.size + globalId < module.contexts.size := by omega
    simp only [demandRoot?, bound, ite_false, Nat.add_sub_cancel_left, globalAt, Option.map_some]

theorem GeneratedDemandOccurrence.rootSelection {module : Core.Module} {function : Func} {le : LEnv}
    {root : DemandNode} {path : List Nat} {action : DemandLoweringAction} {before : LS}
    (occurrence : GeneratedDemandOccurrence module function le root path action before) :
    ∃ owner, GeneratedDemandRootSelection module function le root owner := by
  induction occurrence
  case functionRoot contextId context implementation contextAt implementationAt =>
    exact ⟨contextId, .context contextAt implementationAt⟩
  case globalRoot globalId global globalAt =>
    exact ⟨module.contexts.size + globalId, .global globalAt⟩
  all_goals assumption

structure GeneratedSourceOwner {module : Core.Module} {function : Func} {le : LEnv} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection module function le root owner)
    {plans : Array (Array DemandPoint)} {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    (context : EvaluationContext module plans path node phase) : Prop where
  plan : context.OwnerMatches owner
  source : DemandNodeAt root path node

theorem GeneratedSourceOwner.child {module : Core.Module} {function : Func} {le : LEnv} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection module function le root owner}
    {plans : Array (Array DemandPoint)} {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    {context : EvaluationContext module plans path node phase} (matched : GeneratedSourceOwner selected context)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode) (childPhase : DemandPhase)
    (found : node.child? index = some child) (hasPhase : DemandNodeHasPhase child childPhase) :
    GeneratedSourceOwner selected (context.child primary index child childPhase found hasPhase) := by
  refine ⟨?_, matched.source.snoc index found⟩
  cases context <;> exact matched.plan

theorem GeneratedSourceOwner.transport {module : Core.Module} {function : Func} {le : LEnv} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection module function le root owner}
    {firstPlans secondPlans : Array (Array DemandPoint)} {firstPath secondPath : List Nat}
    {firstNode secondNode : DemandNode} {phase : DemandPhase}
    {first : EvaluationContext module firstPlans firstPath firstNode phase}
    {second : EvaluationContext module secondPlans secondPath secondNode phase}
    (matched : GeneratedSourceOwner selected first) (plans : firstPlans = secondPlans)
    (path : firstPath = secondPath) (node : firstNode = secondNode) (same : HEq first second) :
    GeneratedSourceOwner selected second := by
  subst secondPlans
  subst secondPath
  subst secondNode
  cases eq_of_heq same
  exact matched

theorem GeneratedSourceOwner.excludes_other_owner {module : Core.Module} {function : Func} {le : LEnv} {root : DemandNode}
    {owner otherOwner : Nat} {selected : GeneratedDemandRootSelection module function le root owner}
    {other : GeneratedDemandRootSelection module function le root otherOwner}
    {plans : Array (Array DemandPoint)} {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    {context : EvaluationContext module plans path node phase}
    (profile : module.profile = .shrink) (different : owner ≠ otherOwner)
    (matched : GeneratedSourceOwner selected context) : ¬ GeneratedSourceOwner other context := by
  intro wrong
  cases context with
  | pilot pilot active => cases profile.symm.trans pilot
  | shrink shrink context => exact different (matched.plan.symm.trans wrong.plan)

end Goose.Lower
