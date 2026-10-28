import Goose.Proofs.ExitExecutionActivationOuter
import Goose.Proofs.ExitExecutionOuterCallCatch

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem nested_call_returnFrom_catches (fuel : Nat) (config : EvalConfig)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (callerScope bodyScope blockScope targetId : Nat) (operands : List Expr)
    (callOrigin stmtOrigin outerOrigin returnOrigin ifOrigin : Goose.Core.OriginId)
    (callerRest bodyRest blockRest : List Stmt) (callerTail bodyTail blockTail : Option Expr)
    (context : Goose.Core.ContextId) (arguments : List Arg)
    (initial bound prepared entered bodyBound blockBound before : ExecutionState)
    (outerImpl innerImpl calledImpl : Impl) (calledId : Goose.Core.ImplId)
    (channels : List Channel) (carriers : List Carrier)
    (outerLookup : config.module.impls[outer.implementation]? = some outerImpl)
    (outerBinding : bindAll outer.act initial.nextScope outerPre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == outer.act then
        { current with scopes := (callerScope, initial.nextScope) :: outer.scopes } else current) } = .ok () bound)
    (called : getImplementation config context bound = .ok (calledId, calledImpl) bound)
    (channelSetup : channelsFor config.layout outer.act calledImpl.results.toList callOrigin bound = .ok channels prepared)
    (callPrefix : CallActivationPrefix (fuel + 7) config
      { outer with scopes := (callerScope, initial.nextScope) :: outer.scopes }
      context arguments channels callOrigin prepared inner innerPre
      (.mk bodyScope (.ifS (.bool true)
        (.mk blockScope (.returnFrom targetId operands returnOrigin :: blockRest) blockTail) none ifOrigin :: bodyRest) bodyTail) entered)
    (innerLookup : config.module.impls[inner.implementation]? = some innerImpl)
    (bodyBinding : bindAll inner.act entered.nextScope innerPre { entered with
      nextScope := entered.nextScope + 1
      activations := entered.activations.map (fun current => if current.act == inner.act then
        { current with scopes := (bodyScope, entered.nextScope) :: inner.scopes } else current) } = .ok () bodyBound)
    (blockBinding : bindAll inner.act bodyBound.nextScope []
      { bodyBound with nextScope := bodyBound.nextScope + 1 } = .ok () blockBound)
    (selected : targetActivation config targetId blockBound = .ok outer blockBound)
    (outerStack : ∃ prior between suffix,
      blockBound.activations = prior ++ inner :: between ++ outer :: suffix)
    (distinct : outer.act ≠ inner.act)
    (completed : withExitChannels
      { inner with scopes := (blockScope, bodyBound.nextScope) :: (bodyScope, entered.nextScope) :: inner.scopes }
      outer operands returnOrigin
      (fun channels => evalOperands fuel config
        { inner with scopes := (blockScope, bodyBound.nextScope) :: (bodyScope, entered.nextScope) :: inner.scopes } channels operands)
      blockBound = .ok carriers before)
    (landed : let innerEnv := { inner with scopes := (bodyScope, entered.nextScope) :: inner.scopes }
      let unwound := releaseScopeState inner bodyScope entered.nextScope
        (releaseScopeState innerEnv blockScope bodyBound.nextScope before)
      LandedResultChannels { unwound with activations := unwound.activations.filter (fun current => current.act != inner.act) } outer.channels (outerImpl.results.toList.map (·.ty)) carriers) :
    let innerEnv := { inner with scopes := (bodyScope, entered.nextScope) :: inner.scopes }
    let unwound := releaseScopeState inner bodyScope entered.nextScope
      (releaseScopeState innerEnv blockScope bodyBound.nextScope before)
    let afterInner := { unwound with activations := unwound.activations.filter (fun current => current.act != inner.act) }
    let afterOuter := releaseScopeState outer callerScope initial.nextScope afterInner
    enterActivation (fuel + 13) config outer outerPre
      (.mk callerScope (.expr (.call context arguments callOrigin) stmtOrigin :: callerRest) callerTail) outerOrigin initial =
      .ok carriers { afterOuter with activations := afterOuter.activations.filter (fun current => current.act != outer.act) } := by
  let innerEnv := { inner with scopes := (bodyScope, entered.nextScope) :: inner.scopes }
  let unwound := releaseScopeState inner bodyScope entered.nextScope
    (releaseScopeState innerEnv blockScope bodyBound.nextScope before)
  let afterInner := { unwound with activations := unwound.activations.filter (fun current => current.act != inner.act) }
  have innerEscape := activation_if_block_returnFrom_propagates fuel config inner outer innerPre
    bodyScope blockScope targetId operands returnOrigin ifOrigin callOrigin bodyRest blockRest bodyTail blockTail
    entered bodyBound blockBound before carriers innerImpl innerLookup bodyBinding blockBinding selected outerStack distinct completed
  exact activation_call_escape_catches fuel config outer inner outerPre innerPre callerScope context arguments
    callOrigin stmtOrigin outerOrigin callerRest callerTail _ initial bound prepared entered afterInner
    outerImpl calledImpl calledId channels targetId carriers outerLookup outerBinding called channelSetup callPrefix
    innerEscape distinct landed

theorem nested_call_unwind_preserves_outside (outer inner : RuntimeActivation)
    (callerScope bodyScope blockScope : Nat) (callerInst bodyInst blockInst : Goose.Core.ScopeInst)
    (before : ExecutionState) (entry : Goose.Core.RootInst × Value)
    (callerOutside : (Goose.Proofs.Exit.runtimeScopeRoots outer callerScope callerInst).contains entry.1 = false)
    (bodyOutside : (Goose.Proofs.Exit.runtimeScopeRoots inner bodyScope bodyInst).contains entry.1 = false)
    (blockOutside : (Goose.Proofs.Exit.runtimeScopeRoots
      { inner with scopes := (bodyScope, bodyInst) :: inner.scopes } blockScope blockInst).contains entry.1 = false) :
    let innerEnv := { inner with scopes := (bodyScope, bodyInst) :: inner.scopes }
    let unwound := releaseScopeState inner bodyScope bodyInst (releaseScopeState innerEnv blockScope blockInst before)
    let afterInner := { unwound with activations := unwound.activations.filter (fun current => current.act != inner.act) }
    let afterOuter := releaseScopeState outer callerScope callerInst afterInner
    let final := { afterOuter with activations := afterOuter.activations.filter (fun current => current.act != outer.act) }
    final.construction = before.construction ∧ (entry ∈ final.objects ↔ entry ∈ before.objects) := by
  refine ⟨rfl, ?_⟩
  rw [Goose.Proofs.Exit.runtime_release_scope_outside outer callerScope callerInst _ entry callerOutside]
  exact (activation_block_unwind_preserves_outside inner bodyScope blockScope bodyInst blockInst before entry
    bodyOutside blockOutside).2

#print axioms nested_call_unwind_preserves_outside
#print axioms nested_call_returnFrom_catches

end Goose.Proofs.ExitExecution
