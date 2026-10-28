import Goose.Proofs.ExitExecutionPathDispatchUnwind
import Goose.Proofs.ExitExecutionLandedChannels

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem activation_call_escape_catches (fuel : Nat) (config : EvalConfig)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (scope : Nat) (context : Goose.Core.ContextId) (arguments : List Arg)
    (callOrigin stmtOrigin outerOrigin : Goose.Core.OriginId) (rest : List Stmt) (tail : Option Expr)
    (innerBody : Block) (initial bound prepared entered before : ExecutionState)
    (outerImpl calledImpl : Impl) (calledId : Goose.Core.ImplId) (channels : List Channel)
    (targetId : Nat) (carriers : List Carrier)
    (lookup : config.module.impls[outer.implementation]? = some outerImpl)
    (binding : bindAll outer.act initial.nextScope outerPre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == outer.act then
        { current with scopes := (scope, initial.nextScope) :: outer.scopes } else current) } = .ok () bound)
    (called : getImplementation config context bound = .ok (calledId, calledImpl) bound)
    (channelSetup : channelsFor config.layout outer.act calledImpl.results.toList callOrigin bound = .ok channels prepared)
    (callPrefix : CallActivationPrefix (fuel + 7) config
      { outer with scopes := (scope, initial.nextScope) :: outer.scopes }
      context arguments channels callOrigin prepared inner innerPre innerBody entered)
    (innerEscape : enterActivation (fuel + 7) config inner innerPre innerBody callOrigin entered =
      .escape ⟨outer.act, .nonlocal targetId⟩ carriers before)
    (_distinct : outer.act ≠ inner.act)
    (landed : LandedResultChannels before outer.channels (outerImpl.results.toList.map (·.ty)) carriers) :
    let unwound := releaseScopeState outer scope initial.nextScope before
    enterActivation (fuel + 13) config outer outerPre
      (.mk scope (.expr (.call context arguments callOrigin) stmtOrigin :: rest) tail) outerOrigin initial =
      .ok carriers { unwound with activations := unwound.activations.filter (fun current => current.act != outer.act) } := by
  have callEscape := callPrefix.escape_call ⟨outer.act, .nonlocal targetId⟩ carriers innerEscape
  have bodyEscape : execActivationBody (fuel + 12) config outer outerPre
      (.mk scope (.expr (.call context arguments callOrigin) stmtOrigin :: rest) tail) initial =
      .escape ⟨outer.act, .nonlocal targetId⟩ carriers
        (releaseScopeState outer scope initial.nextScope before) := by
    unfold execActivationBody execResultScope
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [bind, EvalM.get, EvalM.set, withScope, binding, execStmts, execStmt, evalValue,
      called, channelSetup, callEscape, releaseScope]
  have preserved : LandedResultChannels (releaseScopeState outer scope initial.nextScope before)
      outer.channels (outerImpl.results.toList.map (·.ty)) carriers :=
    landed.of_construction_eq (before := before) (after := releaseScopeState outer scope initial.nextScope before) rfl
  simp only [enterActivation, lookup]
  exact finishActivation_catches_landed config.layout outer (outerImpl.results.toList.map (·.ty))
    outerOrigin _ initial _ ⟨outer.act, .nonlocal targetId⟩ carriers bodyEscape rfl preserved

#print axioms activation_call_escape_catches

end Goose.Proofs.ExitExecution
