import Goose.Proofs.ConstructionAcceptedParameterCallInitialized
import Goose.Proofs.ConstructionAcceptedScalarArgument

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem evalArguments_scalarParameter_body_initialized {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (results : callee.results = #[])
    (declared : callee.vars[0]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (initialized : frame.initialized = config.module.globals.size)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression descriptor.ty roots typingAfter rootsAfter) :
    let outcome := evalArguments fuel config frame.interpretation.environment callee.vars callee.params.toList [.byVal expression] state
    Goose.Proofs.Exit.stepState outcome = state ∧
      match outcome with
      | .ok values _ => ∃ value, values = [value] ∧ ∃ helperFrame activation after,
          let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
          let scopedState := ownershipResultScopeState activation callee.body.scope activated
          let root := Goose.Core.RootInst.local activation.act state.nextScope 0
          helperFrame.source.impl = callee ∧ helperFrame.initialized = config.module.globals.size ∧ helperFrame.phase = .implementation contextId ∧ helperFrame.interpretation.environment = activation ∧
          activation.act = state.nextAct ∧ activation.scopes = [] ∧ activation.channels = [] ∧
          freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
          freshScope activated = .ok activated.nextScope { activated with nextScope := activated.nextScope + 1 } ∧
          bindAll activation.act state.nextScope [(parameter.var, value)] scopedState = .ok () after ∧
          AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient)
            (registerRootType types root descriptor.ty) (fun other => other = root ∨ live other) regions pending ∧
          AcceptedFrame config accepted (entryStatementsFrame config helperFrame state.nextScope) after
            (registerRootType types root descriptor.ty) ∧
          SourcePosition accepted (entryStatementsFrame config helperFrame state.nextScope) (.statements callee.body.stmts)
      | .stop .. => True
      | _ => False := by
  have outcome := evalArguments_checkedScalar_world form fuel config accepted frame state ambient types live regions pending
    callee.vars parameter world source descriptor.ty roots typingAfter rootsAfter checked
  simp only [parameters] at ⊢
  cases execution : evalArguments fuel config frame.interpretation.environment callee.vars [parameter] [.byVal expression] state with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at outcome
    simpa [execution, Goose.Proofs.Exit.stepState] using outcome.1
  | escape address carriers after =>
    simp [execution, Goose.Proofs.Exit.stepState] at outcome
  | jump target kind after =>
    simp [execution, Goose.Proofs.Exit.stepState] at outcome
  | ok values after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at outcome
    have same := outcome.1
    subst after
    obtain ⟨value, equal, valid⟩ := outcome.2.2.2
    have initialWorld : AcceptedWorld config config.module.globals.size state ambient types live regions pending := initialized ▸ world
    obtain ⟨helperFrame, activation, after, sameImpl, helperInitialized, phase, environment, act, scopes, channels, fresh, scopeFresh,
      bound, extended, nextWorld, nextSource, position⟩ :=
      acceptedScalarParameterCallBody_initialized config accepted state ambient types live regions pending contextId context callee
        parameter descriptor value contextAt calleeAt parameters results declared scalar valid.represented valid.pointers initialWorld
    simp only [Goose.Proofs.Exit.stepState]
    exact ⟨trivial, value, equal, helperFrame, activation, after, sameImpl, helperInitialized, phase, environment, act, scopes, channels, fresh, scopeFresh,
      bound, nextWorld, nextSource, position⟩

#print axioms evalArguments_scalarParameter_body_initialized
end Goose.Proofs.ConstructionAcceptedExecution
