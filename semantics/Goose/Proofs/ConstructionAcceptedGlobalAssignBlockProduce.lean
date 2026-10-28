import Goose.Proofs.ConstructionAcceptedGlobalAssignBlockShape
import Goose.Proofs.ConstructionAcceptedLiteralBlockProducer

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalProduce_globalAssign_integerTail_world (fuel checkFuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (scope id : Nat) (expression : Expr)
    (origin blockOrigin : Nat) (intTy : Goose.Core.IntTy) (literal : Int) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (position : SourcePosition accepted frame (.block ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩))
    (nesting : frame.typingFuel = checkFuel + 3)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    let step := evalProduce fuel config frame.interpretation.environment [.register (.int intTy)]
      (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) state
    RegisterBreakActionOutcome config accepted frame ambient types live regions pending step ∧
      match step with | .ok carriers _ => carriers = [.register (.int intTy literal)] | _ => True := by
  cases fuel with
  | zero => simp [evalProduce, timeout, EvalM.stop, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    let target : BreakTarget := ⟨state.nextScope, frame.interpretation.environment.act, .block, [.register (.int intTy)]⟩
    let pushed := { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks }
    let block : Block := ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩
    let body : EvalM (Flow × List Carrier) := execResultBlock fuel config frame.interpretation.environment [.register (.int intTy)] block
    let action : EvalM (List Carrier) := do
      let (flow, carriers) ← body
      match flow with | .normal _ => pure carriers | _ => fault .flow
    let receive : JumpKind → EvalM (List Carrier) := fun kind => do
      match kind with
      | .breakValue carriers => landCarriersInto blockOrigin [.register (.int intTy)] carriers; pure carriers
      | .continueLoop => fault .flow
    have pushedWorld : AcceptedWorld config frame.initialized pushed (.breakTarget target [] :: ambient) types live regions pending := by
      exact world.pushRegisterBreak config frame.initialized state ambient types live regions pending frame.interpretation.environment.act .block (.int intTy)
    have pushedSource : AcceptedFrame config accepted frame pushed types := source.pushBreak frame.interpretation.environment.act .block [.register (.int intTy)]
    have bodySafe := execResultBlock_globalAssign_integerTail_world fuel checkFuel config accepted frame pushed
      (.breakTarget target [] :: ambient) types live regions pending scope id expression origin intTy literal form
      pushedWorld pushedSource initialized fresh absent position nesting scalar
    have bodyShape : ∀ result after, body pushed = .ok result after → result = (.normal .unit, [.register (.int intTy literal)]) := by
      intro result after executed
      cases fuel with
      | zero => simp [body, block, execResultBlock, timeout, EvalM.stop] at executed
      | succ fuel =>
        cases fuel with
        | zero => simp [body, block, execResultBlock, execResultBlockWith, timeout, EvalM.stop] at executed
        | succ fuel =>
          exact execResultBlock_globalAssign_integerTail_shape fuel checkFuel config accepted frame pushed
            (.breakTarget target [] :: ambient) types live regions pending scope id expression origin intTy literal form
            pushedWorld pushedSource initialized fresh absent position nesting scalar result after executed
    have actionSafe : RegisterBreakActionOutcome config accepted frame (.breakTarget target [] :: ambient) types live regions pending (action pushed) := by
      cases executed : body pushed with
      | stop reason after => simpa [action, bind, executed, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState, body, block] using bodySafe
      | escape address carriers after | jump address kind after => simp [body, block, executed, RegisterBreakActionOutcome] at bodySafe
      | ok result after =>
        have same := bodyShape result after executed
        subst result
        simpa [action, bind, pure, executed, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState, body, block] using bodySafe
    have safe := withRegisterBreak_outcome config accepted frame state ambient types live regions pending
      frame.interpretation.environment.act .block (.int intTy) action receive world actionSafe
    have shape : ∀ result after, withBreakTarget frame.interpretation.environment.act .block [.register (.int intTy)] action receive state = .ok result after →
        result = [.register (.int intTy literal)] := by
      intro result after evaluated
      cases executed : body pushed with
      | stop reason middle | escape address carriers middle =>
        simp [withBreakTarget, pushed, target, action, bind, executed, mapStepState] at evaluated
      | jump address kind middle =>
        simp [body, block, executed, RegisterBreakActionOutcome] at bodySafe
      | ok value middle =>
        have same := bodyShape value middle executed
        subst value
        simp [withBreakTarget, pushed, target, action, bind, pure, executed, mapStepState] at evaluated
        exact evaluated.1.symm
    rw [evalProduce_blockRegister]
    cases evaluated : withBreakTarget frame.interpretation.environment.act .block [.register (.int intTy)] action receive state with
    | stop reason after => simpa [evaluated, RegisterBreakActionOutcome] using safe
    | escape address carriers after | jump address kind after => simp [evaluated, RegisterBreakActionOutcome] at safe
    | ok result after =>
      simp only [evaluated, RegisterBreakActionOutcome] at safe
      exact ⟨safe, shape result after evaluated⟩

#print axioms evalProduce_globalAssign_integerTail_world
end Goose.Proofs.ConstructionAcceptedExecution
