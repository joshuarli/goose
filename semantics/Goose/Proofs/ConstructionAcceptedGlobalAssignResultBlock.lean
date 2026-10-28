import Goose.Proofs.ConstructionAcceptedLiteralResultBlock
import Goose.Proofs.ConstructionAcceptedSingleGlobalStatement
import Goose.Proofs.ConstructionAcceptedEntryActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem execResultBlock_globalAssign_integerTail_world (fuel checkFuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (scope id : Nat) (expression : Expr)
    (origin : Nat) (intTy : Goose.Core.IntTy) (literal : Int) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (position : SourcePosition accepted frame (.block ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩))
    (nesting : frame.typingFuel = checkFuel + 3)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    RegisterBreakActionOutcome config accepted frame ambient types live regions pending
      (execResultBlock fuel config frame.interpretation.environment [.register (.int intTy)]
        ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ state) := by
  cases fuel with
  | zero => simp [execResultBlock, timeout, EvalM.stop, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    cases fuel with
    | zero => simp [execResultBlock, execResultBlockWith, timeout, EvalM.stop, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      let child := unusedChildScopeFrame frame scope state.nextScope (checkFuel + 2)
      let scopeState := ownershipResultScopeState frame.interpretation.environment scope state
      have scopedWorld : AcceptedWorld config child.initialized scopeState ambient types live regions pending := by
        exact acceptedWorld_resultScope config frame.initialized state ambient types live regions pending frame.interpretation.environment scope world
      have childSource : AcceptedFrame config accepted child scopeState types := by
        have entered := source.enterScope_withoutDeclarations scope (checkFuel + 2) fresh absent
        have actual := entered.withActivations (({ state with nextScope := state.nextScope + 1 }).activations.map fun (current : RuntimeActivation) =>
          if current.act == frame.interpretation.environment.act then
            { current with scopes := (scope, state.nextScope) :: frame.interpretation.environment.scopes } else current)
        simpa [scopeState, ownershipResultScopeState, child] using actual
      have childPosition : SourcePosition accepted child (.statements [.assign (.global id) expression origin]) := by
        have statementsPosition := position.block_statements accepted frame scope (checkFuel + 2)
          [.assign (.global id) expression origin] (some (.lit intTy literal)) (by simpa [Nat.add_assoc] using nesting)
        have actual := SourcePosition.instantiate statementsPosition
          (frame.interpretation.enterScope scope state.nextScope) frame.initialized
        simpa [child, unusedChildScopeFrame, blockStatementsFrame] using actual
      have statementSafe := execStmts_singleScalarGlobal_world fuel checkFuel config accepted child scopeState ambient types live regions pending
        id expression origin form scopedWorld childSource initialized childPosition rfl scalar
      exact execResultBlock_integerTail_world fuel config accepted frame state ambient types live regions pending
        scope (checkFuel + 2) [.assign (.global id) expression origin] intTy literal source absent statementSafe

#print axioms execResultBlock_globalAssign_integerTail_world
end Goose.Proofs.ConstructionAcceptedExecution
