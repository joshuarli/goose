import Goose.Proofs.ConstructionAcceptedScalarAssignSource
import Goose.Proofs.ConstructionAcceptedRegisterBreakOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmts_singleScalarGlobal_world (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Nat) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (initialized : frame.initialized = config.module.globals.size)
    (position : SourcePosition accepted frame (.statements [.assign (.global id) expression origin]))
    (nesting : frame.typingFuel = checkFuel + 2)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    let step := execStmts fuel config frame.interpretation.environment [.assign (.global id) expression origin] before
    RegisterBreakActionOutcome config accepted frame ambient types live regions pending step ∧
      match step with | .ok flow _ => flow = .normal .unit | _ => True := by
  cases fuel with
  | zero => simp [execStmts, timeout, EvalM.stop, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    let head := { frame with typingFuel := checkFuel + 1 }
    have headPosition : SourcePosition accepted head (.statement (.assign (.global id) expression origin)) := by
      exact position.statements_head accepted frame _ [] (checkFuel + 1) (by simpa [Nat.add_assoc] using nesting)
    have headSource := source.withTypingFuel (checkFuel + 1)
    have result := execStmt_sourceScalarAssignGlobal fuel checkFuel config accepted head before ambient types live regions pending
      id expression origin form world headSource initialized headPosition rfl scalar
    cases executed : execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before with
    | escape address carriers after | jump target kind after =>
      simp [head, executed, Goose.Proofs.Exit.stepState] at result
    | stop reason after =>
      simp only [head, executed, Goose.Proofs.Exit.stepState] at result
      have finalSource := result.2.1.withTypingFuel frame.typingFuel
      simpa [execStmts, bind, executed, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using
        And.intro result.1 (And.intro finalSource True.intro)
    | ok flow after =>
      simp only [head, executed, Goose.Proofs.Exit.stepState] at result
      have same := result.2.2
      subst flow
      have finalSource := result.2.1.withTypingFuel frame.typingFuel
      cases fuel <;>
        simpa [execStmts, bind, pure, executed, timeout, EvalM.stop, RegisterBreakActionOutcome,
          Goose.Proofs.Exit.stepState] using And.intro result.1 (And.intro finalSource True.intro)

#print axioms execStmts_singleScalarGlobal_world
end Goose.Proofs.ConstructionAcceptedExecution
