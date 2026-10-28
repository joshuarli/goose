import Goose.Proofs.ConstructionAcceptedSingleGlobalReplay
import Goose.Proofs.ConstructionAcceptedSingleGlobalStatement
import Goose.Proofs.ConstructionAcceptedScalarGlobalObservation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmts_singleScalarGlobal_observed (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Nat) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (position : SourcePosition accepted frame (.statements [.assign (.global id) expression origin]))
    (nesting : frame.typingFuel = checkFuel + 2)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    let step := execStmts fuel config frame.interpretation.environment [.assign (.global id) expression origin] before
    let after := Goose.Proofs.Exit.stepState step
    AcceptedWorld config frame.initialized after ambient types live regions pending ∧
      AcceptedFrame config accepted frame after types ∧
      match step with
      | .ok flow _ => flow = .normal .unit ∧ ScalarGlobalObservation frame.interpretation.environment.act before after ∧
          ∃ rootsAfter, rootsAfter.nextVar = frame.rootCursor.nextVar ∧
            GlobalEffectTargetsBounded rootsAfter.eff config.module.globals.size ∧
            typeStatements frame.typingFuel frame.typing [.assign (.global id) expression origin] frame.typingCounter = .ok (frame.typing, frame.typingCounter) ∧
            rpStmts frame.source [.assign (.global id) expression origin] frame.rootCursor = .ok ((), rootsAfter)
      | .stop .. => True
      | _ => False := by
  have result := execStmts_singleScalarGlobal_world fuel checkFuel config accepted frame before ambient types live regions pending
    id expression origin form world source initialized position nesting scalar
  cases executed : execStmts fuel config frame.interpretation.environment [.assign (.global id) expression origin] before with
  | escape address carriers after | jump target kind after => simp [executed, RegisterBreakActionOutcome] at result
  | stop reason after =>
    simp only [executed, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at result ⊢
    exact ⟨result.1.1, result.1.2.1, trivial⟩
  | ok flow after =>
    simp only [executed, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at result ⊢
    have normal := result.2
    subst flow
    obtain ⟨rootsAfter, sameRoot, finalBounded, typed, rooted⟩ := position.singleScalarGlobal_replay accepted frame before types
      id expression origin checkFuel form source initialized bounded nesting
    have observation : ScalarGlobalObservation frame.interpretation.environment.act before after := by
      cases fuel with
      | zero => simp [execStmts, timeout, EvalM.stop] at executed
      | succ fuel =>
        let head := { frame with typingFuel := checkFuel + 1 }
        have headPosition := position.statements_head accepted frame (.assign (.global id) expression origin) [] (checkFuel + 1) nesting
        have headObservation := execStmt_sourceScalarAssignGlobal_observation fuel checkFuel config accepted head before ambient types live regions pending
          id expression origin form world (source.withTypingFuel (checkFuel + 1)) initialized headPosition rfl scalar
        cases headStep : execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before with
        | stop reason middle | escape address carriers middle | jump target kind middle => simp [execStmts, bind, headStep] at executed
        | ok headFlow middle =>
          cases fuel with
          | zero => simp [execStmt, timeout, EvalM.stop] at headStep
          | succ fuel =>
            cases headFlow <;> simp [execStmts, bind, headStep, pure] at executed
            case normal value =>
              subst after
              exact ScalarAssignmentObservation.globalSuccess frame.interpretation.environment.act (by simpa [head, headStep] using headObservation)
    exact ⟨result.1.1, result.1.2.1, rfl, observation, rootsAfter, sameRoot, finalBounded, typed, rooted⟩

#print axioms execStmts_singleScalarGlobal_observed
end Goose.Proofs.ConstructionAcceptedExecution
