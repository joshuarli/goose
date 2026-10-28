import Goose.Proofs.ConstructionAcceptedScalarGlobalSequenceReplay
import Goose.Proofs.ConstructionAcceptedSingleGlobalObserved

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmts_scalarGlobalAssignments_observed {statements : List Stmt}
    (form : ScalarGlobalAssignments statements) :
    ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
      (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.initialized = config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      SourcePosition accepted frame (.statements statements) →
      (∀ id expression origin, .assign (.global id) expression origin ∈ statements → ∀ descriptor,
        config.module.globals[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) →
      let outcome := execStmts fuel config frame.interpretation.environment statements before
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config frame.initialized after ambient types live regions pending ∧
      AcceptedFrame config accepted frame after types ∧
      (match outcome with
      | .ok flow _ => flow = .normal .unit ∧ ScalarGlobalObservation frame.interpretation.environment.act before after
      | .stop .. => True | _ => False) := by
  induction form with
  | nil =>
    intro fuel config accepted frame before ambient types live regions pending world source initialized bounded position scalar
    cases fuel with
    | zero => simp [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel => simp [execStmts, pure, Goose.Proofs.Exit.stepState, world, source, ScalarGlobalObservation.refl]
  | cons id expression origin rest expressionForm restForm ih =>
    intro fuel config accepted frame before ambient types live regions pending world source initialized bounded position scalar
    cases fuel with
    | zero => simp [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have nesting' : frame.typingFuel = checkFuel + 2 := by omega
          obtain ⟨middleRoots, sameRoot, middleBounded, headTyped, headRooted, tailPosition⟩ :=
            position.scalarAssign_tailReplay accepted frame before types (.global id) expression origin rest checkFuel
              expressionForm source initialized bounded nesting' (Or.inr ⟨id, rfl⟩)
          let head := { frame with typingFuel := checkFuel + 1 }
          let middle := { frame with typingFuel := checkFuel + 1, rootCursor := middleRoots }
          have headPosition := position.statements_head accepted frame (.assign (.global id) expression origin) rest (checkFuel + 1) nesting'
          have headScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
              (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := scalar id expression origin (by simp)
          have result := execStmt_sourceScalarAssignGlobal fuel checkFuel config accepted head before ambient types live regions pending
            id expression origin expressionForm world (source.withTypingFuel (checkFuel + 1)) initialized headPosition rfl headScalar
          have observation := execStmt_sourceScalarAssignGlobal_observation fuel checkFuel config accepted head before ambient types live regions pending
            id expression origin expressionForm world (source.withTypingFuel (checkFuel + 1)) initialized headPosition rfl headScalar
          cases step : execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before with
          | escape address carriers after | jump target kind after => simp [head, step, Goose.Proofs.Exit.stepState] at result
          | stop reason after =>
            simp only [head, step, Goose.Proofs.Exit.stepState] at result
            have finalSource := result.2.1.withTypingFuel frame.typingFuel
            simpa [execStmts, bind, step, Goose.Proofs.Exit.stepState] using And.intro result.1 (And.intro finalSource True.intro)
          | ok flow after =>
            simp only [head, step, Goose.Proofs.Exit.stepState] at result
            have normal := result.2.2
            subst flow
            have middleSource : AcceptedFrame config accepted middle after types := result.2.1.withRootCursor middleRoots sameRoot
            have restScalar : ∀ id expression origin, .assign (.global id) expression origin ∈ rest → ∀ descriptor,
                config.module.globals[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
              intro target value targetOrigin member descriptor declared
              exact scalar target value targetOrigin (by simp [member]) descriptor declared
            have tail := ih fuel config accepted middle after ambient types live regions pending result.1 middleSource
              initialized middleBounded tailPosition restScalar
            have firstObservation : ScalarGlobalObservation frame.interpretation.environment.act before after :=
              ScalarAssignmentObservation.globalSuccess _ (by simpa [head, step] using observation)
            cases tailStep : execStmts fuel config frame.interpretation.environment rest after with
            | escape address carriers final | jump target kind final => simp [middle, tailStep, Goose.Proofs.Exit.stepState] at tail
            | stop reason final =>
              simp only [middle, tailStep, Goose.Proofs.Exit.stepState] at tail
              have finalSource := (tail.2.1.withRootCursor frame.rootCursor sameRoot.symm).withTypingFuel frame.typingFuel
              simpa [execStmts, bind, step, tailStep, Goose.Proofs.Exit.stepState] using And.intro tail.1 (And.intro finalSource True.intro)
            | ok finalFlow final =>
              simp only [middle, tailStep, Goose.Proofs.Exit.stepState] at tail
              obtain ⟨normal, lastObservation⟩ := tail.2.2
              subst finalFlow
              have finalSource := (tail.2.1.withRootCursor frame.rootCursor sameRoot.symm).withTypingFuel frame.typingFuel
              have combined := firstObservation.trans lastObservation
              simp only [execStmts, bind, step, tailStep, Goose.Proofs.Exit.stepState]
              exact ⟨tail.1, by simpa [middle] using finalSource, trivial, combined⟩

#print axioms execStmts_scalarGlobalAssignments_observed
end Goose.Proofs.ConstructionAcceptedExecution
