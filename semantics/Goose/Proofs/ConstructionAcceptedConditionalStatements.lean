import Goose.Proofs.ConstructionAcceptedGlobalBranchValidated

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem evalValue_statementConditional (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) (condition yes no : Expr) (yesStatements noStatements : List Stmt) (yesScope noScope origin : Nat)
    (shape : descriptor.init = .ifE condition ⟨yesScope, yesStatements, some yes⟩ ⟨noScope, noStatements, some no⟩ origin)
    (conditionForm : AcceptedBinaryExpression condition) (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no)
    (yesStatementsForm : ScalarExpressionStatements yesStatements) (noStatementsForm : ScalarExpressionStatements noStatements)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ nextLive,
      let activated := { before with nextAct := before.nextAct + 1 }
      let outcome := evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ descriptor.init activated
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with | .ok value _ => ValueRepresentation descriptor.ty value ∧ PointerTypedValue types descriptor.ty value | .stop .. => True | _ => False) := by
  let activated := { before with nextAct := before.nextAct + 1 }
  have activeWorld := (freshAct_acceptedWorld config id before ambient types live world).2
  have activeClear := clear.freshAct
  change ∃ nextLive, let outcome := evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ descriptor.init activated
    let after := Goose.Proofs.Exit.stepState outcome
    AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with | .ok value _ => ValueRepresentation descriptor.ty value ∧ PointerTypedValue types descriptor.ty value | .stop .. => True | _ => False)
  rw [shape]
  cases fuel with
  | zero =>
    simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨live, activeWorld, activeClear, trivial⟩
  | succ fuel =>
    have conditionRun := accepted_globalConditional_condition_evaluates fuel config accepted id descriptor before ambient types live
      world clear present condition _ _ origin shape conditionForm
    change Goose.Proofs.Exit.stepState (evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ condition activated) = activated ∧ _ at conditionRun
    have conditionFlow := conditionRun.2.2
    change (match evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ condition activated with
      | .ok (.bool _) _ | .stop _ _ => True | _ => False) at conditionFlow
    cases conditionExecution : evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ condition activated with
    | escape address carriers after | jump target kind after => simp only [conditionExecution] at conditionFlow
    | stop reason after =>
      have same : after = activated := by simpa [conditionExecution, Goose.Proofs.Exit.stepState] using conditionRun.1
      subst after
      have stopped : evalValue (fuel + 1) config ⟨0, before.nextAct, #[], [], []⟩ (.ifE condition ⟨yesScope, yesStatements, some yes⟩
          ⟨noScope, noStatements, some no⟩ origin) activated = .stop reason activated := by
        simp [evalValue, conditionExecution, bind]
      simp only [stopped, Goose.Proofs.Exit.stepState]
      exact ⟨live, activeWorld, activeClear, trivial⟩
    | ok value after =>
      have same : after = activated := by simpa [conditionExecution, Goose.Proofs.Exit.stepState] using conditionRun.1
      subst after
      cases value with
      | bool boolean =>
        cases boolean with
        | false =>
          obtain ⟨nextLive, branchWorld, branchClear, branchFlow⟩ := accepted_globalConditional_noBlock fuel config accepted id descriptor
            before ambient types live world clear present condition yes no yesStatements noStatements yesScope noScope origin shape
            conditionForm yesForm noForm yesStatementsForm noStatementsForm scalar
          cases branch : execBlock fuel config ⟨0, before.nextAct, #[], [], []⟩ [] [] ⟨noScope, noStatements, some no⟩ activated with
          | stop reason after =>
            dsimp only [activated] at branch
            simp only [branch, Goose.Proofs.Exit.stepState] at branchWorld branchClear
            have stopped : evalValue (fuel + 1) config ⟨0, before.nextAct, #[], [], []⟩ (.ifE condition ⟨yesScope, yesStatements, some yes⟩
                ⟨noScope, noStatements, some no⟩ origin) activated = .stop reason after := by
              simp [evalValue, conditionExecution, expectBool, bind, branch, pure, activated]
            simp only [stopped, Goose.Proofs.Exit.stepState]
            exact ⟨nextLive, branchWorld, branchClear, trivial⟩
          | escape address carriers after | jump target kind after =>
            dsimp only [activated] at branch
            simp only [branch] at branchFlow
          | ok result after =>
            cases result with
            | normal result =>
              dsimp only [activated] at branch
              simp only [branch, Goose.Proofs.Exit.stepState] at branchWorld branchClear branchFlow
              have done : evalValue (fuel + 1) config ⟨0, before.nextAct, #[], [], []⟩ (.ifE condition ⟨yesScope, yesStatements, some yes⟩
                  ⟨noScope, noStatements, some no⟩ origin) activated = .ok result after := by
                simp [evalValue, conditionExecution, expectBool, bind, branch, pure, activated]
              simp only [done, Goose.Proofs.Exit.stepState]
              exact ⟨nextLive, branchWorld, branchClear, branchFlow⟩
            | breaking result | continuing =>
              dsimp only [activated] at branch
              simp only [branch] at branchFlow
        | true =>
          obtain ⟨nextLive, branchWorld, branchClear, branchFlow⟩ := accepted_globalConditional_yesBlock fuel config accepted id descriptor
            before ambient types live world clear present condition yes no yesStatements noStatements yesScope noScope origin shape
            conditionForm yesForm noForm yesStatementsForm noStatementsForm scalar
          cases branch : execBlock fuel config ⟨0, before.nextAct, #[], [], []⟩ [] [] ⟨yesScope, yesStatements, some yes⟩ activated with
          | stop reason after =>
            dsimp only [activated] at branch
            simp only [branch, Goose.Proofs.Exit.stepState] at branchWorld branchClear
            have stopped : evalValue (fuel + 1) config ⟨0, before.nextAct, #[], [], []⟩ (.ifE condition ⟨yesScope, yesStatements, some yes⟩
                ⟨noScope, noStatements, some no⟩ origin) activated = .stop reason after := by
              simp [evalValue, conditionExecution, expectBool, bind, branch, pure, activated]
            simp only [stopped, Goose.Proofs.Exit.stepState]
            exact ⟨nextLive, branchWorld, branchClear, trivial⟩
          | escape address carriers after | jump target kind after =>
            dsimp only [activated] at branch
            simp only [branch] at branchFlow
          | ok result after =>
            cases result with
            | normal result =>
              dsimp only [activated] at branch
              simp only [branch, Goose.Proofs.Exit.stepState] at branchWorld branchClear branchFlow
              have done : evalValue (fuel + 1) config ⟨0, before.nextAct, #[], [], []⟩ (.ifE condition ⟨yesScope, yesStatements, some yes⟩
                  ⟨noScope, noStatements, some no⟩ origin) activated = .ok result after := by
                simp [evalValue, conditionExecution, expectBool, bind, branch, pure, activated]
              simp only [done, Goose.Proofs.Exit.stepState]
              exact ⟨nextLive, branchWorld, branchClear, branchFlow⟩
            | breaking result | continuing =>
              dsimp only [activated] at branch
              simp only [branch] at branchFlow
      | _ => simp only [conditionExecution] at conditionFlow

def StatementConditionalGlobal (descriptor : Global) : Prop :=
  ∃ condition yes no yesStatements noStatements yesScope noScope origin,
    descriptor.init = .ifE condition ⟨yesScope, yesStatements, some yes⟩ ⟨noScope, noStatements, some no⟩ origin ∧
    AcceptedBinaryExpression condition ∧ AcceptedBinaryExpression yes ∧ AcceptedBinaryExpression no ∧
    ScalarExpressionStatements yesStatements ∧ ScalarExpressionStatements noStatements ∧
    ((∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)

theorem initGlobals_statementConditional_single (fuel id : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (world : AcceptedWorld config id before ambient types live [] [])
    (clear : FutureGlobalsClear config id before) (present : config.module.globals[id]? = some descriptor)
    (form : StatementConditionalGlobal descriptor) :
    ∃ completed nextLive,
      let outcome := initGlobals fuel config [id] before
      let after := Goose.Proofs.Exit.stepState outcome
      id ≤ completed ∧ completed ≤ id + 1 ∧ AcceptedWorld config completed after ambient types nextLive [] [] ∧
      (match outcome with | .ok _ _ => completed = id + 1 ∧ FutureGlobalsClear config completed after | .stop _ _ => completed = id ∧ FutureGlobalsClear config id after | .escape .. | .jump .. => False) := by
  obtain ⟨condition, yes, no, yesStatements, noStatements, yesScope, noScope, origin, shape, conditionForm, yesForm, noForm, yesStatementsForm, noStatementsForm, scalar⟩ := form
  have fixed : descriptor.ty.nonfixed = false := by
    rcases scalar with ⟨intTy, same⟩ | same <;> simp [same, Ty.nonfixed]
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  obtain ⟨nextLive, evaluatedWorld, evaluatedClear, flow⟩ :=
    evalValue_statementConditional fuel config accepted id descriptor before ambient types live world clear present
      condition yes no yesStatements noStatements yesScope noScope origin shape conditionForm yesForm noForm yesStatementsForm noStatementsForm scalar
  change AcceptedWorld config id (Goose.Proofs.Exit.stepState (evalValue fuel config environment descriptor.init activated))
    ambient types nextLive [] [] at evaluatedWorld
  change FutureGlobalsClear config id (Goose.Proofs.Exit.stepState (evalValue fuel config environment descriptor.init activated)) at evaluatedClear
  change (match evalValue fuel config environment descriptor.init activated with
    | .ok value _ => ValueRepresentation descriptor.ty value ∧ PointerTypedValue types descriptor.ty value
    | .stop .. => True | _ => False) at flow
  cases execution : evalValue fuel config environment descriptor.init activated with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at evaluatedWorld evaluatedClear
    have stopped : initGlobals fuel config [id] before = .stop reason after := by
      simp [initGlobals, present, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, execution, environment, activated]
    simp only [stopped, Goose.Proofs.Exit.stepState]
    exact ⟨id, nextLive, by omega, by omega, evaluatedWorld, rfl, evaluatedClear⟩
  | escape address carriers after | jump target kind after => simp only [execution] at flow
  | ok value evaluated =>
    simp only [execution, Goose.Proofs.Exit.stepState] at evaluatedWorld evaluatedClear flow
    have scalarValue : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
      rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at flow <;>
        cases value <;> cases flow.1 <;> simp_all [Ty.nonfixed]
    obtain ⟨after, bound, afterWorld⟩ := bindRoot_scalarGlobal_world config id evaluated ambient types nextLive descriptor
      value evaluatedWorld present scalarValue flow.1 flow.2
    have done : initGlobals fuel config [id] before = .ok () after := by
      simp [initGlobals, present, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, execution, bound, environment, activated]
    simp only [done, Goose.Proofs.Exit.stepState]
    exact ⟨id + 1, (fun root => root = .global id ∨ nextLive root), by omega, by omega,
      afterWorld, rfl, evaluatedClear.bindGlobal value bound⟩

#print axioms initGlobals_statementConditional_single
#print axioms evalValue_statementConditional
end Goose.Proofs.ConstructionAcceptedExecution
