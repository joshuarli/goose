import Goose.Proofs.ConstructionAcceptedGlobalFrame
import Goose.Proofs.ConstructionAcceptedScalarGlobal
import Goose.Proofs.ConstructionAcceptedScalarControl

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem initGlobals_scalarExpression_single (fuel initialized : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before) (declared : config.module.globals[initialized]? = some descriptor)
    (form : AcceptedBinaryExpression descriptor.init)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ completed nextLive,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      initialized ≤ completed ∧ completed ≤ initialized + 1 ∧
      AcceptedWorld config completed after ambient types nextLive [] [] ∧
      (match outcome with
      | .ok _ _ => completed = initialized + 1 ∧ FutureGlobalsClear config completed after
      | .stop _ _ => completed = initialized ∧ FutureGlobalsClear config initialized after
      | .escape .. | .jump .. => False) := by
  obtain ⟨names, roots, typingAfter, rootsAfter, activeWorld, frameSource, checked⟩ :=
    accepted_scalarGlobalInitializer_checked config accepted initialized descriptor before ambient types live world clear declared form scalar
  let frame := scalarGlobalInitializerFrame config initialized before.nextAct names
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have activeClear := clear.freshAct
  have fixed : descriptor.ty.nonfixed = false := by
    rcases scalar with ⟨intTy, same⟩ | same <;> simp [same, Ty.nonfixed]
  have evaluated := evalValue_checked_binary_recursive form fuel config accepted frame activated ambient types live [] []
    activeWorld frameSource descriptor.ty roots typingAfter rootsAfter checked
  have unchanged : Goose.Proofs.Exit.stepState (evalValue fuel config environment descriptor.init activated) = activated := evaluated.1
  cases execution : evalValue fuel config environment descriptor.init activated with
  | stop reason after =>
    have same : after = activated := by simpa [execution, Goose.Proofs.Exit.stepState] using unchanged
    subst after
    have stopped : initGlobals fuel config [initialized] before = .stop reason activated := by
      simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, execution, environment, activated]
    simp only [stopped, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, live, by omega, by omega, activeWorld, rfl, activeClear⟩
  | escape address carriers after =>
    exact ((evalValue_scalar_controlFree form fuel config environment).1 activated address carriers after execution).elim
  | jump target kind after =>
    exact ((evalValue_scalar_controlFree form fuel config environment).2 activated target kind after execution).elim
  | ok value after =>
    have same : after = activated := by simpa [execution, Goose.Proofs.Exit.stepState] using unchanged
    subst after
    have valid := evaluated.2.1 value activated execution
    have scalarValue : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
      rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at valid <;>
        cases value <;> cases valid.represented <;> simp_all [Ty.nonfixed]
    obtain ⟨after, bound, afterWorld⟩ := bindRoot_scalarGlobal_world config initialized activated ambient types live descriptor value
      activeWorld declared scalarValue valid.represented valid.pointers
    have done : initGlobals fuel config [initialized] before = .ok () after := by
      simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, execution, bound, environment, activated]
    simp only [done, Goose.Proofs.Exit.stepState]
    exact ⟨initialized + 1, (fun root => root = .global initialized ∨ live root), by omega, by omega,
      afterWorld, rfl, activeClear.bindGlobal value bound⟩

#print axioms initGlobals_scalarExpression_single
end Goose.Proofs.ConstructionAcceptedExecution
