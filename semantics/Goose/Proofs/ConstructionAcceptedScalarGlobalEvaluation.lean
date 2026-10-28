import Goose.Proofs.ConstructionAcceptedNestedGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem initGlobals_scalar_fromEvaluation (fuel id : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (evaluate : ∀ names roots typingAfter rootsAfter,
      let frame := scalarGlobalInitializerFrame config id before.nextAct names
      let activated := { before with nextAct := before.nextAct + 1 }
      AcceptedWorld config id activated ambient types live [] [] → AcceptedFrame config accepted frame activated types →
      CheckedValue frame descriptor.init descriptor.ty roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := evalValue fuel config frame.interpretation.environment descriptor.init activated
        RootTypesExtend types nextTypes ∧
        AcceptedWorld config id (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive [] [] ∧
        FutureGlobalsClear config id (Goose.Proofs.Exit.stepState outcome) ∧
        (match outcome with
         | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation descriptor.ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ completed nextTypes nextLive nextAmbient,
      let outcome := initGlobals fuel config [id] before
      let after := Goose.Proofs.Exit.stepState outcome
      RootTypesExtend types nextTypes ∧ id ≤ completed ∧ completed ≤ id + 1 ∧
      AcceptedWorld config completed after nextAmbient nextTypes nextLive [] [] ∧
      (match outcome with
       | .ok _ _ => nextAmbient = ambient ∧ completed = id + 1 ∧ FutureGlobalsClear config completed after
       | .stop _ _ => completed = id ∧ FutureGlobalsClear config id after
       | .escape .. | .jump .. => False) := by
  obtain ⟨names, roots, typingAfter, rootsAfter, activeWorld, frameSource, checked⟩ :=
    accepted_nestedGlobal_checked config accepted id descriptor before ambient types live world clear present scalar
  let frame := scalarGlobalInitializerFrame config id before.nextAct names
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have fixed : descriptor.ty.nonfixed = false := by
    rcases scalar with ⟨intTy, same⟩ | same <;> simp [same, Ty.nonfixed]
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, safeWorld, safeClear, safeResult⟩ :=
    evaluate names roots typingAfter rootsAfter activeWorld frameSource checked
  change AcceptedWorld config id (Goose.Proofs.Exit.stepState (evalValue fuel config environment descriptor.init activated)) nextAmbient nextTypes nextLive [] [] at safeWorld
  change FutureGlobalsClear config id (Goose.Proofs.Exit.stepState (evalValue fuel config environment descriptor.init activated)) at safeClear
  change (match evalValue fuel config environment descriptor.init activated with
    | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation descriptor.ty value
    | .stop .. => True | .escape .. | .jump .. => False) at safeResult
  cases execution : evalValue fuel config environment descriptor.init activated with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at safeWorld safeClear safeResult
    have stopped : initGlobals fuel config [id] before = .stop reason after := by
      simp [initGlobals, present, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, execution, environment, activated]
    simp only [stopped, Goose.Proofs.Exit.stepState]
    exact ⟨id, nextTypes, nextLive, nextAmbient, extend, by omega, by omega, safeWorld, rfl, safeClear⟩
  | escape address carriers after | jump target kind after => simp [execution] at safeResult
  | ok value evaluated =>
    simp only [execution, Goose.Proofs.Exit.stepState] at safeWorld safeClear safeResult
    obtain ⟨sameAmbient, represented⟩ := safeResult
    subst nextAmbient
    have scalarValue : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
      rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at represented <;>
        cases value <;> cases represented <;> simp_all [Ty.nonfixed]
    have pointers : PointerTypedValue nextTypes descriptor.ty value := by
      rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at represented ⊢ <;>
        cases value <;> cases represented <;> constructor
    obtain ⟨after, bound, afterWorld⟩ := bindRoot_scalarGlobal_world config id evaluated ambient nextTypes nextLive descriptor
      value safeWorld present scalarValue represented pointers
    have done : initGlobals fuel config [id] before = .ok () after := by
      simp [initGlobals, present, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, execution, bound, environment, activated]
    simp only [done, Goose.Proofs.Exit.stepState]
    exact ⟨id + 1, nextTypes, (fun root => root = .global id ∨ nextLive root), ambient, extend, by omega, by omega,
      afterWorld, rfl, rfl, safeClear.bindGlobal value bound⟩

#print axioms initGlobals_scalar_fromEvaluation
end Goose.Proofs.ConstructionAcceptedExecution
