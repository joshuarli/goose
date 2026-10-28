import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedScalarGlobalEvaluation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem initGlobals_registerCall_fromEvaluation (fuel id : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (target origin : Nat) (context : Context) (implementation : Impl)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor)
    (form : descriptor.init = .call target [] origin)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨descriptor.ty, .register, none⟩])
    (evaluate : ∀ names roots typingAfter rootsAfter,
      let frame := scalarGlobalInitializerFrame config id before.nextAct names
      let activated := { before with nextAct := before.nextAct + 1 }
      AcceptedWorld config id activated ambient types live [] [] → AcceptedFrame config accepted frame activated types →
      CheckedValue frame (.call target [] origin) descriptor.ty roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := evalValue fuel config frame.interpretation.environment (.call target [] origin) activated
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
  apply initGlobals_scalar_fromEvaluation fuel id config accepted before ambient types live descriptor world clear present scalar
  intro names roots typingAfter rootsAfter frame activated activeWorld frameSource checked
  have callChecked : CheckedValue (scalarGlobalInitializerFrame config id before.nextAct names) (.call target [] origin)
      descriptor.ty roots typingAfter rootsAfter := by simpa [form] using checked
  have outcome := evaluate names roots typingAfter rootsAfter activeWorld frameSource callChecked
  rw [form]
  exact outcome

theorem initGlobals_recursive_register_single_withLocals (fuel id : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (target origin : Nat) (context : Context) (implementation : Impl)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor)
    (form : descriptor.init = .call target [] origin)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨descriptor.ty, .register, none⟩])
    (graph : RegisterCallGraphWithLocals config descriptor.ty) :
    ∃ completed nextTypes nextLive nextAmbient,
      let outcome := initGlobals fuel config [id] before
      let after := Goose.Proofs.Exit.stepState outcome
      RootTypesExtend types nextTypes ∧ id ≤ completed ∧ completed ≤ id + 1 ∧
      AcceptedWorld config completed after nextAmbient nextTypes nextLive [] [] ∧
      (match outcome with
       | .ok _ _ => nextAmbient = ambient ∧ completed = id + 1 ∧ FutureGlobalsClear config completed after
       | .stop _ _ => completed = id ∧ FutureGlobalsClear config id after
       | .escape .. | .jump .. => False) := by
  apply initGlobals_registerCall_fromEvaluation fuel id config accepted before ambient types live descriptor target origin context implementation
    world clear present form scalar contextAt implementationAt parameters results
  intro names roots typingAfter rootsAfter
  dsimp only
  intro activeWorld frameSource checked
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, flow⟩ :=
    evalValue_recursive_register_withLocals fuel config accepted (scalarGlobalInitializerFrame config id before.nextAct names)
      { before with nextAct := before.nextAct + 1 } ambient types live [] [] target context implementation descriptor.ty origin
      graph activeWorld frameSource contextAt implementationAt parameters results scalar roots typingAfter rootsAfter checked
  exact ⟨nextTypes, nextLive, nextAmbient, extend, finalWorld, clear, flow⟩

#print axioms initGlobals_registerCall_fromEvaluation
#print axioms initGlobals_recursive_register_single_withLocals
end Goose.Proofs.ConstructionAcceptedExecution
