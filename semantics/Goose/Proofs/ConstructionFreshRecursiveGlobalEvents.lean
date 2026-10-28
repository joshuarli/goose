import Goose.Proofs.ConstructionMixedScalarValueEvents
import Goose.Proofs.ConstructionFreshByteBindingEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem initGlobal_recursiveScalar_events (fuel global : Nat) (config : EvalConfig)
    (descriptor : Global) (before : ExecutionState)
    (declared : config.module.globals[global]? = some descriptor)
    (form : AcceptedBinaryExpression descriptor.init)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    (Goose.Proofs.Exit.stepState (initGlobals fuel config [global] before)).construction.events = before.construction.events := by
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have frame := bind_events_frame (evalValue fuel config environment descriptor.init)
    (fun value => bindRoot (.global global) value >>= fun _ => pure ()) activated (by
      intro value current
      rw [bind_events_frame (bindRoot (.global global) value)]
      · exact bindRoot_events (.global global) value current
      · intro result after
        simp [pure, Goose.Proofs.Exit.stepState])
  have query := evalValue_scalar_query form fuel config environment activated
  rw [query] at frame
  rcases scalar with ⟨intTy, ty⟩ | ty <;>
    simp only [initGlobals, declared, ty, Ty.nonfixed, freshAct, EvalM.get, EvalM.set, bind, pure, Bool.false_eq_true, ↓reduceIte] <;>
    simpa only [bind, pure, environment, activated] using frame

#print axioms initGlobal_recursiveScalar_events

end Goose.Proofs.ConstructionAcceptedExecution
