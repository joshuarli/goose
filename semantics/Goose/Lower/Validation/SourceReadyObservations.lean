import Goose.Lower.Validation.ReplacementEmission
import Goose.GIR.ReplacementContentFlowProofsSliceSubstitution

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

def ReadyCallObservations (module : GIR.Module) (func : Func) (state : State) (instruction : Inst) : Prop :=
  ∀ value calleeId arguments origin, instruction = .def value (.call calleeId arguments origin) →
    ∀ callee, module.funcs[calleeId]? = some callee → CallObservationReady callee func state arguments

theorem ReadyCallObservations.noncall {module : GIR.Module} {func : Func} {state : State} {instruction : Inst}
    (absent : ∀ value callee arguments origin, instruction ≠ .def value (.call callee arguments origin)) :
    ReadyCallObservations module func state instruction := by
  intro value callee arguments origin same
  exact False.elim (absent value callee arguments origin same)

theorem ReadyCallObservations.definition {module : GIR.Module} {func : Func} {state : State}
    (value : ValueId) (operation : Op)
    (absent : ∀ callee arguments origin, operation ≠ .call callee arguments origin) :
    ReadyCallObservations module func state (.def value operation) := by
  apply ReadyCallObservations.noncall
  intro result callee arguments origin same
  exact absent callee arguments origin (Inst.def.inj same).2

theorem ReadyCallObservations.call {module : GIR.Module} {func : Func} {state : State}
    (value : ValueId) (calleeId : FnId) (arguments : List ValueId) (origin : Option OriginId)
    (ready : ∀ callee, module.funcs[calleeId]? = some callee → CallObservationReady callee func state arguments) :
    ReadyCallObservations module func state (.def value (.call calleeId arguments origin)) := by
  intro result selected inputs source same callee row
  have fields := Inst.def.inj same
  have data := Op.call.inj fields.2
  obtain ⟨rfl, rfl, rfl⟩ := data
  exact ready callee row

theorem ReadyCallObservations.effect (module : GIR.Module) (func : Func) (state : State) (effect : Effect) :
    ReadyCallObservations module func state (.eff effect) :=
  .noncall (by intro value callee arguments origin impossible; cases impossible)

theorem ReadyCallObservations.term (module : GIR.Module) (func : Func) (state : State) (term : Term) :
    ReadyCallObservations module func state (.term term) :=
  .noncall (by intro value callee arguments origin impossible; cases impossible)

#print axioms ReadyCallObservations.noncall
#print axioms ReadyCallObservations.definition
#print axioms ReadyCallObservations.call
#print axioms ReadyCallObservations.effect
#print axioms ReadyCallObservations.term

end Goose.Lower.Validation.ReplacementContentFlowSource
