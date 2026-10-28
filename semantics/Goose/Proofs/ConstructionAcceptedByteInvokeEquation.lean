import Goose.Proofs.ConstructionAcceptedByteReceiverCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem invokeByteReceiver_body (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId id : Nat) (origin : OriginId) (context : Context) (helper : Impl) (state : ExecutionState)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver)
    (current : destinationCurrent state.construction id = .ok id)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, helper.vars, [], [.construct id]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    invokeCall (fuel + 5) config environment contextId [] [.construct id] origin state =
      (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] helper.body) >>= fun carriers =>
        deliverCarriers (fuel + 4) config.layout [.construct id] carriers origin) pushed := by
  have renewal : renewReceivingDestination id state.construction = .ok id state.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, ready.present, ready.opened]
  have adapted := adapt_open_byte_receiver config state id ready receiver
  simp [invokeCall, getImplementation, contextAt, helperAt, parameters, results, evalArguments, renewal,
    adapted, liftConstruction, bind, pure, freshAct, EvalM.get, EvalM.set, enterActivation,
    Nat.not_le.mpr depth]

#print axioms invokeByteReceiver_body
end Goose.Proofs.ConstructionAcceptedExecution
