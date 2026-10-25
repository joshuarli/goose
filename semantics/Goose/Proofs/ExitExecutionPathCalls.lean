import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionInvocationValuesNative

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem neverEscapes_bind_escape (action : EvalM α) (next : α → EvalM β)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (first : ProducerNeverEscapes action)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    ∃ value prepared, action initial = .ok value prepared ∧
      next value prepared = .escape address carriers final := by
  cases evaluated : action initial with
  | ok value prepared => exact ⟨value, prepared, rfl, by simpa only [bind, evaluated] using escaped⟩
  | stop reason after | jump target kind after => simp only [bind, evaluated] at escaped; cases escaped
  | escape target payload after => exact False.elim (first _ _ _ _ evaluated)

private theorem neverEscapes_deliverCarriers (fuel : Nat) (layout : LayoutEnv)
    (channels : List Channel) (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (deliverCarriers fuel layout channels carriers origin) := by
  unfold deliverCarriers
  repeat' first
    | with_reducible exact producerNeverEscapes_copyValue _ _ _ _ _ _
    | with_reducible exact producerNeverEscapes_completedReceivingDestination _
    | producer_never_escapes_step

theorem callInvocation_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : invokeCall (fuel + 1) config environment context arguments channels origin initial =
      .escape address carriers final) :
    (∃ id implementation firstChannels prepared,
      CallArgumentPrefix config context channels origin initial id implementation firstChannels prepared ∧
      evalArguments fuel config environment implementation.vars implementation.params.toList arguments prepared =
        .escape address carriers final) ∨
    ∃ activation pre body entered,
      CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered ∧
      enterActivation fuel config activation pre body origin entered = .escape address carriers final := by
  simp only [invokeCall] at escaped
  obtain ⟨⟨id, implementation⟩, lookupState, lookup, rest⟩ :=
    neverEscapes_bind_escape _ _ initial final address carriers (valueNeverEscapes_getImplementation _ _) escaped
  split at rest
  · simp only [fault] at rest; cases rest
  · rename_i arity
    have receivingSafe : ProducerNeverEscapes
        (((channels.zip implementation.results.toList).mapM fun pair => do
          match pair.2.request, pair.1 with
          | .register, _ => pure (Channel.register pair.2.ty)
          | .value, .construct incoming | .elementRun, .construct incoming =>
              let destination ← liftConstruction origin (renewReceivingDestination incoming)
              liftConstruction origin (adaptDestinationType destination pair.2.ty)
              pure (.construct destination)
          | .value, .register _ | .elementRun, .register _ => fault .shape
          | _, .completion _ => fault .flow) : EvalM (List Channel)) := by
      producer_never_escapes_base
    obtain ⟨firstChannels, firstState, receiving, rest⟩ :=
      neverEscapes_bind_escape _ _ lookupState final address carriers receivingSafe rest
    have receivingPrefix := CallArgumentPrefix.actual initial lookupState firstState id implementation firstChannels
      lookup (Bool.eq_false_iff.mpr arity) receiving
    cases argumentsDone : evalArguments fuel config environment implementation.vars implementation.params.toList arguments firstState with
    | stop reason after | jump target kind after => simp only [bind, argumentsDone] at rest; cases rest
    | escape target payload after =>
        simp only [bind, argumentsDone] at rest
        cases rest
        exact Or.inl ⟨id, implementation, firstChannels, firstState, receivingPrefix, argumentsDone⟩
    | ok values argumentState =>
        simp only [bind, argumentsDone] at rest
        have renewalSafe : ProducerNeverEscapes ((firstChannels.mapM fun channel => match channel with
          | .register ty => pure (Channel.register ty)
          | .construct destination => do
              pure (.construct (← liftConstruction origin (renewReceivingDestination destination)))
          | .completion _ => fault .flow) : EvalM (List Channel)) := by
          producer_never_escapes_base
        obtain ⟨renewed, ready, renewal, rest⟩ :=
          neverEscapes_bind_escape _ _ argumentState final address carriers renewalSafe rest
        simp only [EvalM.get, bind] at rest
        split at rest
        · simp only [timeout, EvalM.stop] at rest; cases rest
        · rename_i depth
          simp only [freshAct, EvalM.get, EvalM.set, bind, pure] at rest
          let activation : RuntimeActivation := ⟨id, ready.nextAct, implementation.vars, [], renewed⟩
          let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
          let entered : ExecutionState := { ready with nextAct := ready.nextAct + 1, activations := activation :: ready.activations }
          have actual := CallActivationPrefix.actual initial firstState argumentState ready id implementation firstChannels
            renewed values receivingPrefix argumentsDone renewal (Nat.lt_of_not_ge depth)
          change (enterActivation fuel config activation pre implementation.body origin >>= fun returned =>
            deliverCarriers fuel config.layout channels returned origin) entered = .escape address carriers final at rest
          cases enteredResult : enterActivation fuel config activation pre implementation.body origin entered with
          | stop reason after | jump target kind after => simp only [bind, enteredResult] at rest; cases rest
          | escape target payload after =>
              simp only [bind, enteredResult] at rest
              cases rest
              exact Or.inr ⟨activation, pre, implementation.body, entered, actual, enteredResult⟩
          | ok returned after =>
              simp only [bind, enteredResult] at rest
              exact False.elim (neverEscapes_deliverCarriers fuel config.layout channels returned origin _ _ _ _ rest)

#print axioms callInvocation_escape_inv
end Goose.Proofs.ExitExecution
