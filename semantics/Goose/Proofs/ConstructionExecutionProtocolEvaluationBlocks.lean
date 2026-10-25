import Goose.Proofs.ConstructionExecutionProtocolEvaluationContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

theorem execBlock_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    (PreservesConstructionInvariant predicate) (execBlock (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execBlock]
  protocol_eval previous

theorem execResultBlockWith_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    (PreservesConstructionInvariant predicate) (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execResultBlockWith, execResultScope]
  protocol_eval previous

theorem execActivationBody_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesConstructionInvariant predicate (execActivationBody (fuel + 1) config environment pre body) := by
  cases body
  simp only [execActivationBody, execResultScope]
  protocol_eval previous

theorem invokeCall_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply preservesConstructionInvariant_bind
  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getImplementation config context)
  · intro implementation
    rcases implementation with ⟨id, implementation⟩
    split
    · protocol_eval previous
    · apply preservesConstructionInvariant_bind
      · protocol_eval previous
      · intro callableChannels
        apply preservesConstructionInvariant_bind
        · exact previous.arguments _ _ _ _
        · intro values
          apply preservesConstructionInvariant_bind
          · protocol_eval previous
          · intro renewedChannels
            apply preservesConstructionInvariant_bind
            · exact preservesConstructionInvariant_get
            · intro state
              split
              · protocol_eval previous
              · apply preservesConstructionInvariant_allocateActivation
                  (make := fun act => ⟨id, act, implementation.vars, [], renewedChannels⟩)
                  (action := fun activation => do
                    let carriers ← enterActivation fuel config activation
                      ((implementation.params.toList.zip values).map fun item => (item.1.var, item.2))
                      implementation.body origin
                    deliverCarriers fuel config.layout channels carriers origin)
                intro activation
                protocol_eval previous


end Goose.Proofs.ConstructionExecutionProtocol
