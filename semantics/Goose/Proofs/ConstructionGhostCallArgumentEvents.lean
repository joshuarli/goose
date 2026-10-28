import Goose.Proofs.ConstructionGhostCallSetupHistory
import Goose.Proofs.ConstructionGhostModuleResultEvents

namespace Goose.Proofs.ConstructionGhostCallArgumentEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostArguments

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem callAfterArguments_keepsEventPrefix (fuel : Nat) (config : EvalConfig) (id : Goose.Core.ImplId)
    (implementation : Impl) (channels callableChannels : List Channel) (origin : Goose.Core.OriginId)
    (values : List Value) : KeepsEventPrefix (callAfterArguments fuel config id implementation channels callableChannels origin values) := by
  intro state
  apply (eventPrefix_iff_isPrefix _ _).mpr
  have preserved : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
      (callAfterArguments fuel config id implementation channels callableChannels origin values) := by
    let previous := evaluation_preservesConstructionInvariant (predicate := PrefixInvariant state.construction.events) fuel config
    unfold callAfterArguments
    apply preservesConstructionInvariant_bind
    · protocol_eval previous
    · intro renewedChannels
      apply preservesConstructionInvariant_bind
      · exact preservesConstructionInvariant_get
      · intro current
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
  exact preserved state List.prefix_rfl

theorem argumentReplay_visitPrefix {config : EvalConfig} {environment : RuntimeActivation} {vars : Array LocalVar}
    {fuel offset : Nat} {parameters : List Param} {arguments : List Arg} {before : ExecutionState}
    {outcome : ExecutionStep (List Value)} {visits : List ArgumentInvocation}
    (replay : ArgumentReplay config environment vars fuel offset parameters arguments before outcome visits)
    (visit : ArgumentInvocation) (member : visit ∈ visits) :
    EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState outcome).construction.events := by
  induction replay with
  | timeout | done | arityLeft | arityRight => simp at member
  | @next fuel offset parameter parameters argument arguments before middle value outcome visits head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with same | later
      · subst visit
        have kept := (evaluation_keepsEventPrefix fuel config).arguments environment vars parameters arguments middle
        rw [tail.sound] at kept
        cases outcome <;> simpa [prependValue, Goose.Proofs.Exit.stepState] using kept
      · have kept := ih later
        cases outcome <;> simpa [prependValue, Goose.Proofs.Exit.stepState] using kept
  | stopped | escaped | jumped =>
      simp only [List.mem_singleton] at member
      subst visit
      exact eventPrefix_refl _

theorem callArgumentsContinuation_resultPrefix (fuel : Nat) (config : EvalConfig) (id : Goose.Core.ImplId)
    (implementation : Impl) (channels callableChannels : List Channel) (origin : Goose.Core.OriginId)
    (outcome : ExecutionStep (List Value)) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome)).construction.events := by
  cases outcome with
  | ok values state => exact callAfterArguments_keepsEventPrefix fuel config id implementation channels callableChannels origin values state
  | stop | escape | jump => exact eventPrefix_refl _

theorem invokeCall_argumentVisitPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before argumentsReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels : List Channel) (outcome : ExecutionStep (List Value)) (visits : List ArgumentInvocation)
    (visit : ArgumentInvocation)
    (replay : ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments argumentsReady outcome visits)
    (member : visit ∈ visits)
    (execution : invokeCall (fuel + 1) config environment context arguments channels origin before =
      callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome) :
    EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState (invokeCall (fuel + 1) config environment context arguments channels origin before)).construction.events := by
  rw [execution]
  exact eventPrefix_trans _ _ _ (argumentReplay_visitPrefix replay visit member)
    (callArgumentsContinuation_resultPrefix fuel config id implementation channels callableChannels origin outcome)

#print axioms invokeCall_argumentVisitPrefix
#print axioms callArgumentsContinuation_resultPrefix
#print axioms argumentReplay_visitPrefix
#print axioms callAfterArguments_keepsEventPrefix
end Goose.Proofs.ConstructionGhostCallArgumentEvents
