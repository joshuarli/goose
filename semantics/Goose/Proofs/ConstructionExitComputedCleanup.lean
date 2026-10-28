import Goose.Proofs.ConstructionExitComputedScalarBacking
import Goose.Proofs.ExitExecutionPathCompletion
import Goose.Proofs.ConstructionExitCompletionSetup
import Goose.Proofs.ConstructionExitFrameRelease
import Goose.Proofs.ConstructionExitEvaluationHistoryMixedCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem register_completion_preparation (types : List Ty) (id : Nat) (origin : OriginId) (before : ExecutionState) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    CompletionPreparation (types.map Channel.register ++ [.construct id]) origin before
      (types.map (fun ty => (Channel.register ty, none)) ++ [(.completion token, some token)]) waited := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  have wait : waitExitDestination id before.construction = .ok token waited.construction := by
    simp [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure, token, waited]
  induction types with
  | nil =>
    simp only [List.map_nil, List.nil_append, CompletionPreparation, List.mapM_cons, List.mapM_nil,
      liftConstruction, wait, bind, pure]
    rfl
  | cons ty rest ih =>
    simp only [List.map_cons, List.cons_append, CompletionPreparation, List.mapM_cons, bind, pure] at ih ⊢
    rw [ih]

theorem materialize_registers_completed (before after : ExecutionState) (types : List Ty)
    (carriers : List Carrier) (id : Nat) (origin : OriginId) (tokens : List Nat)
    (ready : CarriersLandingReady before (types.map Channel.register) carriers) :
    materializeOwnedCarriers origin tokens (carriers ++ [.completed id]) after =
      .ok (carriers ++ [.completed id]) after := by
  induction types generalizing carriers with
  | nil =>
    cases carriers with
    | nil => simp [materializeOwnedCarriers, List.mapM_cons, List.mapM_nil, bind, pure]
    | cons carrier rest =>
      have lengths := ready.lengths
      simp at lengths
  | cons ty rest ih =>
    cases carriers with
    | nil =>
      have lengths := ready.lengths
      simp at lengths
    | cons carrier tail =>
      have first : CarrierLandingReady before (.register ty) carrier := ready.pairs _ _ (by simp)
      have tailReady : CarriersLandingReady before (rest.map Channel.register) tail := by
        refine ⟨?_, ?_⟩
        · simpa only [List.map_cons, List.length_cons, Nat.succ.injEq] using ready.lengths
        · intro channel item member
          apply ready.pairs
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
          exact Or.inr member
      have next := ih tail tailReady
      cases first with
      | register ty value =>
        simp only [materializeOwnedCarriers, List.cons_append, List.mapM_cons, bind, pure] at next ⊢
        rw [next]

#print axioms materialize_registers_completed

theorem completion_channels_after_ok (channels : List Channel) (origin : OriginId)
    (action : List Channel → EvalM (List Carrier)) (initial prepared before : ExecutionState)
    (planned : List (Channel × Option Nat)) (carriers : List Carrier)
    (setup : CompletionPreparation channels origin initial planned prepared)
    (evaluated : action (planned.map Prod.fst) prepared = .ok carriers before)
    (materialized : materializeOwnedCarriers origin (planned.filterMap Prod.snd) carriers before = .ok carriers before) :
    withCompletionChannels channels origin action initial =
      finishBorrowedExitChannels origin [] (planned.filterMap Prod.snd) false carriers (.ok carriers) before := by
  unfold withCompletionChannels
  change (match ((do
    let items ← completionPlanAction channels origin
    pure (items.map Prod.fst, items.filterMap Prod.snd)) initial) with
    | .ok (items, tokens) state => _
    | .stop reason state => ExecutionStep.stop reason state
    | .escape address payload state => ExecutionStep.escape address payload state
    | .jump target kind state => ExecutionStep.jump target kind state) = _
  change completionPlanAction channels origin initial = .ok planned prepared at setup
  simp only [bind, setup, pure, evaluated, materialized, finishBorrowedExitChannels, exitChannelCleanupBorrowed,
    Bool.false_eq_true, ↓reduceIte, List.reverse_nil, List.forIn_nil]
  rfl

#print axioms completion_channels_after_ok

theorem mixed_completion_timeout_cleanup (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (id : Nat) (origin : OriginId)
    (prefixTypes : List Ty) (expressions : List Expr)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : EvaluationHistoryCoverage before ambient pending) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    let cleaned := { waited with construction := { waited.construction with
      exitReservations := waited.construction.exitReservations.set! token .released } }
    withCompletionChannels (prefixTypes.map Channel.register ++ [.construct id]) origin
      (fun channels => evalOperands 0 config environment channels expressions) before = .stop .timeout cleaned ∧
    EvaluationHistoryLifecycle cleaned ambient pending := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  let cleaned := { waited with construction := { waited.construction with
    exitReservations := waited.construction.exitReservations.set! token .released } }
  let planned := prefixTypes.map (fun ty => (Channel.register ty, none)) ++ [(.completion token, some token)]
  have setup := register_completion_preparation prefixTypes id origin before
  have stopped : evalOperands 0 config environment (planned.map Prod.fst) expressions waited = .stop .timeout waited := by
    simp [evalOperands, timeout, EvalM.stop]
  have action := withCompletionChannels_after_stop (prefixTypes.map Channel.register ++ [.construct id]) origin
    (fun channels => evalOperands 0 config environment channels expressions) before waited waited planned .timeout setup stopped
  have ticket : waited.construction.exitReservations[token]? = some (.waiting id) := by simp [waited, token]
  have released := releaseExitReservation_waiting waited.construction token id ticket
  have noTokens : prefixTypes.filterMap (fun _ => (none : Option Nat)) = [] := by
    induction prefixTypes <;> simp_all
  have execution : withCompletionChannels (prefixTypes.map Channel.register ++ [.construct id]) origin
      (fun channels => evalOperands 0 config environment channels expressions) before = .stop .timeout cleaned := by
    rw [action]
    simp only [planned, List.filterMap_append, List.filterMap_map, Function.comp_def, List.filterMap_cons,
      List.filterMap_nil, noTokens, List.map_nil, List.nil_append, finishBorrowedExitChannels, exitChannelCleanupBorrowed,
      Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons,
      List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  have tracked := completion_operands_release_all_outcomes 0 config initialized environment before ambient types live regions pending
    id (planned.map Prod.fst) expressions origin world history
  have trackAfter := tracked.2
  simp only [evalOperands, timeout, EvalM.stop] at trackAfter
  change EvaluationHistoryLifecycle (Goose.Proofs.Exit.stepState (liftConstruction origin (releaseExitReservation token) waited))
    (.completionChannels [token] [] [] :: ambient) pending at trackAfter
  have after : EvaluationHistoryLifecycle cleaned (.completionChannels [token] [] [] :: ambient) pending := by
    simpa only [evalOperands, timeout, EvalM.stop, liftConstruction, released, Goose.Proofs.Exit.stepState] using trackAfter
  exact ⟨execution, ⟨after.1, evaluationHistoryCoverage_pop cleaned ambient pending (.completionChannels [token] [] []) after.2⟩⟩

theorem mixed_scalar_completion_cleanup (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (bytes : List UInt8) (origin : OriginId) (operands : List (CheckedNumericOperand source))
    (world : AcceptedWorld config source.initialized before ambient types live regions pending)
    (frame : AcceptedFrame config accepted source before types) (history : EvaluationHistoryCoverage before ambient pending)
    (scalar : ∀ operand ∈ operands, (∃ ty, operand.ty = .int ty) ∨ operand.ty = .bool)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    let prefixTypes := operands.map CheckedNumericOperand.ty
    let expressions := operands.map CheckedNumericOperand.expression ++ [.bytes (.varr (.int .u8)) bytes origin]
    ∃ after : ExecutionState, ∀ carriers,
      evalOperands (fuel + operands.length + 5) config source.interpretation.environment
        (prefixTypes.map Channel.register) (operands.map CheckedNumericOperand.expression) waited = .ok carriers waited →
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! token .released } }
      withCompletionChannels (prefixTypes.map Channel.register ++ [.construct id]) origin
        (fun channels => evalOperands (fuel + operands.length + 5) config source.interpretation.environment channels expressions) before =
        .ok (carriers ++ [.completed id]) cleaned ∧
      EvaluationHistoryLifecycle cleaned
        (.returned (carriers ++ [.completed id]) :: .completionChannels [token] [] [] :: ambient)
        (⟨prefixTypes.map Channel.register ++ [.completion token], carriers ++ [.completed id]⟩ :: pending) := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  let prefixTypes := operands.map CheckedNumericOperand.ty
  let expressions := operands.map CheckedNumericOperand.expression ++ [.bytes (.varr (.int .u8)) bytes origin]
  let planned := prefixTypes.map (fun ty => (Channel.register ty, none)) ++ [(.completion token, some token)]
  obtain ⟨after, allOutcomes, success⟩ := numeric_scalar_completion_execution fuel config accepted source before ambient types
    live regions pending id bytes origin operands world frame history scalar ready receiver packed adaptation request current fits
  refine ⟨after, ?_⟩
  intro carriers prefixResult
  have prefixAction : evalOperands (fuel + operands.length + 5) config source.interpretation.environment
      (operands.map (fun operand => Channel.register operand.ty)) (operands.map CheckedNumericOperand.expression) waited =
      .ok carriers waited := by simpa only [prefixTypes, List.map_map, Function.comp_def] using prefixResult
  obtain ⟨evaluated, mixedReady, prefixBacking, byteBacking, byteReady, byteLanding⟩ := success carriers prefixAction
  have ticketReady : CarrierLandingReady after (.completion token) (.completed id) := byteReady
  cases ticketReady with
  | completion _ oldIncoming selected _ role snapshot ticket receiving =>
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    have released := releaseExitReservation_active after.construction token role oldIncoming selected snapshot ticket
    have setup := register_completion_preparation prefixTypes id origin before
    have plannedChannels : planned.map Prod.fst = prefixTypes.map Channel.register ++ [.completion token] := by
      simp [planned, List.map_map, Function.comp_def]
    have noTokens : prefixTypes.filterMap (fun _ => (none : Option Nat)) = [] := by
      induction prefixTypes <;> simp_all
    have plannedTokens : planned.filterMap Prod.snd = [token] := by
      simp only [planned, List.filterMap_append, List.filterMap_map, Function.comp_def, noTokens,
        List.nil_append, List.filterMap_cons, List.filterMap_nil]
    have evaluatedPlan : evalOperands (fuel + operands.length + 5) config source.interpretation.environment
        (planned.map Prod.fst) expressions waited = .ok (carriers ++ [.completed id]) after := by
      simpa only [plannedChannels, expressions, prefixTypes, List.map_map, Function.comp_def] using evaluated
    have prefixInfo := checked_numeric_operands_after_wait (fuel + operands.length + 5) config accepted source before ambient
      types live regions pending id operands world frame history
    obtain ⟨_, prefixReady, _, _⟩ := prefixInfo.2.2.2.2.2 carriers waited prefixAction
    have materialized : materializeOwnedCarriers origin (planned.filterMap Prod.snd)
        (carriers ++ [.completed id]) after = .ok (carriers ++ [.completed id]) after :=
      materialize_registers_completed waited after prefixTypes carriers id origin _ (by
        simpa only [prefixTypes, List.map_map, Function.comp_def] using prefixReady)
    have wrapper := completion_channels_after_ok (prefixTypes.map Channel.register ++ [.construct id]) origin
      (fun channels => evalOperands (fuel + operands.length + 5) config source.interpretation.environment channels expressions)
      before waited after planned (carriers ++ [.completed id]) setup evaluatedPlan materialized
    have execution : withCompletionChannels (prefixTypes.map Channel.register ++ [.construct id]) origin
        (fun channels => evalOperands (fuel + operands.length + 5) config source.interpretation.environment channels expressions) before =
        .ok (carriers ++ [.completed id]) cleaned := by
      rw [wrapper, plannedTokens]
      simp only [finishBorrowedExitChannels, exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
      rfl
    have beforeCleanup : EvaluationHistoryLifecycle after
        (.returned (carriers ++ [.completed id]) :: .completionChannels [token] [] [] :: ambient)
        (⟨prefixTypes.map Channel.register ++ [.completion token], carriers ++ [.completed id]⟩ :: pending) := by
      simpa only [evaluated, EvaluationHistoryLifecycleOutcome, OwnershipResultShape.retainedCarriers,
        prefixTypes, List.map_map, Function.comp_def] using allOutcomes
    have afterCleanup := evaluationHistoryLifecycle_release origin token _ _ after beforeCleanup
    refine ⟨execution, ?_⟩
    simpa only [liftConstruction, released, Goose.Proofs.Exit.stepState] using afterCleanup

#print axioms mixed_scalar_completion_cleanup

#print axioms mixed_completion_timeout_cleanup

#print axioms register_completion_preparation

end Goose.Proofs.ConstructionAcceptedExecution
