import Goose.Proofs.ConstructionExitWaitingWorld
import Goose.Proofs.ConstructionExitEvaluationHistoryMixedCompletion

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem register_prefix_completion_ready (before after : ExecutionState) (types : List Ty)
    (carriers : List Carrier) (token id : Nat)
    (prefixReady : CarriersLandingReady before (types.map Channel.register) carriers)
    (completionReady : CarrierLandingReady after (.completion token) (.completed id)) :
    CarriersLandingReady after (types.map Channel.register ++ [.completion token]) (carriers ++ [.completed id]) := by
  induction types generalizing carriers with
  | nil =>
    cases carriers with
    | nil =>
      refine ⟨rfl, ?_⟩
      intro channel carrier member
      simp only [List.map_nil, List.nil_append, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      exact completionReady
    | cons carrier rest =>
      have lengths := prefixReady.lengths
      simp at lengths
  | cons ty rest ih =>
    cases carriers with
    | nil =>
      have lengths := prefixReady.lengths
      simp at lengths
    | cons carrier tail =>
      have first : CarrierLandingReady before (.register ty) carrier := prefixReady.pairs _ _ (by simp)
      have restReady : CarriersLandingReady before (rest.map Channel.register) tail := by
        refine ⟨?_, ?_⟩
        · simpa only [List.map_cons, List.length_cons, Nat.succ.injEq] using prefixReady.lengths
        · intro channel item member
          apply prefixReady.pairs
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
          exact Or.inr member
      have mixed := ih tail restReady
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.cons_append, List.length_cons, Nat.succ.injEq]
        exact mixed.lengths
      · intro channel item member
        simp only [List.map_cons, List.cons_append, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at member
        rcases member with equal | prior
        · obtain ⟨rfl, rfl⟩ := equal
          cases first with
          | register ty value => exact .register ty value
        · exact mixed.pairs channel item prior

theorem register_prefix_completion_landing (before after : ExecutionState) (types : List Ty)
    (carriers : List Carrier) (token id : Nat) (origin : OriginId)
    (prefixReady : CarriersLandingReady before (types.map Channel.register) carriers)
    (completionLanding : landCarriersInto origin [.completion token] [.completed id] after = .ok () after) :
    landCarriersInto origin (types.map Channel.register ++ [.completion token]) (carriers ++ [.completed id]) after =
      .ok () after := by
  induction types generalizing carriers with
  | nil =>
    cases carriers with
    | nil => simpa using completionLanding
    | cons carrier rest =>
      have lengths := prefixReady.lengths
      simp at lengths
  | cons ty rest ih =>
    cases carriers with
    | nil =>
      have lengths := prefixReady.lengths
      simp at lengths
    | cons carrier tail =>
      have first : CarrierLandingReady before (.register ty) carrier := prefixReady.pairs _ _ (by simp)
      have restReady : CarriersLandingReady before (rest.map Channel.register) tail := by
        refine ⟨?_, ?_⟩
        · simpa only [List.map_cons, List.length_cons, Nat.succ.injEq] using prefixReady.lengths
        · intro channel item member
          apply prefixReady.pairs
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
          exact Or.inr member
      have next := ih tail restReady
      cases first with
      | register ty value =>
        simp only [landCarriersInto, List.map_cons, List.cons_append, List.length_cons,
          List.zip_cons_cons, List.forIn_cons, bind, pure] at next ⊢
        have lengths := restReady.lengths
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, lengths,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at next ⊢
        exact next

#print axioms register_prefix_completion_landing

#print axioms register_prefix_completion_ready

theorem numeric_scalar_completion_execution (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
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
    let channels := operands.map (fun operand => Channel.register operand.ty)
    let expressions := operands.map CheckedNumericOperand.expression
    ∃ after,
      EvaluationHistoryLifecycleOutcome .carriers (channels ++ [.completion token])
        (.completionChannels [token] [] [] :: ambient) pending
        (evalOperands (fuel + operands.length + 5) config source.interpretation.environment
          (channels ++ [.completion token]) (expressions ++ [.bytes (.varr (.int .u8)) bytes origin]) waited) ∧
      ∀ carriers,
      evalOperands (fuel + operands.length + 5) config source.interpretation.environment channels expressions waited =
        .ok carriers waited →
      evalOperands (fuel + operands.length + 5) config source.interpretation.environment
        (channels ++ [.completion token]) (expressions ++ [.bytes (.varr (.int .u8)) bytes origin]) waited =
        .ok (carriers ++ [.completed id]) after ∧
      CarriersLandingReady after (channels ++ [.completion token]) (carriers ++ [.completed id]) ∧
      (∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier) ∧
      CarrierResultBacking config.layout after (.completed id) ∧
      CarrierLandingReady after (.completion token) (.completed id) ∧
      landCarriersInto origin (channels ++ [.completion token]) (carriers ++ [.completed id]) after = .ok () after := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  have waitedWorld := (waitExitDestination_acceptedWorld config source.initialized before ambient types live regions pending id world history.1).2
  have waitedFrame := (acceptedFrame_waitExitDestination id frame).2
  have waitHistory := wait_completion_references_bounded before.construction ambient id [] [] history.1
  have coverage : EvaluationHistoryCoverage waited (.completionChannels [token] [] [] :: ambient) pending := by
    refine ⟨waitHistory.2, ?_⟩
    intro old member
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
    exact history.2 old member
  obtain ⟨after, _, byteProduce, _, byteReady, byteBacking, byteLanding⟩ :=
    completion_byte_receiver_history (fuel + 2) config source.initialized source.interpretation.environment before ambient
      types live regions pending id bytes origin world history ready receiver packed adaptation request current fits
  change evalProduce (fuel + 4) config source.interpretation.environment [.completion token]
    (.bytes (.varr (.int .u8)) bytes origin) waited = .ok [.completed id] after at byteProduce
  have execution : ∀ (items : List (CheckedNumericOperand source)) (carriers : List Carrier),
      evalOperands (fuel + items.length + 5) config source.interpretation.environment
        (items.map (fun operand => Channel.register operand.ty)) (items.map CheckedNumericOperand.expression) waited =
        .ok carriers waited →
      evalOperands (fuel + items.length + 5) config source.interpretation.environment
        (items.map (fun operand => Channel.register operand.ty) ++ [.completion token])
        (items.map CheckedNumericOperand.expression ++ [.bytes (.varr (.int .u8)) bytes origin]) waited =
        .ok (carriers ++ [.completed id]) after ∧
      ((∀ operand ∈ items, (∃ ty, operand.ty = .int ty) ∨ operand.ty = .bool) →
      ∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier) := by
    intro items
    induction items with
    | nil =>
      intro carriers prefixResult
      simp only [List.map_nil, List.length_nil, Nat.add_zero, evalOperands, pure, ExecutionStep.ok.injEq] at prefixResult
      obtain ⟨rfl, _⟩ := prefixResult
      refine ⟨?_, ?_⟩
      · simp only [List.map_nil, List.nil_append, List.length_nil, Nat.add_zero, evalOperands, byteProduce, singleCarrier, bind, pure]
      · intro _ carrier member
        cases member
    | cons first rest ih =>
      intro carriers prefixResult
      have head := accepted_numeric_register_outcomes first.form (fuel + rest.length + 4) config accepted source waited
        (.completionChannels [token] [] [] :: ambient) types live regions pending waitedWorld waitedFrame coverage
        first.ty first.roots first.typingAfter first.rootsAfter first.checked
      let action := evalProduce (fuel + rest.length + 5) config source.interpretation.environment [.register first.ty] first.expression
      have tailFuel : fuel + (rest.length + 1) + 5 = (fuel + rest.length + 5) + 1 := by omega
      cases result : action waited with
      | stop reason final | escape target carried final | jump target kind final =>
        dsimp only [action] at result
        simp only [List.map_cons, List.length_cons, tailFuel, evalOperands, result, bind] at prefixResult
        cases prefixResult
      | ok headCarriers final =>
        dsimp only [action] at result
        obtain ⟨value, headEq, finalEq, acceptedValue, _, _, _⟩ := head.2.2.2.2 headCarriers final result
        subst headCarriers
        subst final
        simp only [List.map_cons, List.length_cons, tailFuel, evalOperands, result, singleCarrier, bind, pure] at prefixResult
        cases tail : evalOperands (fuel + rest.length + 5) config source.interpretation.environment
            (rest.map (fun operand => Channel.register operand.ty)) (rest.map CheckedNumericOperand.expression) waited with
        | stop reason final | escape target carried final | jump target kind final =>
          simp only [tail, bind] at prefixResult
          cases prefixResult
        | ok restCarriers final =>
          simp only [tail, bind, pure, ExecutionStep.ok.injEq] at prefixResult
          obtain ⟨rfl, rfl⟩ := prefixResult
          have mixed := ih restCarriers tail
          refine ⟨?_, ?_⟩
          · simp only [List.map_cons, List.cons_append, List.length_cons, tailFuel, evalOperands,
              result, singleCarrier, bind, pure, mixed.1, List.cons_append]
          · intro scalarItems carrier member
            simp only [List.mem_cons] at member
            rcases member with same | member
            · subst carrier
              have scalarHead := scalarItems first (by simp)
              have represented := acceptedValue.represented
              rcases scalarHead with ⟨ty, same⟩ | same
              · rw [same] at represented
                cases represented with
                | integer ty value => exact .register _ (.integer ty value)
                | stored ty value nonfixed logical => cases nonfixed
              · rw [same] at represented
                cases represented with
                | boolean value => exact .register _ (.boolean value)
                | stored ty value nonfixed logical => cases nonfixed
            · exact mixed.2 (fun operand found => scalarItems operand (by simp [found])) carrier member
  have allOutcomes := completion_mixed_operands_all_outcomes (fuel + operands.length + 5) config source.initialized
    source.interpretation.environment before ambient types live regions pending id
    (operands.map (fun operand => Channel.register operand.ty) ++ [.completion token])
    (operands.map CheckedNumericOperand.expression ++ [.bytes (.varr (.int .u8)) bytes origin]) world history
  refine ⟨after, allOutcomes.2, ?_⟩
  intro carriers prefixResult
  have result := execution operands carriers prefixResult
  have prefixFacts := checked_numeric_operands (fuel + operands.length + 5) config accepted source waited
    (.completionChannels [token] [] [] :: ambient) types live regions pending waitedWorld waitedFrame coverage operands
  obtain ⟨_, prefixReady, _, _⟩ := prefixFacts.2.2.2.2 carriers waited prefixResult
  have readyAll := register_prefix_completion_ready waited after (operands.map CheckedNumericOperand.ty) carriers token id
    (by simpa only [List.map_map, Function.comp_def] using prefixReady) (byteReady.pairs _ _ (by simp [token]))
  refine ⟨result.1, ?_, result.2 scalar, byteBacking _ (by simp), byteReady.pairs _ _ (by simp [token]), ?_⟩
  · simpa only [List.map_map, Function.comp_def] using readyAll
  · have landed := register_prefix_completion_landing waited after (operands.map CheckedNumericOperand.ty) carriers token id origin
      (by simpa only [List.map_map, Function.comp_def] using prefixReady) (by simpa only [token] using byteLanding)
    simpa only [List.map_map, Function.comp_def] using landed

#print axioms numeric_scalar_completion_execution

end Goose.Proofs.ConstructionAcceptedExecution
