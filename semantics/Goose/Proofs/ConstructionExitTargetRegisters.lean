import Goose.Proofs.ConstructionExitEvaluationHistoryNumericOperands
import Goose.Proofs.ConstructionExitEscapeTargetChannels

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem exitChannels_registers (source target : RuntimeActivation) (origin : OriginId) (state : ExecutionState)
    (types : List Ty) (expressions : List Expr) (channels : target.channels = types.map Channel.register)
    (lengths : types.length = expressions.length) :
    exitChannels source target expressions origin state = .ok (types.map Channel.register) state := by
  have mapped : ∀ (types : List Ty) (expressions : List Expr), types.length = expressions.length →
      (((types.map Channel.register).zip expressions).mapM (fun pair => do
        let reserve := fun incoming => do
          let kind ← exitSource source incoming pair.2
          let (_, selected) ← liftConstruction origin (reserveExitDestination incoming kind)
          pure (Channel.construct selected)
        match pair.1 with
        | .register ty => pure (.register ty)
        | .construct incoming => reserve incoming
        | .completion token =>
            match (← EvalM.get).construction.exitReservations[token]? with
            | some (.waiting _) => pure (.completion token)
            | some (.active _ _ selected _) => reserve (← receivingDestination selected)
            | _ => fault .flow) : EvalM (List Channel)) state = .ok (types.map Channel.register) state := by
    intro types
    induction types with
    | nil =>
      intro expressions lengths
      cases expressions <;> simp_all [bind, pure]
    | cons ty rest ih =>
      intro expressions lengths
      cases expressions with
      | nil => simp at lengths
      | cons expression tail =>
        simp only [List.length_cons, Nat.succ.injEq] at lengths
        have next := ih tail lengths
        simp only [bind, pure] at next
        simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, bind, pure]
        rw [next]
  have result := mapped types expressions lengths
  simp only [exitChannels, channels, List.length_map, lengths, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact result

theorem materialize_register_carriers (origin : OriginId) (tokens : List Nat) (state : ExecutionState)
    (types : List Ty) (carriers : List Carrier) (ready : CarriersLandingReady state (types.map Channel.register) carriers) :
    materializeOwnedCarriers origin tokens carriers state = .ok carriers state := by
  induction types generalizing carriers with
  | nil =>
    cases carriers with
    | nil => simp [materializeOwnedCarriers, List.mapM_nil, pure]
    | cons carrier rest => have lengths := ready.lengths; simp at lengths
  | cons ty rest ih =>
    cases carriers with
    | nil => have lengths := ready.lengths; simp at lengths
    | cons carrier tail =>
      have first : CarrierLandingReady state (.register ty) carrier := ready.pairs _ _ (by simp)
      have remaining : CarriersLandingReady state (rest.map Channel.register) tail := by
        refine ⟨?_, ?_⟩
        · simpa only [List.map_cons, List.length_cons, Nat.succ.injEq] using ready.lengths
        · intro channel item member
          apply ready.pairs
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
          exact Or.inr member
      have next := ih tail remaining
      cases first with
      | register ty value =>
        simp only [materializeOwnedCarriers, List.mapM_cons, bind, pure] at next ⊢
        rw [next]

theorem checked_register_returnFrom (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (targetId : Nat) (target : RuntimeActivation) (origin : OriginId) (operands : List (CheckedNumericOperand source))
    (world : AcceptedWorld config source.initialized state ambient types live regions pending)
    (frame : AcceptedFrame config accepted source state types) (history : EvaluationHistoryCoverage state ambient pending)
    (selected : targetActivation config targetId state = .ok target state)
    (channels : target.channels = (operands.map CheckedNumericOperand.ty).map Channel.register) :
    let expressions := operands.map CheckedNumericOperand.expression
    let outcome := evalOperands fuel config source.interpretation.environment target.channels expressions state
    ∀ carriers after, outcome = .ok carriers after →
      execStmt (fuel + 1) config source.interpretation.environment (.returnFrom targetId expressions origin) state =
        .escape ⟨target.act, .nonlocal targetId⟩ carriers state ∧
      CarriersLandingReady state target.channels carriers ∧
      (∀ carrier ∈ carriers, CarrierResultBacking config.layout state carrier) ∧
      landCarriersInto origin target.channels carriers state = .ok () state ∧
      AcceptedWorld config source.initialized state ambient types live regions pending ∧
      EvaluationHistoryLifecycle state (.returned carriers :: ambient) (⟨target.channels, carriers⟩ :: pending) := by
  let expressions := operands.map CheckedNumericOperand.expression
  let resultTypes := operands.map CheckedNumericOperand.ty
  have checked := checked_numeric_operands fuel config accepted source state ambient types live regions pending world frame history operands
  dsimp only
  intro carriers after success
  have successMapped : evalOperands fuel config source.interpretation.environment
      (operands.map (fun operand => Channel.register operand.ty)) expressions state = .ok carriers after := by
    simpa only [channels, resultTypes, expressions, List.map_map, Function.comp_def] using success
  obtain ⟨same, ready, backed, _⟩ := checked.2.2.2.2 carriers after successMapped
  subst after
  have targetReady : CarriersLandingReady state target.channels carriers := by
    simpa only [channels, resultTypes, List.map_map, Function.comp_def] using ready
  have setup := exitChannels_registers source.interpretation.environment target origin state resultTypes expressions channels (by simp [resultTypes, expressions])
  have borrowed : borrowedExitChannelReceipts target state = [] := by
    simp only [borrowedExitChannelReceipts, channels, List.filterMap_map, Function.comp_def]
    induction resultTypes <;> simp_all
  have materialized := materialize_register_carriers origin [] state resultTypes carriers (by
    simpa only [resultTypes, List.map_map, Function.comp_def] using ready)
  have complete : withExitChannels source.interpretation.environment target expressions origin
      (fun channels => evalOperands fuel config source.interpretation.environment channels expressions) state = .ok carriers state := by
    rw [withExitChannels_decomposition, setup]
    simp only [successMapped, resultTypes, List.map_map, Function.comp_def, exitChannelReservationTokens,
      Nat.sub_self, List.range_zero, List.map_nil, materialized, borrowed, finishBorrowedExitChannels,
      exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_nil, List.forIn_nil, bind, pure]
  have returned : execStmt (fuel + 1) config source.interpretation.environment (.returnFrom targetId expressions origin) state =
      .escape ⟨target.act, .nonlocal targetId⟩ carriers state := by
    simp only [execStmt, bind, selected, complete, Goose.Construct.escaped]
  refine ⟨returned, targetReady, backed, ?_, world, ?_⟩
  · simpa only [channels] using register_channels_landing resultTypes carriers origin state (by simpa only [channels] using targetReady)
  · exact evaluationHistoryLifecycle_returned state ambient pending target.channels carriers ⟨world.ownership.source.structural.1.1, history⟩

theorem checked_register_returnFrom_all_outcomes (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (targetId : Nat) (target : RuntimeActivation) (origin : OriginId) (operands : List (CheckedNumericOperand source))
    (world : AcceptedWorld config source.initialized state ambient types live regions pending)
    (frame : AcceptedFrame config accepted source state types) (history : EvaluationHistoryCoverage state ambient pending)
    (selected : targetActivation config targetId state = .ok target state)
    (channels : target.channels = (operands.map CheckedNumericOperand.ty).map Channel.register) :
    let expressions := operands.map CheckedNumericOperand.expression
    let outcome := evalOperands fuel config source.interpretation.environment target.channels expressions state
    let result := execStmt (fuel + 1) config source.interpretation.environment (.returnFrom targetId expressions origin) state
    result = (match outcome with
      | .ok carriers final => .escape ⟨target.act, .nonlocal targetId⟩ carriers final
      | .stop reason final => .stop reason final
      | .escape address carriers final => .escape address carriers final
      | .jump target kind final => .jump target kind final) ∧
    Goose.Proofs.Exit.stepState result = state ∧
    AcceptedWorld config source.initialized (Goose.Proofs.Exit.stepState result) ambient types live regions pending ∧
    (∀ carriers final, outcome = .ok carriers final →
      CarriersLandingReady final target.channels carriers ∧
      (∀ carrier ∈ carriers, CarrierResultBacking config.layout final carrier) ∧
      landCarriersInto origin target.channels carriers final = .ok () final) := by
  let expressions := operands.map CheckedNumericOperand.expression
  let resultTypes := operands.map CheckedNumericOperand.ty
  let action := evalOperands fuel config source.interpretation.environment target.channels expressions
  have checked := checked_numeric_operands fuel config accepted source state ambient types live regions pending world frame history operands
  have sameState : Goose.Proofs.Exit.stepState (action state) = state := by
    simpa only [action, channels, resultTypes, expressions, List.map_map, Function.comp_def] using checked.2.1
  have setup := exitChannels_registers source.interpretation.environment target origin state resultTypes expressions channels (by simp [resultTypes, expressions])
  have borrowed : borrowedExitChannelReceipts target state = [] := by
    simp only [borrowedExitChannelReceipts, channels, List.filterMap_map, Function.comp_def]
    induction resultTypes <;> simp_all
  have execution : execStmt (fuel + 1) config source.interpretation.environment (.returnFrom targetId expressions origin) state =
      (match action state with
      | .ok carriers final => .escape ⟨target.act, .nonlocal targetId⟩ carriers final
      | .stop reason final => .stop reason final
      | .escape address carriers final => .escape address carriers final
      | .jump target kind final => .jump target kind final) := by
    cases outcome : action state with
    | ok carriers final =>
      have successful := checked_register_returnFrom fuel config accepted source state ambient types live regions pending
        targetId target origin operands world frame history selected channels
      have result := successful carriers final (by simpa only [action, expressions] using outcome)
      have finalEq : final = state := by simpa only [outcome, Goose.Proofs.Exit.stepState] using sameState
      subst final
      simpa only [outcome, expressions] using result.1
    | stop reason final | escape address carriers final | jump target kind final =>
      have finalEq : final = state := by simpa only [outcome, Goose.Proofs.Exit.stepState] using sameState
      subst final
      dsimp only [action] at outcome
      rw [channels] at outcome
      change evalOperands fuel config source.interpretation.environment (resultTypes.map Channel.register) expressions state = _ at outcome
      simp only [execStmt, selected, bind, withExitChannels_decomposition, setup, outcome,
        exitChannelReservationTokens, Nat.sub_self, List.range_zero, List.map_nil, borrowed,
        finishBorrowedExitChannels, exitChannelCleanupBorrowed, List.reverse_nil, List.forIn_nil,
        Bool.false_eq_true, ↓reduceIte, pure]
  have resultState : Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config source.interpretation.environment
      (.returnFrom targetId expressions origin) state) = state := by
    rw [execution]
    cases outcome : action state <;> simp only [outcome, Goose.Proofs.Exit.stepState] at sameState ⊢ <;> exact sameState
  dsimp only
  refine ⟨execution, resultState, ?_, ?_⟩
  · change AcceptedWorld config source.initialized (Goose.Proofs.Exit.stepState
      (execStmt (fuel + 1) config source.interpretation.environment (.returnFrom targetId expressions origin) state))
      ambient types live regions pending
    rw [resultState]
    exact world
  · intro carriers final success
    have result := checked_register_returnFrom fuel config accepted source state ambient types live regions pending
      targetId target origin operands world frame history selected channels carriers final success
    have finalEq : final = state := by
      have actionSuccess : action state = .ok carriers final := success
      simpa only [actionSuccess, Goose.Proofs.Exit.stepState] using sameState
    subst final
    exact ⟨result.2.1, result.2.2.1, result.2.2.2.1⟩

#print axioms checked_register_returnFrom_all_outcomes

#print axioms checked_register_returnFrom

end Goose.Proofs.ConstructionAcceptedExecution
