import Goose.Proofs.ConstructionExitEvaluationHistoryNumeric

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

structure CheckedNumericOperand (frame : ConstructionSourceFrame) where
  expression : Expr
  ty : Ty
  roots : List RootRef
  typingAfter : Nat
  rootsAfter : RState
  form : AcceptedNumericExpression expression
  checked : CheckedValue frame expression ty roots typingAfter rootsAfter

theorem register_channels_landing (types : List Ty) (carriers : List Carrier) (origin : Goose.Core.OriginId)
    (state : ExecutionState) (ready : CarriersLandingReady state (types.map Channel.register) carriers) :
    landCarriersInto origin (types.map Channel.register) carriers state = .ok () state := by
  induction types generalizing carriers with
  | nil =>
    cases carriers with
    | nil => simp [landCarriersInto, bind, pure]
    | cons carrier rest =>
      have lengths := ready.lengths
      simp at lengths
  | cons ty rest ih =>
    cases carriers with
    | nil =>
      have lengths := ready.lengths
      simp at lengths
    | cons carrier restCarriers =>
      have first : CarrierLandingReady state (.register ty) carrier := by
        apply ready.pairs
        simp
      have tailReady : CarriersLandingReady state (rest.map Channel.register) restCarriers := by
        refine ⟨?_, ?_⟩
        · simpa only [List.map_cons, List.length_cons, Nat.succ.injEq] using ready.lengths
        · intro channel item member
          apply ready.pairs
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
          exact Or.inr member
      cases carrier with
      | register value =>
        have tail := ih restCarriers tailReady
        simp only [landCarriersInto, List.map_cons, List.length_cons, List.zip_cons_cons, List.forIn_cons,
          bind, pure] at tail ⊢
        have length := tailReady.lengths
        simp only [length, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at tail ⊢
        exact tail
      | completed id => cases first
      | pendingNamed token => cases first

#print axioms register_channels_landing

theorem checked_numeric_operands (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (history : EvaluationHistoryCoverage state ambient pending) (operands : List (CheckedNumericOperand frame)) :
    let channels := operands.map (fun operand => Channel.register operand.ty)
    let expressions := operands.map CheckedNumericOperand.expression
    let outcome := evalOperands fuel config frame.interpretation.environment channels expressions state
    EvaluationHistoryLifecycleOutcome .carriers channels ambient pending outcome ∧
      Goose.Proofs.Exit.stepState outcome = state ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      ∀ carriers after, outcome = .ok carriers after → after = state ∧
        CarriersLandingReady after channels carriers ∧
        (∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier) ∧
        landCarriersInto 0 channels carriers after = .ok () after := by
  let channels := operands.map (fun operand => Channel.register operand.ty)
  let expressions := operands.map CheckedNumericOperand.expression
  have historyValid : EvaluationHistoryLifecycle state ambient pending := ⟨world.ownership.source.structural.1.1, history⟩
  have tracked := evaluator_history_outcome fuel config .carriers _
    (.operands frame.interpretation.environment channels expressions) state ambient pending channels historyValid
  have inductionResult : ∀ (fuel : Nat) (items : List (CheckedNumericOperand frame)),
      let channels := items.map (fun operand => Channel.register operand.ty)
      let expressions := items.map CheckedNumericOperand.expression
      let outcome := evalOperands fuel config frame.interpretation.environment channels expressions state
      Goose.Proofs.Exit.stepState outcome = state ∧
        ∀ carriers after, outcome = .ok carriers after → after = state ∧
          CarriersLandingReady after channels carriers ∧
          ∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier := by
    intro fuel
    induction fuel with
    | zero =>
      intro items
      simp only [evalOperands, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
      intro carriers after impossible
      cases impossible
    | succ fuel ih =>
      intro items
      cases items with
      | nil =>
        simp only [List.map_nil, evalOperands, pure, Goose.Proofs.Exit.stepState, true_and, ExecutionStep.ok.injEq]
        intro carriers after same
        obtain ⟨rfl, rfl⟩ := same
        exact ⟨rfl, ⟨rfl, by simp⟩, by simp⟩
      | cons first rest =>
        cases fuel with
        | zero =>
          simp only [List.map_cons, evalOperands, evalProduce, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState,
            reduceCtorEq, true_and]
          intro carriers after impossible
          cases impossible
        | succ n =>
          have head := accepted_numeric_register_outcomes first.form n config accepted frame state ambient types live regions pending
            world source history first.ty first.roots first.typingAfter first.rootsAfter first.checked
          have tail := ih rest
          let headAction := evalProduce (n + 1) config frame.interpretation.environment [.register first.ty] first.expression
          cases headResult : headAction state with
          | stop reason final | escape target carried final | jump target kind final =>
            dsimp only [headAction] at headResult
            have unchanged : final = state := by simpa only [headResult, Goose.Proofs.Exit.stepState] using head.2.1
            subst final
            simp only [List.map_cons, evalOperands, headResult, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
            intro carriers after impossible
            cases impossible
          | ok firstCarriers final =>
            dsimp only [headAction] at headResult
            obtain ⟨value, firstEq, finalEq, _, firstReady, firstBacked, _⟩ := head.2.2.2.2 firstCarriers final headResult
            subst final
            subst firstCarriers
            cases tailResult : evalOperands (n + 1) config frame.interpretation.environment
                (rest.map (fun operand => .register operand.ty)) (rest.map CheckedNumericOperand.expression) state with
            | stop reason final | escape target carried final | jump target kind final =>
              have unchanged : final = state := by simpa only [tailResult, Goose.Proofs.Exit.stepState] using tail.1
              subst final
              simp only [List.map_cons, evalOperands, headResult, singleCarrier, bind, pure, tailResult,
                Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
              intro carriers after impossible
              cases impossible
            | ok restCarriers final =>
              obtain ⟨finalEq, restReady, restBacked⟩ := tail.2 restCarriers final tailResult
              subst final
              simp only [List.map_cons, evalOperands, headResult, singleCarrier, bind, pure, tailResult,
                Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
              intro carriers after same
              obtain ⟨rfl, rfl⟩ := same
              refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
              · simp only [List.length_cons, List.length_map, restReady.lengths]
              · intro channel carrier member
                simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at member
                rcases member with same | member
                · obtain ⟨rfl, rfl⟩ := same
                  exact .register _ _
                · exact restReady.pairs channel carrier member
              · intro carrier member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact firstBacked _ (by simp)
                · exact restBacked carrier member
  have result := inductionResult fuel operands
  refine ⟨tracked, result.1, ?_, ?_, ?_⟩
  · simpa only [result.1] using world
  · simpa only [result.1] using source
  · intro carriers after success
    obtain ⟨same, ready, backed⟩ := result.2 carriers after success
    refine ⟨same, ready, backed, ?_⟩
    simpa only [List.map_map, Function.comp_def] using
      register_channels_landing (operands.map CheckedNumericOperand.ty) carriers 0 after (by simpa only [channels, List.map_map, Function.comp_def] using ready)

#print axioms checked_numeric_operands

end Goose.Proofs.ConstructionAcceptedExecution
