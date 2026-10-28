import Goose.Proofs.ConstructionExitComputedCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

def OperandTerminal : ExecutionStep (List Carrier) → Prop
  | .ok .. => False
  | _ => True

theorem checked_numeric_terminal_suffix (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config source.initialized state ambient types live regions pending)
    (frame : AcceptedFrame config accepted source state types) (history : EvaluationHistoryCoverage state ambient pending)
    (extraChannels : List Channel) (extraExpressions : List Expr) :
    ∀ (fuel : Nat) (items : List (CheckedNumericOperand source)),
      let prefixChannels := items.map (fun operand => Channel.register operand.ty)
      let prefixExpressions := items.map CheckedNumericOperand.expression
      let outcome := evalOperands fuel config source.interpretation.environment prefixChannels prefixExpressions state
      OperandTerminal outcome →
      evalOperands fuel config source.interpretation.environment (prefixChannels ++ extraChannels)
        (prefixExpressions ++ extraExpressions) state = outcome := by
  intro fuel
  induction fuel with
  | zero =>
    intro items
    dsimp only
    intro terminal
    simp only [evalOperands, timeout, EvalM.stop]
  | succ fuel ih =>
    intro items
    dsimp only
    intro terminal
    cases items with
    | nil =>
      simp only [List.map_nil, evalOperands, pure, OperandTerminal] at terminal
    | cons first rest =>
      cases fuel with
      | zero =>
        simp only [List.map_cons, List.cons_append, evalOperands, evalProduce, timeout, EvalM.stop, bind]
      | succ n =>
        have head := accepted_numeric_register_outcomes first.form n config accepted source state ambient types live regions pending
          world frame history first.ty first.roots first.typingAfter first.rootsAfter first.checked
        let action := evalProduce (n + 1) config source.interpretation.environment [.register first.ty] first.expression
        cases result : action state with
        | stop reason final | escape target carried final | jump target kind final =>
          dsimp only [action] at result
          simp only [List.map_cons, List.cons_append, evalOperands, result, bind]
        | ok headCarriers final =>
          dsimp only [action] at result
          obtain ⟨value, headEq, finalEq, _, _, _, _⟩ := head.2.2.2.2 headCarriers final result
          subst headCarriers
          subst final
          simp only [List.map_cons, evalOperands, result, singleCarrier, bind, pure] at terminal
          cases tail : evalOperands (n + 1) config source.interpretation.environment
              (rest.map (fun operand => Channel.register operand.ty)) (rest.map CheckedNumericOperand.expression) state with
          | ok restCarriers final =>
            simp only [tail, bind, pure, OperandTerminal] at terminal
          | stop reason final | escape target carried final | jump target kind final =>
            have tailTerminal : OperandTerminal (evalOperands (n + 1) config source.interpretation.environment
                (rest.map (fun operand => Channel.register operand.ty)) (rest.map CheckedNumericOperand.expression) state) := by
              simp only [tail, OperandTerminal]
            have mixed := ih rest tailTerminal
            simp only [tail] at mixed
            simp only [List.map_cons, List.cons_append, evalOperands, result, singleCarrier, bind, pure, mixed, tail]

theorem checked_numeric_stop_completion_cleanup (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (origin : OriginId) (operands : List (CheckedNumericOperand source)) (extraExpressions : List Expr)
    (reason : Goose.Core.Stop)
    (world : AcceptedWorld config source.initialized before ambient types live regions pending)
    (frame : AcceptedFrame config accepted source before types) (history : EvaluationHistoryCoverage before ambient pending) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    let cleaned := { waited with construction := { waited.construction with
      exitReservations := waited.construction.exitReservations.set! token .released } }
    let prefixTypes := operands.map CheckedNumericOperand.ty
    let prefixExpressions := operands.map CheckedNumericOperand.expression
    ∀ final, evalOperands fuel config source.interpretation.environment (prefixTypes.map Channel.register) prefixExpressions waited =
      .stop reason final →
    withCompletionChannels (prefixTypes.map Channel.register ++ [.construct id]) origin
      (fun channels => evalOperands fuel config source.interpretation.environment channels (prefixExpressions ++ extraExpressions)) before =
      .stop reason cleaned ∧ EvaluationHistoryLifecycle cleaned ambient pending := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  let cleaned := { waited with construction := { waited.construction with
    exitReservations := waited.construction.exitReservations.set! token .released } }
  let prefixTypes := operands.map CheckedNumericOperand.ty
  let prefixExpressions := operands.map CheckedNumericOperand.expression
  let planned := prefixTypes.map (fun ty => (Channel.register ty, none)) ++ [(.completion token, some token)]
  dsimp only
  intro final stopped
  have unchanged := checked_numeric_operands_after_wait fuel config accepted source before ambient types live regions pending
    id operands world frame history
  have sameState : Goose.Proofs.Exit.stepState (evalOperands fuel config source.interpretation.environment
      (prefixTypes.map Channel.register) prefixExpressions waited) = waited := by
    simpa only [prefixTypes, prefixExpressions, List.map_map, Function.comp_def] using unchanged.2.2.1
  change evalOperands fuel config source.interpretation.environment (prefixTypes.map Channel.register)
    prefixExpressions waited = .stop reason final at stopped
  have finalEq : final = waited := by
    simpa only [stopped, Goose.Proofs.Exit.stepState] using sameState
  subst final
  have waitedWorld := (waitExitDestination_acceptedWorld config source.initialized before ambient types live regions pending id world history.1).2
  have waitedFrame := (acceptedFrame_waitExitDestination id frame).2
  have bounded := (wait_completion_references_bounded before.construction ambient id [] [] history.1).2
  have coverage : EvaluationHistoryCoverage waited (.completionChannels [token] [] [] :: ambient) pending := by
    refine ⟨bounded, ?_⟩
    intro old member
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
    exact history.2 old member
  have prefixStop : evalOperands fuel config source.interpretation.environment
      (operands.map (fun operand => Channel.register operand.ty)) prefixExpressions waited = .stop reason waited := by
    simpa only [prefixTypes, List.map_map, Function.comp_def] using stopped
  have terminal : OperandTerminal (evalOperands fuel config source.interpretation.environment
      (operands.map (fun operand => Channel.register operand.ty)) prefixExpressions waited) := by
    rw [prefixStop]
    trivial
  have propagation := checked_numeric_terminal_suffix config accepted source waited (.completionChannels [token] [] [] :: ambient)
    types live regions pending waitedWorld waitedFrame coverage [.completion token] extraExpressions fuel operands terminal
  have planChannels : planned.map Prod.fst = prefixTypes.map Channel.register ++ [.completion token] := by
    simp [planned, List.map_map, Function.comp_def]
  have mixedStop : evalOperands fuel config source.interpretation.environment (planned.map Prod.fst)
      (prefixExpressions ++ extraExpressions) waited = .stop reason waited := by
    simpa only [planChannels, prefixTypes, prefixExpressions, List.map_map, Function.comp_def, prefixStop] using propagation
  have setup := register_completion_preparation prefixTypes id origin before
  have action := withCompletionChannels_after_stop (prefixTypes.map Channel.register ++ [.construct id]) origin
    (fun channels => evalOperands fuel config source.interpretation.environment channels (prefixExpressions ++ extraExpressions))
    before waited waited planned reason setup mixedStop
  have ticket : waited.construction.exitReservations[token]? = some (.waiting id) := by simp [waited, token]
  have released := releaseExitReservation_waiting waited.construction token id ticket
  have noTokens : prefixTypes.filterMap (fun _ => (none : Option Nat)) = [] := by
    induction prefixTypes <;> simp_all
  have execution : withCompletionChannels (prefixTypes.map Channel.register ++ [.construct id]) origin
      (fun channels => evalOperands fuel config source.interpretation.environment channels (prefixExpressions ++ extraExpressions)) before =
      .stop reason cleaned := by
    rw [action]
    simp only [planned, List.filterMap_append, List.filterMap_map, Function.comp_def, List.filterMap_cons,
      List.filterMap_nil, noTokens, List.nil_append, finishBorrowedExitChannels, exitChannelCleanupBorrowed,
      Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil, List.forIn_cons, List.forIn_nil,
      liftConstruction, released, bind, pure]
    rfl
  have tracked := completion_operands_release_all_outcomes fuel config source.initialized source.interpretation.environment
    before ambient types live regions pending id (planned.map Prod.fst) (prefixExpressions ++ extraExpressions) origin world history
  have trackAfter := tracked.2
  change (match evalOperands fuel config source.interpretation.environment (planned.map Prod.fst)
      (prefixExpressions ++ extraExpressions) waited with
    | .ok carriers state | .escape _ carriers state | .jump _ (.breakValue carriers) state =>
        EvaluationHistoryLifecycle (Goose.Proofs.Exit.stepState (liftConstruction origin (releaseExitReservation token) state))
          (.returned carriers :: .completionChannels [token] [] [] :: ambient) (⟨planned.map Prod.fst, carriers⟩ :: pending)
    | .stop _ state | .jump _ .continueLoop state =>
        EvaluationHistoryLifecycle (Goose.Proofs.Exit.stepState (liftConstruction origin (releaseExitReservation token) state))
          (.completionChannels [token] [] [] :: ambient) pending) at trackAfter
  rw [mixedStop] at trackAfter
  have after : EvaluationHistoryLifecycle cleaned (.completionChannels [token] [] [] :: ambient) pending := by
    simpa only [liftConstruction, released, Goose.Proofs.Exit.stepState] using trackAfter
  exact ⟨execution, ⟨after.1, evaluationHistoryCoverage_pop cleaned ambient pending (.completionChannels [token] [] []) after.2⟩⟩

#print axioms checked_numeric_stop_completion_cleanup

#print axioms checked_numeric_terminal_suffix

end Goose.Proofs.ConstructionAcceptedExecution
