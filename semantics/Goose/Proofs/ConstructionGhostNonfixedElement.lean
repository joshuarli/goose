import Goose.Proofs.ConstructionGhostElements

namespace Goose.Proofs.ConstructionGhostNonfixedElement
open Goose.Construct
open Goose.Proofs.ConstructionGhostElements Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionInitializerLoopReplay

def childElementContinuation (origin : Goose.Core.OriginId) (parent child : Goose.Core.DestinationId)
    (source : ExecutionStep Unit) : ExecutionStep Unit :=
  match source with
  | .ok () state => (do
      let child ← completedReceivingDestination child
      receivingAction origin parent (fun parent => attachChild parent child)) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem nonfixedElement_source_execution (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (parent child : Goose.Core.DestinationId)
    (element : Ty) (operand : Expr) (before layoutReady childReady : ExecutionState)
    (layout : ReceivingLayout) (nonfixed : element.nonfixed = true)
    (layoutResult : receivingLayout config.layout element before = .ok layout layoutReady)
    (childResult : receivingAction (expressionOrigin operand) parent
      (fun current => openChild current element layout) layoutReady = .ok child childReady) :
    buildElement (fuel + 1) config environment parent element operand before =
      childElementContinuation (expressionOrigin operand) parent child
        (buildExpr fuel config environment child operand childReady) := by
  simp only [buildElement, nonfixed, ↓reduceIte, bind, layoutResult, childResult, childElementContinuation]
  cases buildExpr fuel config environment child operand childReady <;> rfl

theorem nestedArray_element_ghost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (parent child current : Goose.Core.DestinationId)
    (element innerElement ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId)
    (path : List Nat) (before layoutReady childReady prepared ready : ExecutionState)
    (layout : ReceivingLayout) (pending : PendingDestination)
    (nonfixed : element.nonfixed = true) (fixed : innerElement.nonfixed = false)
    (layoutResult : receivingLayout config.layout element before = .ok layout layoutReady)
    (childResult : receivingAction origin parent
      (fun current => openChild current element layout) layoutReady = .ok child childReady)
    (renewed : liftConstruction origin (renewReceivingDestination child) childReady = .ok current prepared)
    (found : getDestination current prepared = .ok pending ready)
    (elementTypeFound : elementType pending.capability.logicalType = some innerElement) :
    ∃ outcome visits,
      OperandReplay (fun operand => buildElement (fuel + 1) config environment current innerElement operand)
        0 operands [] ready outcome visits ∧
      (∀ visit ∈ visits, FixedElementTree config environment current innerElement (fuel + 1)
        (visit.path (path ++ [0])) visit.operand visit.before visit.outcome) ∧
      visits.map Invocation.operand = operands.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      buildElement (fuel + 3) config environment parent element (.arrLit ty operands origin) before =
        childElementContinuation origin parent child
          (protectDestination origin current (fun _ =>
            match discardValues outcome with
            | .ok _ state => receivingAction origin current finishDestination state
            | .stop reason state => .stop reason state
            | .escape address carriers state => .escape address carriers state
            | .jump target kind state => .jump target kind state) prepared) := by
  obtain ⟨outcome, visits, replay, children, ordered, once, execution⟩ :=
    arrayLiteral_fixedElements_ghost fuel config environment child current ty operands origin (path ++ [0])
      childReady prepared ready pending innerElement fixed renewed found elementTypeFound
  refine ⟨outcome, visits, replay, children, ordered, once, ?_⟩
  rw [nonfixedElement_source_execution (fuel + 2) config environment parent child element
    (.arrLit ty operands origin) before layoutReady childReady layout nonfixed layoutResult childResult]
  rw [execution]
  rfl

private def nestedArrayWitness : EvalM Unit := do
  let config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
  let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
  let inner := Ty.varr (.int .i64)
  let outer := Ty.varr inner
  let destination ← newDestination config.layout environment.act outer .value 0
  buildExpr 50 config environment destination (.arrLit outer
    [.arrLit inner [.blockE (.mk 0 [.print [.text "once"] 0]
      (some (.lit .i64 7))) 0, .lit .i64 8] 0] 0)

private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem nestedArrayWitness_sideEffect :
    ∃ state, nestedArrayWitness .initial = .ok () state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨stepState (nestedArrayWitness .initial), ?_, ?_⟩ <;>
    unfold nestedArrayWitness stepState <;> cbv

#print axioms nestedArrayWitness_sideEffect
#print axioms nestedArray_element_ghost
theorem freshAct_transition (before : ExecutionState) :
    freshAct before = .ok before.nextAct { before with nextAct := before.nextAct + 1 } := by
  rfl

#print axioms nonfixedElement_source_execution
#print axioms freshAct_transition
end Goose.Proofs.ConstructionGhostNonfixedElement
