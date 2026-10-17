import Goose.Construct.Eval
import Goose.Proofs.ExitExecution

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct

inductive ListMapMLoopSuccess (action : α → EvalM β) :
    List α → List β → ExecutionState → List β → ExecutionState → Prop
  | nil (accumulator : List β) (state : ExecutionState) :
      ListMapMLoopSuccess action [] accumulator state accumulator.reverse state
  | cons {item : α} {rest : List α} {accumulator : List β}
      {initial middle final : ExecutionState} {value : β} {values : List β}
      (head : action item initial = .ok value middle)
      (tail : ListMapMLoopSuccess action rest (value :: accumulator) middle values final) :
      ListMapMLoopSuccess action (item :: rest) accumulator initial values final

inductive ListMapMLoopStopped (action : α → EvalM β) :
    List α → List β → ExecutionState → Goose.Core.Stop → ExecutionState → List α → Prop
  | atHead {item : α} {rest : List α} {accumulator : List β}
      {initial final : ExecutionState} {reason : Goose.Core.Stop}
      (head : action item initial = .stop reason final) :
      ListMapMLoopStopped action (item :: rest) accumulator initial reason final [item]
  | afterHead {item : α} {rest visited : List α} {accumulator : List β}
      {initial middle final : ExecutionState} {value : β} {reason : Goose.Core.Stop}
      (head : action item initial = .ok value middle)
      (tail : ListMapMLoopStopped action rest (value :: accumulator) middle reason final visited) :
      ListMapMLoopStopped action (item :: rest) accumulator initial reason final (item :: visited)

inductive ListMapMLoopEscaped (action : α → EvalM β) :
    List α → List β → ExecutionState → ExitAddress → List Carrier → ExecutionState → List α → Prop
  | atHead {item : α} {rest : List α} {accumulator : List β}
      {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
      (head : action item initial = .escape address carriers final) :
      ListMapMLoopEscaped action (item :: rest) accumulator initial address carriers final [item]
  | afterHead {item : α} {rest visited : List α} {accumulator : List β}
      {initial middle final : ExecutionState} {value : β} {address : ExitAddress}
      {carriers : List Carrier}
      (head : action item initial = .ok value middle)
      (tail : ListMapMLoopEscaped action rest (value :: accumulator) middle address carriers final visited) :
      ListMapMLoopEscaped action (item :: rest) accumulator initial address carriers final
        (item :: visited)

inductive ListMapMLoopJumped (action : α → EvalM β) :
    List α → List β → ExecutionState → Nat → JumpKind → ExecutionState → List α → Prop
  | atHead {item : α} {rest : List α} {accumulator : List β}
      {initial final : ExecutionState} {target : Nat} {kind : JumpKind}
      (head : action item initial = .jump target kind final) :
      ListMapMLoopJumped action (item :: rest) accumulator initial target kind final [item]
  | afterHead {item : α} {rest visited : List α} {accumulator : List β}
      {initial middle final : ExecutionState} {value : β} {target : Nat} {kind : JumpKind}
      (head : action item initial = .ok value middle)
      (tail : ListMapMLoopJumped action rest (value :: accumulator) middle target kind final visited) :
      ListMapMLoopJumped action (item :: rest) accumulator initial target kind final
        (item :: visited)

def SourcePrefix (visited inputs : List α) : Prop :=
  ∃ suffix, inputs = visited ++ suffix

theorem listMapMLoop_success_trace (action : α → EvalM β) (inputs : List α)
    (accumulator : List β) (initial : ExecutionState) (values : List β) (final : ExecutionState)
    (result : List.mapM.loop action inputs accumulator initial = .ok values final) :
    ListMapMLoopSuccess action inputs accumulator initial values final := by
  induction inputs generalizing accumulator initial values final with
  | nil =>
      rw [List.mapM.loop.eq_1] at result
      simp only [pure] at result
      cases result
      exact .nil accumulator initial
  | cons item rest ih =>
      rw [List.mapM.loop.eq_2] at result
      cases head : action item initial with
      | ok value middle =>
          simp only [bind, head] at result
          exact .cons head (ih (value :: accumulator) middle values final result)
      | stop reason middle => simp only [bind, head] at result; cases result
      | escape address carriers middle => simp only [bind, head] at result; cases result
      | jump target kind middle => simp only [bind, head] at result; cases result

theorem listMapM_success_trace (action : α → EvalM β) (inputs : List α)
    (initial : ExecutionState) (values : List β) (final : ExecutionState)
    (result : (inputs.mapM action) initial = .ok values final) :
    ListMapMLoopSuccess action inputs [] initial values final := by
  apply listMapMLoop_success_trace action inputs [] initial values final
  simpa only [List.mapM] using result

private def listForInUnit (action : α → EvalM Unit) (inputs : List α) : EvalM PUnit :=
  forIn inputs PUnit.unit (fun input _ => do
    action input
    pure (ForInStep.yield PUnit.unit))

private theorem listForInUnit_success_trace (action : α → EvalM Unit) (inputs : List α)
    (accumulator : List Unit) (initial final : ExecutionState)
    (result : listForInUnit action inputs initial = .ok PUnit.unit final) :
    ∃ values, ListMapMLoopSuccess action inputs accumulator initial values final := by
  induction inputs generalizing accumulator initial final with
  | nil =>
      simp only [listForInUnit, List.forIn_nil, pure] at result
      cases result
      exact ⟨accumulator.reverse, .nil accumulator initial⟩
  | cons input inputs ih =>
      simp only [listForInUnit, List.forIn_cons] at result
      cases head : action input initial with
      | ok value middle =>
          simp only [bind, head, pure] at result
          obtain ⟨values, tail⟩ := ih (value :: accumulator) middle final result
          exact ⟨values, .cons head tail⟩
      | stop reason middle => simp only [bind, head] at result; cases result
      | escape address carriers middle => simp only [bind, head] at result; cases result
      | jump target kind middle => simp only [bind, head] at result; cases result

private theorem protectDestination_success (origin : Goose.Core.OriginId)
    (destination : Goose.Core.DestinationId) (action : EvalM α)
    (initial : ExecutionState) (value : α) (final : ExecutionState)
    (result : protectDestination origin destination action initial = .ok value final) :
    action initial = .ok value final := by
  cases actionResult : action initial with
  | ok actual state => simp only [protectDestination, actionResult] at result; cases result; rfl
  | stop reason state => simp only [protectDestination, actionResult] at result; cases result
  | escape address carriers state =>
      simp only [protectDestination, actionResult] at result
      split at result <;> cases result
  | jump target kind state =>
      simp only [protectDestination, actionResult] at result
      split at result <;> cases result

theorem listMapMLoop_success_length (action : α → EvalM β) {inputs : List α}
    {accumulator : List β} {initial : ExecutionState} {values : List β} {final : ExecutionState}
    (trace : ListMapMLoopSuccess action inputs accumulator initial values final) :
    values.length = inputs.length + accumulator.length := by
  induction trace with
  | nil accumulator state => simp
  | @cons item rest accumulator initial middle final value values head tail ih =>
      simp only [List.length_cons] at ih ⊢
      omega

theorem buildExpr_arrayLiteral_success_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (destination : Goose.Core.DestinationId) (ty : Ty)
    (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState)
    (result : buildExpr (fuel + 1) config environment destination (.arrLit ty operands origin)
      initial = .ok () final) :
    ∃ pending before element values after,
      getDestination destination initial = .ok pending before ∧
      elementType pending.capability.logicalType = some element ∧
      ListMapMLoopSuccess
        (fun operand => buildElement fuel config environment destination element operand)
        operands [] before values after ∧
      values.length = operands.length ∧
      liftConstruction origin (finishDestination destination) after = .ok () final := by
  simp only [buildExpr, expressionOrigin] at result
  have bodyResult : (do
      let pending ← getDestination destination
      let some element := elementType pending.capability.logicalType | fault .shape
      for operand in operands do
        buildElement fuel config environment destination element operand
      liftConstruction origin (finishDestination destination)) initial = .ok () final :=
    protectDestination_success origin destination _ initial () final result
  cases pendingResult : getDestination destination initial with
  | ok pending before =>
      simp only [bind, pendingResult] at bodyResult
      cases elementResult : elementType pending.capability.logicalType with
      | none => simp only [elementResult] at bodyResult; cases bodyResult
      | some element =>
          simp only [elementResult] at bodyResult
          split at bodyResult
          case h_1 _ value after loopResult =>
              have loopSuccess : listForInUnit
                  (fun operand => buildElement fuel config environment destination element operand)
                  operands before = .ok PUnit.unit after := by
                exact loopResult
              obtain ⟨values, trace⟩ := listForInUnit_success_trace
                (fun operand => buildElement fuel config environment destination element operand)
                operands [] before after loopSuccess
              have count : values.length = operands.length := by
                simpa using listMapMLoop_success_length
                  (fun operand => buildElement fuel config environment destination element operand)
                  trace
              refine ⟨pending, before, element, values, after, ?_, elementResult, trace,
                count, bodyResult⟩
              rfl
          case h_2 _ _ _ _ => cases bodyResult
          case h_3 _ _ _ _ => cases bodyResult
          case h_4 _ _ _ _ => cases bodyResult
  | stop reason before => simp only [bind, pendingResult] at bodyResult; cases bodyResult
  | escape address carriers before => simp only [bind, pendingResult] at bodyResult; cases bodyResult
  | jump target kind before => simp only [bind, pendingResult] at bodyResult; cases bodyResult

theorem evalValue_nonfixedArray_success_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (value : Value)
    (nonfixed : ty.nonfixed = true)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .ok value final) :
    ∃ elementFuel destination opened pending before element values after buildFinal,
      fuel = elementFuel + 1 ∧
      newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial =
        .ok destination opened ∧
      getDestination destination opened = .ok pending before ∧
      elementType pending.capability.logicalType = some element ∧
      ListMapMLoopSuccess
        (fun operand => buildElement elementFuel config environment destination element operand)
        operands [] before values after ∧
      values.length = operands.length ∧
      liftConstruction origin (finishDestination destination) after = .ok () buildFinal := by
  simp only [evalValue] at result
  simp [nonfixed] at result
  simp only [constructLocal] at result
  cases opened : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
      (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial with
  | ok destination before =>
      simp only [bind, opened] at result
      cases built : buildExpr fuel config environment destination (.arrLit ty operands origin) before with
      | ok _ buildFinal =>
          cases fuel with
          | zero => simp only [buildExpr] at built; cases built
          | succ elementFuel =>
              obtain ⟨pending, before', element, values, after, openedDestination, elementResult,
                trace, count, finish⟩ := buildExpr_arrayLiteral_success_trace elementFuel config
                  environment destination ty operands origin before buildFinal built
              exact ⟨elementFuel, destination, before, pending, before', element, values, after,
                buildFinal, rfl, rfl, openedDestination, elementResult, trace, count, finish⟩
      | stop reason after => simp only [built] at result; cases result
      | escape address carriers after => simp only [built] at result; cases result
      | jump target kind after => simp only [built] at result; cases result
  | stop reason before => simp only [bind, opened] at result; cases result
  | escape address carriers before => simp only [bind, opened] at result; cases result
  | jump target kind before => simp only [bind, opened] at result; cases result

theorem listMapMLoop_stopped_trace (action : α → EvalM β) (inputs : List α)
    (accumulator : List β) (initial : ExecutionState) (reason : Goose.Core.Stop)
    (final : ExecutionState)
    (result : List.mapM.loop action inputs accumulator initial = .stop reason final) :
    ∃ visited, ListMapMLoopStopped action inputs accumulator initial reason final visited := by
  induction inputs generalizing accumulator initial reason final with
  | nil =>
      rw [List.mapM.loop.eq_1] at result
      simp only [pure] at result
      cases result
  | cons item rest ih =>
      rw [List.mapM.loop.eq_2] at result
      cases head : action item initial with
      | ok value middle =>
          simp only [bind, head] at result
          obtain ⟨visited, tail⟩ := ih (value :: accumulator) middle reason final result
          exact ⟨item :: visited, .afterHead head tail⟩
      | stop stopped final' =>
          simp only [bind, head] at result
          cases result
          exact ⟨[item], .atHead (rest := rest) (accumulator := accumulator) head⟩
      | escape address carriers final' => simp only [bind, head] at result; cases result
      | jump target kind final' => simp only [bind, head] at result; cases result

theorem sourcePrefix_of_stopped {action : α → EvalM β} {inputs : List α}
    {accumulator : List β} {initial : ExecutionState} {reason : Goose.Core.Stop}
    {final : ExecutionState} {visited : List α}
    (trace : ListMapMLoopStopped action inputs accumulator initial reason final visited) :
    SourcePrefix visited inputs := by
  induction trace with
  | atHead head => exact ⟨_, rfl⟩
  | @afterHead item rest visited accumulator initial middle final value reason head tail ih =>
      obtain ⟨suffix, suffixEq⟩ := ih
      exact ⟨suffix, by simp [suffixEq]⟩

theorem listMapM_stopped_source_prefix (action : α → EvalM β) (inputs : List α)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (result : (inputs.mapM action) initial = .stop reason final) :
    ∃ visited, SourcePrefix visited inputs := by
  change List.mapM.loop action inputs [] initial = .stop reason final at result
  obtain ⟨visited, trace⟩ := listMapMLoop_stopped_trace action inputs [] initial reason final result
  exact ⟨visited, sourcePrefix_of_stopped trace⟩

theorem listMapMLoop_escaped_trace (action : α → EvalM β) (inputs : List α)
    (accumulator : List β) (initial : ExecutionState) (address : ExitAddress)
    (carriers : List Carrier) (final : ExecutionState)
    (result : List.mapM.loop action inputs accumulator initial =
      .escape address carriers final) :
    ∃ visited, ListMapMLoopEscaped action inputs accumulator initial address carriers final visited := by
  induction inputs generalizing accumulator initial address carriers final with
  | nil =>
      rw [List.mapM.loop.eq_1] at result
      simp only [pure] at result
      cases result
  | cons item rest ih =>
      rw [List.mapM.loop.eq_2] at result
      cases head : action item initial with
      | ok value middle =>
          simp only [bind, head] at result
          obtain ⟨visited, tail⟩ := ih (value :: accumulator) middle address carriers final result
          exact ⟨item :: visited, .afterHead head tail⟩
      | stop reason final' => simp only [bind, head] at result; cases result
      | escape escapedAddress escapedCarriers final' =>
          simp only [bind, head] at result
          cases result
          exact ⟨[item], .atHead (rest := rest) (accumulator := accumulator) head⟩
      | jump target kind final' => simp only [bind, head] at result; cases result

theorem sourcePrefix_of_escaped {action : α → EvalM β} {inputs : List α}
    {accumulator : List β} {initial : ExecutionState} {address : ExitAddress}
    {carriers : List Carrier} {final : ExecutionState} {visited : List α}
    (trace : ListMapMLoopEscaped action inputs accumulator initial address carriers final visited) :
    SourcePrefix visited inputs := by
  induction trace with
  | atHead head => exact ⟨_, rfl⟩
  | @afterHead item rest visited accumulator initial middle final value address carriers head tail ih =>
      obtain ⟨suffix, suffixEq⟩ := ih
      exact ⟨suffix, by simp [suffixEq]⟩

theorem listMapMLoop_jumped_trace (action : α → EvalM β) (inputs : List α)
    (accumulator : List β) (initial : ExecutionState) (target : Nat) (kind : JumpKind)
    (final : ExecutionState)
    (result : List.mapM.loop action inputs accumulator initial = .jump target kind final) :
    ∃ visited, ListMapMLoopJumped action inputs accumulator initial target kind final visited := by
  induction inputs generalizing accumulator initial target kind final with
  | nil =>
      rw [List.mapM.loop.eq_1] at result
      simp only [pure] at result
      cases result
  | cons item rest ih =>
      rw [List.mapM.loop.eq_2] at result
      cases head : action item initial with
      | ok value middle =>
          simp only [bind, head] at result
          obtain ⟨visited, tail⟩ := ih (value :: accumulator) middle target kind final result
          exact ⟨item :: visited, .afterHead head tail⟩
      | stop reason final' => simp only [bind, head] at result; cases result
      | escape address carriers final' => simp only [bind, head] at result; cases result
      | jump jumpedTarget jumpedKind final' =>
          simp only [bind, head] at result
          cases result
          exact ⟨[item], .atHead (rest := rest) (accumulator := accumulator) head⟩

theorem sourcePrefix_of_jumped {action : α → EvalM β} {inputs : List α}
    {accumulator : List β} {initial : ExecutionState} {target : Nat} {kind : JumpKind}
    {final : ExecutionState} {visited : List α}
    (trace : ListMapMLoopJumped action inputs accumulator initial target kind final visited) :
    SourcePrefix visited inputs := by
  induction trace with
  | atHead head => exact ⟨_, rfl⟩
  | @afterHead item rest visited accumulator initial middle final value target kind head tail ih =>
      obtain ⟨suffix, suffixEq⟩ := ih
      exact ⟨suffix, by simp [suffixEq]⟩

theorem listMapM_jumped_source_prefix (action : α → EvalM β) (inputs : List α)
    (initial final : ExecutionState) (target : Nat) (kind : JumpKind)
    (result : (inputs.mapM action) initial = .jump target kind final) :
    ∃ visited, SourcePrefix visited inputs := by
  change List.mapM.loop action inputs [] initial = .jump target kind final at result
  obtain ⟨visited, trace⟩ :=
    listMapMLoop_jumped_trace action inputs [] initial target kind final result
  exact ⟨visited, sourcePrefix_of_jumped trace⟩

theorem listMapM_escaped_source_prefix (action : α → EvalM β) (inputs : List α)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (result : (inputs.mapM action) initial = .escape address carriers final) :
    ∃ visited, SourcePrefix visited inputs := by
  change List.mapM.loop action inputs [] initial = .escape address carriers final at result
  obtain ⟨visited, trace⟩ :=
    listMapMLoop_escaped_trace action inputs [] initial address carriers final result
  exact ⟨visited, sourcePrefix_of_escaped trace⟩

theorem listMapM_success_length (action : α → EvalM β) (inputs : List α)
    (initial : ExecutionState) (values : List β) (final : ExecutionState)
    (result : (inputs.mapM action) initial = .ok values final) :
    values.length = inputs.length := by
  have trace := listMapM_success_trace action inputs initial values final result
  simpa using listMapMLoop_success_length action trace

inductive EvalOperandsSuccess (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Channel → List Expr → ExecutionState → List Carrier → ExecutionState → Prop
  | nil (fuel : Nat) (state : ExecutionState) :
      EvalOperandsSuccess config environment fuel [] [] state [] state
  | cons {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands : List Expr}
      {initial producedState middle final : ExecutionState} {produced : List Carrier}
      {carrier : Carrier} {carriers : List Carrier}
      (produce : evalProduce fuel config environment [channel] operand initial =
        .ok produced producedState)
      (single : singleCarrier produced producedState = .ok carrier middle)
      (tail : EvalOperandsSuccess config environment fuel channels operands middle carriers final) :
      EvalOperandsSuccess config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial (carrier :: carriers) final

inductive EvalOperandsStopped (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Channel → List Expr → ExecutionState → Goose.Core.Stop → ExecutionState →
      List Expr → Prop
  | timeout (channels : List Channel) (operands : List Expr) (initial : ExecutionState) :
      EvalOperandsStopped config environment 0 channels operands initial .timeout initial []
  | missingChannel (fuel : Nat) (operand : Expr) (operands : List Expr)
      (initial : ExecutionState) :
      EvalOperandsStopped config environment (fuel + 1) [] (operand :: operands) initial
        (.fault .arity) initial []
  | missingOperand (fuel : Nat) (channel : Channel) (channels : List Channel)
      (initial : ExecutionState) :
      EvalOperandsStopped config environment (fuel + 1) (channel :: channels) [] initial
        (.fault .arity) initial []
  | atProduce {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands : List Expr} {initial final : ExecutionState} {reason : Goose.Core.Stop}
      (head : evalProduce fuel config environment [channel] operand initial = .stop reason final) :
      EvalOperandsStopped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial reason final [operand]
  | atCarrier {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands : List Expr} {initial producedState final : ExecutionState}
      {produced : List Carrier} {reason : Goose.Core.Stop}
      (produce : evalProduce fuel config environment [channel] operand initial =
        .ok produced producedState)
      (single : singleCarrier produced producedState = .stop reason final) :
      EvalOperandsStopped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial reason final [operand]
  | afterHead {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands visited : List Expr} {initial producedState middle final : ExecutionState}
      {produced : List Carrier} {carrier : Carrier} {reason : Goose.Core.Stop}
      (produce : evalProduce fuel config environment [channel] operand initial =
        .ok produced producedState)
      (single : singleCarrier produced producedState = .ok carrier middle)
      (tail : EvalOperandsStopped config environment fuel channels operands middle reason final
        visited) :
      EvalOperandsStopped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial reason final (operand :: visited)

inductive EvalOperandsEscaped (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Channel → List Expr → ExecutionState → ExitAddress → List Carrier →
      ExecutionState → List Expr → Prop
  | atProduce {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands : List Expr} {initial final : ExecutionState} {address : ExitAddress}
      {carriers : List Carrier}
      (head : evalProduce fuel config environment [channel] operand initial =
        .escape address carriers final) :
      EvalOperandsEscaped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial address carriers final [operand]
  | atCarrier {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands : List Expr} {initial producedState final : ExecutionState}
      {produced : List Carrier} {address : ExitAddress} {carriers : List Carrier}
      (produce : evalProduce fuel config environment [channel] operand initial =
        .ok produced producedState)
      (single : singleCarrier produced producedState = .escape address carriers final) :
      EvalOperandsEscaped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial address carriers final [operand]
  | afterHead {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands visited : List Expr} {initial producedState middle final : ExecutionState}
      {produced : List Carrier} {carrier : Carrier} {address : ExitAddress}
      {carriers : List Carrier}
      (produce : evalProduce fuel config environment [channel] operand initial =
        .ok produced producedState)
      (single : singleCarrier produced producedState = .ok carrier middle)
      (tail : EvalOperandsEscaped config environment fuel channels operands middle address
        carriers final visited) :
      EvalOperandsEscaped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial address carriers final (operand :: visited)

inductive EvalOperandsJumped (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Channel → List Expr → ExecutionState → Nat → JumpKind → ExecutionState →
      List Expr → Prop
  | atProduce {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands : List Expr} {initial final : ExecutionState} {target : Nat} {kind : JumpKind}
      (head : evalProduce fuel config environment [channel] operand initial =
        .jump target kind final) :
      EvalOperandsJumped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial target kind final [operand]
  | atCarrier {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands : List Expr} {initial producedState final : ExecutionState}
      {produced : List Carrier} {target : Nat} {kind : JumpKind}
      (produce : evalProduce fuel config environment [channel] operand initial =
        .ok produced producedState)
      (single : singleCarrier produced producedState = .jump target kind final) :
      EvalOperandsJumped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial target kind final [operand]
  | afterHead {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands visited : List Expr} {initial producedState middle final : ExecutionState}
      {produced : List Carrier} {carrier : Carrier} {target : Nat} {kind : JumpKind}
      (produce : evalProduce fuel config environment [channel] operand initial =
        .ok produced producedState)
      (single : singleCarrier produced producedState = .ok carrier middle)
      (tail : EvalOperandsJumped config environment fuel channels operands middle target kind final
        visited) :
      EvalOperandsJumped config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial target kind final (operand :: visited)

theorem evalOperands_success_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) :
    ∀ {channels : List Channel} {operands : List Expr} {initial final : ExecutionState}
      {carriers : List Carrier},
      evalOperands fuel config environment channels operands initial = .ok carriers final →
      EvalOperandsSuccess config environment fuel channels operands initial carriers final := by
  induction fuel with
  | zero =>
      intro channels operands initial final carriers result
      simp only [evalOperands, timeout, EvalM.stop] at result
      cases result
  | succ fuel ih =>
      intro channels operands initial final carriers result
      cases channels with
      | nil =>
          cases operands with
          | nil =>
              simp only [evalOperands, pure] at result
              cases result
              exact .nil _ initial
          | cons operand operands =>
              simp only [evalOperands, fault, EvalM.stop] at result
              cases result
      | cons channel channels =>
          cases operands with
          | nil =>
              simp only [evalOperands, fault, EvalM.stop] at result
              cases result
          | cons operand operands =>
              simp only [evalOperands] at result
              cases produce : evalProduce fuel config environment [channel] operand initial with
              | ok produced producedState =>
                  simp only [bind, produce] at result
                  cases single : singleCarrier produced producedState with
                  | ok carrier middle =>
                      simp only [single] at result
                      cases tail : evalOperands fuel config environment channels operands middle with
                      | ok remaining final' =>
                          simp only [tail, pure] at result
                          injection result with carriersEq stateEq
                          subst carriers
                          subst final
                          exact .cons produce single (ih tail)
                      | stop reason final' => simp only [tail] at result; cases result
                      | escape address exits final' => simp only [tail] at result; cases result
                      | jump target kind final' => simp only [tail] at result; cases result
                  | stop reason middle => simp only [single] at result; cases result
                  | escape address exits middle => simp only [single] at result; cases result
                  | jump target kind middle => simp only [single] at result; cases result
              | stop reason middle => simp only [bind, produce] at result; cases result
              | escape address exits middle => simp only [bind, produce] at result; cases result
              | jump target kind middle => simp only [bind, produce] at result; cases result

theorem evalOperands_success_count (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) {channels : List Channel} {operands : List Expr}
    {initial final : ExecutionState} {carriers : List Carrier}
    (trace : EvalOperandsSuccess config environment fuel channels operands initial carriers final) :
    carriers.length = operands.length := by
  induction trace with
  | nil _ state => rfl
  | @cons fuel channel channels operand operands initial middle final carrier carriers head tail ih =>
      simp only [List.length_cons] at ih ⊢
      omega

theorem evalOperands_stopped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) :
    ∀ {channels : List Channel} {operands : List Expr} {initial final : ExecutionState}
      {reason : Goose.Core.Stop},
      evalOperands fuel config environment channels operands initial = .stop reason final →
      ∃ visited, EvalOperandsStopped config environment fuel channels operands initial reason final
        visited := by
  induction fuel with
  | zero =>
      intro channels operands initial final reason result
      simp only [evalOperands, timeout] at result
      cases result
      exact ⟨[], .timeout channels operands initial⟩
  | succ fuel ih =>
      intro channels operands initial final reason result
      cases channels with
      | nil =>
          cases operands with
          | nil =>
              simp only [evalOperands, pure] at result
              cases result
          | cons operand operands =>
              simp only [evalOperands, fault] at result
              cases result
              exact ⟨[], .missingChannel fuel operand operands initial⟩
      | cons channel channels =>
          cases operands with
          | nil =>
              simp only [evalOperands, fault] at result
              cases result
              exact ⟨[], .missingOperand fuel channel channels initial⟩
          | cons operand operands =>
              simp only [evalOperands] at result
              cases produce : evalProduce fuel config environment [channel] operand initial with
              | ok produced producedState =>
                  simp only [bind, produce] at result
                  cases single : singleCarrier produced producedState with
                  | ok carrier middle =>
                      simp only [single] at result
                      cases tail : evalOperands fuel config environment channels operands middle with
                      | ok carriers final' => simp only [tail, pure] at result; cases result
                      | stop stopped final' =>
                          simp only [tail] at result
                          cases result
                          obtain ⟨visited, trace⟩ := ih tail
                          exact ⟨operand :: visited, .afterHead produce single trace⟩
                      | escape address carriers final' => simp only [tail] at result; cases result
                      | jump target kind final' => simp only [tail] at result; cases result
                  | stop stopped final' =>
                      simp only [single] at result
                      cases result
                      exact ⟨[operand], .atCarrier produce single⟩
                  | escape address carriers final' => simp only [single] at result; cases result
                  | jump target kind final' => simp only [single] at result; cases result
              | stop stopped final' =>
                  simp only [bind, produce] at result
                  cases result
                  exact ⟨[operand], .atProduce produce⟩
              | escape address carriers final' => simp only [bind, produce] at result; cases result
              | jump target kind final' => simp only [bind, produce] at result; cases result

theorem evalOperands_escaped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) :
    ∀ {channels : List Channel} {operands : List Expr} {initial final : ExecutionState}
      {address : ExitAddress} {carriers : List Carrier},
      evalOperands fuel config environment channels operands initial = .escape address carriers final →
      ∃ visited, EvalOperandsEscaped config environment fuel channels operands initial address
        carriers final visited := by
  induction fuel with
  | zero =>
      intro channels operands initial final address carriers result
      simp only [evalOperands, timeout] at result
      cases result
  | succ fuel ih =>
      intro channels operands initial final address carriers result
      cases channels with
      | nil =>
          cases operands with
          | nil =>
              simp only [evalOperands, pure] at result
              cases result
          | cons operand operands =>
              simp only [evalOperands, fault] at result
              cases result
      | cons channel channels =>
          cases operands with
          | nil =>
              simp only [evalOperands, fault] at result
              cases result
          | cons operand operands =>
              simp only [evalOperands] at result
              cases produce : evalProduce fuel config environment [channel] operand initial with
              | ok produced producedState =>
                  simp only [bind, produce] at result
                  cases single : singleCarrier produced producedState with
                  | ok carrier middle =>
                      simp only [single] at result
                      cases tail : evalOperands fuel config environment channels operands middle with
                      | ok remaining final' => simp only [tail, pure] at result; cases result
                      | stop reason final' => simp only [tail] at result; cases result
                      | escape escapedAddress escapedCarriers final' =>
                          simp only [tail] at result
                          cases result
                          obtain ⟨visited, trace⟩ := ih tail
                          exact ⟨operand :: visited, .afterHead produce single trace⟩
                      | jump target kind final' => simp only [tail] at result; cases result
                  | stop reason final' => simp only [single] at result; cases result
                  | escape escapedAddress escapedCarriers final' =>
                      simp only [single] at result
                      cases result
                      exact ⟨[operand], .atCarrier produce single⟩
                  | jump target kind final' => simp only [single] at result; cases result
              | stop reason final' => simp only [bind, produce] at result; cases result
              | escape escapedAddress escapedCarriers final' =>
                  simp only [bind, produce] at result
                  cases result
                  exact ⟨[operand], .atProduce produce⟩
              | jump target kind final' => simp only [bind, produce] at result; cases result

theorem evalOperands_jumped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) :
    ∀ {channels : List Channel} {operands : List Expr} {initial final : ExecutionState}
      {target : Nat} {kind : JumpKind},
      evalOperands fuel config environment channels operands initial = .jump target kind final →
      ∃ visited, EvalOperandsJumped config environment fuel channels operands initial target kind
        final visited := by
  induction fuel with
  | zero =>
      intro channels operands initial final target kind result
      simp only [evalOperands, timeout] at result
      cases result
  | succ fuel ih =>
      intro channels operands initial final target kind result
      cases channels with
      | nil =>
          cases operands with
          | nil =>
              simp only [evalOperands, pure] at result
              cases result
          | cons operand operands =>
              simp only [evalOperands, fault] at result
              cases result
      | cons channel channels =>
          cases operands with
          | nil =>
              simp only [evalOperands, fault] at result
              cases result
          | cons operand operands =>
              simp only [evalOperands] at result
              cases produce : evalProduce fuel config environment [channel] operand initial with
              | ok produced producedState =>
                  simp only [bind, produce] at result
                  cases single : singleCarrier produced producedState with
                  | ok carrier middle =>
                      simp only [single] at result
                      cases tail : evalOperands fuel config environment channels operands middle with
                      | ok remaining final' => simp only [tail, pure] at result; cases result
                      | stop reason final' => simp only [tail] at result; cases result
                      | escape address carriers final' => simp only [tail] at result; cases result
                      | jump jumpedTarget jumpedKind final' =>
                          simp only [tail] at result
                          cases result
                          obtain ⟨visited, trace⟩ := ih tail
                          exact ⟨operand :: visited, .afterHead produce single trace⟩
                  | stop reason final' => simp only [single] at result; cases result
                  | escape address carriers final' => simp only [single] at result; cases result
                  | jump jumpedTarget jumpedKind final' =>
                      simp only [single] at result
                      cases result
                      exact ⟨[operand], .atCarrier produce single⟩
              | stop reason final' => simp only [bind, produce] at result; cases result
              | escape address carriers final' => simp only [bind, produce] at result; cases result
              | jump jumpedTarget jumpedKind final' =>
                  simp only [bind, produce] at result
                  cases result
                  exact ⟨[operand], .atProduce produce⟩

theorem evalOperands_stopped_source_prefix {config : EvalConfig}
    {environment : RuntimeActivation} {fuel : Nat} {channels : List Channel}
    {operands visited : List Expr} {initial final : ExecutionState} {reason : Goose.Core.Stop}
    (trace : EvalOperandsStopped config environment fuel channels operands initial reason final
      visited) :
    SourcePrefix visited operands := by
  induction trace with
  | timeout channels operands initial => exact ⟨operands, rfl⟩
  | missingChannel fuel operand operands initial => exact ⟨operand :: operands, rfl⟩
  | missingOperand fuel channel channels initial => exact ⟨[], rfl⟩
  | atProduce head => exact ⟨_, rfl⟩
  | atCarrier produce single => exact ⟨_, rfl⟩
  | @afterHead fuel channel channels operand operands visited initial producedState middle final
      produced carrier reason produce single tail ih =>
      obtain ⟨suffix, suffixEq⟩ := ih
      exact ⟨suffix, by simp [suffixEq]⟩

theorem evalOperands_escaped_source_prefix {config : EvalConfig}
    {environment : RuntimeActivation} {fuel : Nat} {channels : List Channel}
    {operands visited : List Expr} {initial final : ExecutionState} {address : ExitAddress}
    {carriers : List Carrier}
    (trace : EvalOperandsEscaped config environment fuel channels operands initial address
      carriers final visited) :
    SourcePrefix visited operands := by
  induction trace with
  | atProduce head => exact ⟨_, rfl⟩
  | atCarrier produce single => exact ⟨_, rfl⟩
  | @afterHead fuel channel channels operand operands visited initial producedState middle final
      produced carrier address carriers produce single tail ih =>
      obtain ⟨suffix, suffixEq⟩ := ih
      exact ⟨suffix, by simp [suffixEq]⟩

theorem evalOperands_jumped_source_prefix {config : EvalConfig}
    {environment : RuntimeActivation} {fuel : Nat} {channels : List Channel}
    {operands visited : List Expr} {initial final : ExecutionState} {target : Nat}
    {kind : JumpKind}
    (trace : EvalOperandsJumped config environment fuel channels operands initial target kind
      final visited) :
    SourcePrefix visited operands := by
  induction trace with
  | atProduce head => exact ⟨_, rfl⟩
  | atCarrier produce single => exact ⟨_, rfl⟩
  | @afterHead fuel channel channels operand operands visited initial producedState middle final
      produced carrier target kind produce single tail ih =>
      obtain ⟨suffix, suffixEq⟩ := ih
      exact ⟨suffix, by simp [suffixEq]⟩

theorem evalProduce_values_success_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (carriers : List Carrier)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .ok carriers final) :
    EvalOperandsSuccess config environment fuel channels operands initial carriers final := by
  apply evalOperands_success_trace fuel config environment
  simpa only [evalProduce] using result

theorem evalProduce_values_stopped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .stop reason final) :
    ∃ visited, EvalOperandsStopped config environment fuel channels operands initial reason final
      visited := by
  apply evalOperands_stopped_trace fuel config environment
  simpa only [evalProduce] using result

theorem evalProduce_values_escaped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .escape address carriers final) :
    ∃ visited, EvalOperandsEscaped config environment fuel channels operands initial address
      carriers final visited := by
  apply evalOperands_escaped_trace fuel config environment
  simpa only [evalProduce] using result

theorem evalProduce_values_jumped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (target : Nat) (kind : JumpKind)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .jump target kind final) :
    ∃ visited, EvalOperandsJumped config environment fuel channels operands initial target kind
      final visited := by
  apply evalOperands_jumped_trace fuel config environment
  simpa only [evalProduce] using result

theorem evalProduce_values_stopped_source_prefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .stop reason final) :
    ∃ visited, SourcePrefix visited operands := by
  obtain ⟨visited, trace⟩ := evalProduce_values_stopped_trace fuel config environment channels
    operands initial final reason result
  exact ⟨visited, evalOperands_stopped_source_prefix trace⟩

theorem evalProduce_values_escaped_source_prefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .escape address carriers final) :
    ∃ visited, SourcePrefix visited operands := by
  obtain ⟨visited, trace⟩ := evalProduce_values_escaped_trace fuel config environment channels
    operands initial final address carriers result
  exact ⟨visited, evalOperands_escaped_source_prefix trace⟩

theorem evalProduce_values_jumped_source_prefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (target : Nat) (kind : JumpKind)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .jump target kind final) :
    ∃ visited, SourcePrefix visited operands := by
  obtain ⟨visited, trace⟩ := evalProduce_values_jumped_trace fuel config environment channels
    operands initial final target kind result
  exact ⟨visited, evalOperands_jumped_source_prefix trace⟩

theorem evalProduce_values_success_count (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (carriers : List Carrier)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .ok carriers final) :
    carriers.length = operands.length :=
  evalOperands_success_count fuel config environment (evalProduce_values_success_trace
    fuel config environment channels operands initial final carriers result)

theorem evalValue_fixedFill_source_once (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (element : Ty) (count : Nat) (operand : Expr)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (values : Array Value)
    (fixed : (Ty.arr element count).nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.fill (.arr element count) operand origin)
      initial = .ok (.fixed values) final) :
    ∃ value, evalValue fuel config environment operand initial = .ok value final ∧
      values = Array.replicate count value := by
  simp only [evalValue] at result
  have notTrue : ¬ (Ty.arr element count).nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandResult : evalValue fuel config environment operand initial with
  | ok value final' =>
      rw [operandResult] at result
      have valuesEq : values = Array.replicate count value := by
        injection result with valueEq stateEq
        injection valueEq with valuesEq
        exact valuesEq.symm
      have finalEq : final' = final := by injection result
      subst final'
      exact ⟨value, rfl, valuesEq⟩
  | stop reason final' => rw [operandResult] at result; cases result
  | escape address carriers final' => rw [operandResult] at result; cases result
  | jump target kind final' => rw [operandResult] at result; cases result

theorem evalValue_fixedFill_result (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (element : Ty) (count : Nat) (operand : Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState)
    (fixed : (Ty.arr element count).nonfixed = false) :
    evalValue (fuel + 1) config environment (.fill (.arr element count) operand origin) initial =
      match evalValue fuel config environment operand initial with
      | .ok value final => .ok (.fixed (Array.replicate count value)) final
      | .stop reason final => .stop reason final
      | .escape address carriers final => .escape address carriers final
      | .jump target kind final => .jump target kind final := by
  simp only [evalValue]
  simp [fixed, bind, pure]
  cases evalValue fuel config environment operand initial <;> rfl

theorem evalValue_fixedArray_operands_success_order (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (values : List Value)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .ok (.fixed values.toArray) final) :
    ListMapMLoopSuccess (fun operand => evalValue fuel config environment operand)
      operands [] initial values final := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' =>
      simp only [operandsResult] at result
      have arrayEq : evaluated.toArray = values.toArray := by
        have valueEq : Value.fixed evaluated.toArray = Value.fixed values.toArray := by
          injection result with valueEq stateEq
        injection valueEq with arrayEq
      have listEq : evaluated = values := by
        have listArrayEq := congrArg Array.toList arrayEq
        simpa using listArrayEq
      have stateEq : final' = final := by injection result
      subst final'
      rw [← listEq]
      exact listMapM_success_trace _ _ _ _ _ operandsResult
  | stop reason final' => simp only [operandsResult] at result; cases result
  | escape address carriers final' => simp only [operandsResult] at result; cases result
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_fixedArray_operands_success_count (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (values : List Value)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .ok (.fixed values.toArray) final) :
    values.length = operands.length := by
  simpa using listMapMLoop_success_length
    (fun operand => evalValue fuel config environment operand)
    (evalValue_fixedArray_operands_success_order fuel config environment ty operands origin
      initial final values fixed result)

theorem evalValue_structLiteral_operands_success_order (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (initial final : ExecutionState) (values : List Value)
    (result : evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands)
      initial = .ok (.record id values.toArray) final) :
    ListMapMLoopSuccess (fun operand => evalValue fuel config environment operand)
      operands [] initial values final := by
  simp only [evalValue, bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' =>
      rw [operandsResult] at result
      have arrayEq : evaluated.toArray = values.toArray := by
        have valueEq : Value.record id evaluated.toArray = Value.record id values.toArray := by
          injection result with valueEq stateEq
        injection valueEq with arrayEq
      have listEq : evaluated = values := by
        have listArrayEq := congrArg Array.toList arrayEq
        simpa using listArrayEq
      have stateEq : final' = final := by injection result
      subst final'
      rw [← listEq]
      exact listMapM_success_trace _ _ _ _ _ operandsResult
  | stop reason final' =>
      simp only [operandsResult] at result
      cases result
  | escape address carriers final' =>
      simp only [operandsResult] at result
      cases result
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_structLiteral_operands_success_count (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (initial final : ExecutionState) (values : List Value)
    (result : evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands)
      initial = .ok (.record id values.toArray) final) :
    values.length = operands.length := by
  simpa using listMapMLoop_success_length
    (fun operand => evalValue fuel config environment operand)
    (evalValue_structLiteral_operands_success_order fuel config environment id fields operands
      initial final values result)

theorem evalValue_structLiteral_operands_stopped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (reason : Goose.Core.Stop) (initial final : ExecutionState)
    (result : evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands)
      initial = .stop reason final) :
    ∃ visited, ListMapMLoopStopped (fun operand => evalValue fuel config environment operand)
      operands [] initial reason final visited := by
  simp only [evalValue, bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' => simp only [operandsResult] at result; cases result
  | stop stopped final' =>
      simp only [operandsResult] at result
      cases result
      exact listMapMLoop_stopped_trace _ _ [] _ reason _ operandsResult
  | escape address carriers final' => simp only [operandsResult] at result; cases result
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_structLiteral_operands_escaped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (address : ExitAddress) (carriers : List Carrier)
    (initial final : ExecutionState)
    (result : evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands)
      initial = .escape address carriers final) :
    ∃ visited, ListMapMLoopEscaped (fun operand => evalValue fuel config environment operand)
      operands [] initial address carriers final visited := by
  simp only [evalValue, bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' => simp only [operandsResult] at result; cases result
  | stop reason final' => simp only [operandsResult] at result; cases result
  | escape escapedAddress escapedCarriers final' =>
      simp only [operandsResult] at result
      cases result
      exact listMapMLoop_escaped_trace _ _ [] _ address carriers _ operandsResult
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_structLiteral_operands_jumped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (target : Nat) (kind : JumpKind) (initial final : ExecutionState)
    (result : evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands)
      initial = .jump target kind final) :
    ∃ visited, ListMapMLoopJumped (fun operand => evalValue fuel config environment operand)
      operands [] initial target kind final visited := by
  simp only [evalValue, bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' => simp only [operandsResult] at result; cases result
  | stop reason final' => simp only [operandsResult] at result; cases result
  | escape address carriers final' => simp only [operandsResult] at result; cases result
  | jump jumpedTarget jumpedKind final' =>
      simp only [operandsResult] at result
      cases result
      exact listMapMLoop_jumped_trace _ _ [] _ target kind _ operandsResult

theorem evalValue_fixedArray_operands_stopped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (reason : Goose.Core.Stop) (initial final : ExecutionState)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .stop reason final) :
    ∃ visited, ListMapMLoopStopped (fun operand => evalValue fuel config environment operand)
      operands [] initial reason final visited := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' => simp only [operandsResult] at result; cases result
  | stop stopped final' =>
      simp only [operandsResult] at result
      cases result
      exact listMapMLoop_stopped_trace _ _ [] _ reason _ operandsResult
  | escape address carriers final' => simp only [operandsResult] at result; cases result
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_fixedArray_operands_stopped_prefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (reason : Goose.Core.Stop) (initial final : ExecutionState)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .stop reason final) :
    ∃ visited, SourcePrefix visited operands := by
  obtain ⟨visited, trace⟩ := evalValue_fixedArray_operands_stopped_trace
    fuel config environment ty operands origin reason initial final fixed result
  exact ⟨visited, sourcePrefix_of_stopped trace⟩

theorem evalValue_fixedArray_operands_escaped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (address : ExitAddress) (carriers : List Carrier)
    (initial final : ExecutionState) (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .escape address carriers final) :
    ∃ visited, ListMapMLoopEscaped (fun operand => evalValue fuel config environment operand)
      operands [] initial address carriers final visited := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' => simp only [operandsResult] at result; cases result
  | stop reason final' => simp only [operandsResult] at result; cases result
  | escape address' carriers' final' =>
      simp only [operandsResult] at result
      cases result
      exact listMapMLoop_escaped_trace _ _ [] _ address carriers _ operandsResult
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_fixedArray_operands_jumped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (target : Nat) (kind : JumpKind)
    (initial final : ExecutionState) (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .jump target kind final) :
    ∃ visited, ListMapMLoopJumped (fun operand => evalValue fuel config environment operand)
      operands [] initial target kind final visited := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' => simp only [operandsResult] at result; cases result
  | stop reason final' => simp only [operandsResult] at result; cases result
  | escape address carriers final' => simp only [operandsResult] at result; cases result
  | jump jumpedTarget jumpedKind final' =>
      simp only [operandsResult] at result
      cases result
      exact listMapMLoop_jumped_trace _ _ [] _ target kind _ operandsResult

theorem evalValue_fixedArray_operands_escaped_prefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (address : ExitAddress) (carriers : List Carrier)
    (initial final : ExecutionState) (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .escape address carriers final) :
    ∃ visited, SourcePrefix visited operands := by
  obtain ⟨visited, trace⟩ := evalValue_fixedArray_operands_escaped_trace
    fuel config environment ty operands origin address carriers initial final fixed result
  exact ⟨visited, sourcePrefix_of_escaped trace⟩

end Goose.Proofs.ConstructionExecution
