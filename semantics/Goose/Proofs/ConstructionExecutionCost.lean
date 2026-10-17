import Goose.Proofs.ConstructionExecutionSourceOrder

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct

private theorem sourcePrefix_length_le {visited inputs : List α}
    (ordered : SourcePrefix visited inputs) : visited.length ≤ inputs.length := by
  obtain ⟨suffix, rfl⟩ := ordered
  simp

inductive ListMapMOperandCost (action : α → EvalM β) (inputs : List α)
    (initial : ExecutionState) : ExecutionStep (List β) → Prop
  | completed {values : List β} {final : ExecutionState}
      (trace : ListMapMLoopSuccess action inputs [] initial values final) :
      ListMapMOperandCost action inputs initial (.ok values final)
  | stopped {reason : Goose.Core.Stop} {final : ExecutionState} {visited : List α}
      (trace : ListMapMLoopStopped action inputs [] initial reason final visited) :
      ListMapMOperandCost action inputs initial (.stop reason final)
  | escaped {address : ExitAddress} {carriers : List Carrier} {final : ExecutionState}
      {visited : List α}
      (trace : ListMapMLoopEscaped action inputs [] initial address carriers final visited) :
      ListMapMOperandCost action inputs initial (.escape address carriers final)
  | jumped {target : Nat} {kind : JumpKind} {final : ExecutionState} {visited : List α}
      (trace : ListMapMLoopJumped action inputs [] initial target kind final visited) :
      ListMapMOperandCost action inputs initial (.jump target kind final)

theorem listMapM_operand_cost (action : α → EvalM β) (inputs : List α)
    (initial : ExecutionState) :
    ListMapMOperandCost action inputs initial ((inputs.mapM action) initial) := by
  cases result : (inputs.mapM action) initial with
  | ok values final =>
      exact .completed (listMapM_success_trace action inputs initial values final result)
  | stop reason final =>
      obtain ⟨visited, trace⟩ := listMapMLoop_stopped_trace action inputs [] initial reason final
        (by simpa only [List.mapM] using result)
      exact .stopped trace
  | escape address carriers final =>
      obtain ⟨visited, trace⟩ := listMapMLoop_escaped_trace action inputs [] initial address carriers
        final (by simpa only [List.mapM] using result)
      exact .escaped trace
  | jump target kind final =>
      obtain ⟨visited, trace⟩ := listMapMLoop_jumped_trace action inputs [] initial target kind final
        (by simpa only [List.mapM] using result)
      exact .jumped trace

theorem listMapM_operand_cost_prefix {action : α → EvalM β} {inputs : List α}
    {initial : ExecutionState} {result : ExecutionStep (List β)}
    (cost : ListMapMOperandCost action inputs initial result) :
    ∃ visited, SourcePrefix visited inputs ∧ visited.length ≤ inputs.length := by
  cases cost with
  | completed trace => exact ⟨inputs, ⟨[], by simp⟩, Nat.le_refl _⟩
  | stopped trace =>
      exact ⟨_, sourcePrefix_of_stopped trace, sourcePrefix_length_le (sourcePrefix_of_stopped trace)⟩
  | escaped trace =>
      exact ⟨_, sourcePrefix_of_escaped trace, sourcePrefix_length_le (sourcePrefix_of_escaped trace)⟩
  | jumped trace =>
      exact ⟨_, sourcePrefix_of_jumped trace, sourcePrefix_length_le (sourcePrefix_of_jumped trace)⟩

def fixedArrayOperandResult : ExecutionStep (List Value) → ExecutionStep Value
  | .ok values final => .ok (.fixed values.toArray) final
  | .stop reason final => .stop reason final
  | .escape address carriers final => .escape address carriers final
  | .jump target kind final => .jump target kind final

structure FixedArrayOperandCost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (outcome : ExecutionStep Value) where
  mapped : ExecutionStep (List Value)
  mapResult : (operands.mapM (evalValue fuel config environment)) initial = mapped
  loop : ListMapMOperandCost (evalValue fuel config environment) operands initial mapped
  output : outcome = fixedArrayOperandResult mapped

def evalValue_fixedArray_operand_cost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (outcome : ExecutionStep Value)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial = outcome) :
    FixedArrayOperandCost fuel config environment ty operands origin initial outcome := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases mapResult : (operands.mapM (evalValue fuel config environment)) initial with
  | ok values final =>
      simp only [mapResult] at result
      have output : outcome = fixedArrayOperandResult (.ok values final) := by
        cases result
        rfl
      exact ⟨.ok values final, mapResult,
        .completed (listMapM_success_trace _ _ _ _ _ mapResult), output⟩
  | stop reason final =>
      simp only [mapResult] at result
      have output : outcome = fixedArrayOperandResult (.stop reason final) := by
        cases result
        rfl
      exact ⟨.stop reason final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_stopped_trace (evalValue fuel config environment)
          operands [] initial reason final (by simpa only [List.mapM] using mapResult)
        exact .stopped trace, output⟩
  | escape address carriers final =>
      simp only [mapResult] at result
      have output : outcome = fixedArrayOperandResult (.escape address carriers final) := by
        cases result
        rfl
      exact ⟨.escape address carriers final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_escaped_trace (evalValue fuel config environment)
          operands [] initial address carriers final (by simpa only [List.mapM] using mapResult)
        exact .escaped trace, output⟩
  | jump target kind final =>
      simp only [mapResult] at result
      have output : outcome = fixedArrayOperandResult (.jump target kind final) := by
        cases result
        rfl
      exact ⟨.jump target kind final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_jumped_trace (evalValue fuel config environment)
          operands [] initial target kind final (by simpa only [List.mapM] using mapResult)
        exact .jumped trace, output⟩

theorem evalValue_fixedArray_operand_cost_prefix {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {ty : Ty} {operands : List Expr}
    {origin : Goose.Core.OriginId} {initial : ExecutionState} {outcome : ExecutionStep Value}
    (cost : FixedArrayOperandCost fuel config environment ty operands origin initial outcome) :
    ∃ visited, SourcePrefix visited operands ∧ visited.length ≤ operands.length :=
  listMapM_operand_cost_prefix cost.loop

def recordOperandResult (id : Goose.Core.StructId) :
    ExecutionStep (List Value) → ExecutionStep Value
  | .ok values final => .ok (.record id values.toArray) final
  | .stop reason final => .stop reason final
  | .escape address carriers final => .escape address carriers final
  | .jump target kind final => .jump target kind final

structure RecordOperandCost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (initial : ExecutionState) (outcome : ExecutionStep Value) where
  mapped : ExecutionStep (List Value)
  mapResult : (operands.mapM (evalValue fuel config environment)) initial = mapped
  loop : ListMapMOperandCost (evalValue fuel config environment) operands initial mapped
  output : outcome = recordOperandResult id mapped

def evalValue_structLiteral_operand_cost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (initial : ExecutionState) (outcome : ExecutionStep Value)
    (result : evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands)
      initial = outcome) :
    RecordOperandCost fuel config environment id fields operands initial outcome := by
  simp only [evalValue, bind, pure] at result
  cases mapResult : (operands.mapM (evalValue fuel config environment)) initial with
  | ok values final =>
      simp only [mapResult] at result
      have output : outcome = recordOperandResult id (.ok values final) := by
        cases result
        rfl
      exact ⟨.ok values final, mapResult,
        .completed (listMapM_success_trace _ _ _ _ _ mapResult), output⟩
  | stop reason final =>
      simp only [mapResult] at result
      have output : outcome = recordOperandResult id (.stop reason final) := by
        cases result
        rfl
      exact ⟨.stop reason final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_stopped_trace (evalValue fuel config environment)
          operands [] initial reason final (by simpa only [List.mapM] using mapResult)
        exact .stopped trace, output⟩
  | escape address carriers final =>
      simp only [mapResult] at result
      have output : outcome = recordOperandResult id (.escape address carriers final) := by
        cases result
        rfl
      exact ⟨.escape address carriers final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_escaped_trace (evalValue fuel config environment)
          operands [] initial address carriers final (by simpa only [List.mapM] using mapResult)
        exact .escaped trace, output⟩
  | jump target kind final =>
      simp only [mapResult] at result
      have output : outcome = recordOperandResult id (.jump target kind final) := by
        cases result
        rfl
      exact ⟨.jump target kind final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_jumped_trace (evalValue fuel config environment)
          operands [] initial target kind final (by simpa only [List.mapM] using mapResult)
        exact .jumped trace, output⟩

theorem evalValue_structLiteral_operand_cost_prefix {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {id : Goose.Core.StructId} {fields : TyList}
    {operands : List Expr} {initial : ExecutionState} {outcome : ExecutionStep Value}
    (cost : RecordOperandCost fuel config environment id fields operands initial outcome) :
    ∃ visited, SourcePrefix visited operands ∧ visited.length ≤ operands.length :=
  listMapM_operand_cost_prefix cost.loop

def runOperandLoop (action : α → EvalM Unit) (inputs : List α) : EvalM PUnit :=
  forIn inputs PUnit.unit (fun input _ => do
    action input
    pure (ForInStep.yield PUnit.unit))

inductive OperandLoopTrace (action : α → EvalM Unit) :
    List α → ExecutionState → ExecutionStep PUnit → List α → Prop
  | nil (state : ExecutionState) : OperandLoopTrace action [] state (.ok PUnit.unit state) []
  | cons {item : α} {rest visited : List α} {initial middle : ExecutionState}
      {outcome : ExecutionStep PUnit}
      (head : action item initial = .ok () middle)
      (tail : OperandLoopTrace action rest middle outcome visited) :
      OperandLoopTrace action (item :: rest) initial outcome (item :: visited)
  | stopped {item : α} {rest : List α} {initial final : ExecutionState} {reason : Goose.Core.Stop}
      (head : action item initial = .stop reason final) :
      OperandLoopTrace action (item :: rest) initial (.stop reason final) [item]
  | escaped {item : α} {rest : List α} {initial final : ExecutionState}
      {address : ExitAddress} {carriers : List Carrier}
      (head : action item initial = .escape address carriers final) :
      OperandLoopTrace action (item :: rest) initial (.escape address carriers final) [item]
  | jumped {item : α} {rest : List α} {initial final : ExecutionState}
      {target : Nat} {kind : JumpKind}
      (head : action item initial = .jump target kind final) :
      OperandLoopTrace action (item :: rest) initial (.jump target kind final) [item]

theorem runOperandLoop_trace (action : α → EvalM Unit) (inputs : List α)
    (initial : ExecutionState) (outcome : ExecutionStep PUnit)
    (result : runOperandLoop action inputs initial = outcome) :
    ∃ visited, OperandLoopTrace action inputs initial outcome visited := by
  induction inputs generalizing initial outcome with
  | nil =>
      simp only [runOperandLoop, List.forIn_nil, pure] at result
      cases result
      exact ⟨[], .nil initial⟩
  | cons item rest ih =>
      simp only [runOperandLoop, List.forIn_cons] at result
      cases head : action item initial with
      | ok value middle =>
          cases value
          simp only [bind, head, pure] at result
          obtain ⟨visited, trace⟩ := ih middle outcome result
          exact ⟨item :: visited, .cons head trace⟩
      | stop reason final =>
          simp only [bind, head] at result
          cases result
          exact ⟨[item], .stopped head⟩
      | escape address carriers final =>
          simp only [bind, head] at result
          cases result
          exact ⟨[item], .escaped head⟩
      | jump target kind final =>
          simp only [bind, head] at result
          cases result
          exact ⟨[item], .jumped head⟩

theorem operandLoopTrace_prefix {action : α → EvalM Unit} {inputs visited : List α}
    {initial : ExecutionState} {outcome : ExecutionStep PUnit}
    (trace : OperandLoopTrace action inputs initial outcome visited) : SourcePrefix visited inputs := by
  induction trace with
  | nil state => exact ⟨[], rfl⟩
  | cons head tail ih =>
      obtain ⟨suffix, rfl⟩ := ih
      exact ⟨suffix, rfl⟩
  | stopped head => exact ⟨_, rfl⟩
  | escaped head => exact ⟨_, rfl⟩
  | jumped head => exact ⟨_, rfl⟩

theorem operandLoopTrace_nonempty {action : α → EvalM Unit} {item : α} {rest visited : List α}
    {initial : ExecutionState} {outcome : ExecutionStep PUnit}
    (trace : OperandLoopTrace action (item :: rest) initial outcome visited) : visited ≠ [] := by
  cases trace <;> simp

theorem operandLoopTrace_success_visits_all {action : α → EvalM Unit} {inputs visited : List α}
    {initial : ExecutionState} {outcome : ExecutionStep PUnit}
    (trace : OperandLoopTrace action inputs initial outcome visited)
    (succeeded : ∃ final, outcome = .ok PUnit.unit final) : visited = inputs := by
  induction trace with
  | nil state => rfl
  | cons head tail ih => exact congrArg (List.cons _) (ih succeeded)
  | stopped head | escaped head | jumped head =>
      obtain ⟨final, impossible⟩ := succeeded
      cases impossible

inductive NonfixedArrayOperandTraversal (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) : List Expr → Prop
  | allocationInterrupted (outcome : ExecutionStep Goose.Core.DestinationId)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial = outcome)
      (interrupted : ∀ destination opened, outcome ≠ .ok destination opened) :
      NonfixedArrayOperandTraversal fuel config environment ty operands origin initial []
  | buildTimeout (destination : Goose.Core.DestinationId) (opened : ExecutionState)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial =
          .ok destination opened)
      (noFuel : fuel = 0) :
      NonfixedArrayOperandTraversal fuel config environment ty operands origin initial []
  | renewalInterrupted (elementFuel : Nat) (destination : Goose.Core.DestinationId)
      (opened : ExecutionState) (outcome : ExecutionStep Goose.Core.DestinationId)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial =
          .ok destination opened)
      (positive : fuel = elementFuel + 1)
      (renewal : liftConstruction origin (renewReceivingDestination destination) opened = outcome)
      (interrupted : ∀ current prepared, outcome ≠ .ok current prepared) :
      NonfixedArrayOperandTraversal fuel config environment ty operands origin initial []
  | destinationInterrupted (elementFuel : Nat) (destination current : Goose.Core.DestinationId)
      (opened prepared : ExecutionState) (outcome : ExecutionStep PendingDestination)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial =
          .ok destination opened)
      (positive : fuel = elementFuel + 1)
      (renewal : liftConstruction origin (renewReceivingDestination destination) opened = .ok current prepared)
      (lookup : getDestination current prepared = outcome)
      (interrupted : ∀ pending before, outcome ≠ .ok pending before) :
      NonfixedArrayOperandTraversal fuel config environment ty operands origin initial []
  | missingElement (elementFuel : Nat) (destination current : Goose.Core.DestinationId)
      (opened prepared before : ExecutionState) (pending : PendingDestination)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial =
          .ok destination opened)
      (positive : fuel = elementFuel + 1)
      (renewal : liftConstruction origin (renewReceivingDestination destination) opened = .ok current prepared)
      (lookup : getDestination current prepared = .ok pending before)
      (missing : elementType pending.capability.logicalType = none) :
      NonfixedArrayOperandTraversal fuel config environment ty operands origin initial []
  | operands (elementFuel : Nat) (destination current : Goose.Core.DestinationId)
      (opened prepared before : ExecutionState) (pending : PendingDestination) (element : Ty)
      (outcome : ExecutionStep PUnit) (visited : List Expr)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial =
          .ok destination opened)
      (positive : fuel = elementFuel + 1)
      (renewal : liftConstruction origin (renewReceivingDestination destination) opened = .ok current prepared)
      (lookup : getDestination current prepared = .ok pending before)
      (elementType : Goose.Construct.elementType pending.capability.logicalType = some element)
      (loop : runOperandLoop (fun operand => buildElement elementFuel config environment current element operand)
        operands before = outcome)
      (trace : OperandLoopTrace (fun operand => buildElement elementFuel config environment current element operand)
        operands before outcome visited) :
      NonfixedArrayOperandTraversal fuel config environment ty operands origin initial visited

theorem nonfixedArrayOperandTraversal_prefix {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {ty : Ty} {operands visited : List Expr}
    {origin : Goose.Core.OriginId} {initial : ExecutionState}
    (trace : NonfixedArrayOperandTraversal fuel config environment ty operands origin initial visited) :
    SourcePrefix visited operands := by
  cases trace with
  | operands _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ loop => exact operandLoopTrace_prefix loop
  | allocationInterrupted | buildTimeout | renewalInterrupted | destinationInterrupted | missingElement =>
      exact ⟨operands, rfl⟩

structure NonfixedArrayOperandCost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (outcome : ExecutionStep Value) where
  evaluation : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial = outcome
  nonfixed : ty.nonfixed = true
  traversal : ∃ visited, NonfixedArrayOperandTraversal fuel config environment ty operands origin initial visited

theorem evalValue_nonfixedArray_operand_cost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (outcome : ExecutionStep Value)
    (nonfixed : ty.nonfixed = true)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial = outcome) :
    NonfixedArrayOperandCost fuel config environment ty operands origin initial outcome := by
  refine ⟨result, nonfixed, ?_⟩
  cases allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
      (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial with
  | stop reason opened | escape address carriers opened | jump target kind opened =>
      exact ⟨[], .allocationInterrupted _ allocation (by intros; intro impossible; cases impossible)⟩
  | ok destination opened =>
      cases fuel with
      | zero => exact ⟨[], .buildTimeout destination opened allocation rfl⟩
      | succ elementFuel =>
          cases renewal : liftConstruction origin (renewReceivingDestination destination) opened with
          | stop reason prepared | escape address carriers prepared | jump target kind prepared =>
              exact ⟨[], .renewalInterrupted elementFuel destination opened _ allocation rfl renewal
                (by intros; intro impossible; cases impossible)⟩
          | ok current prepared =>
              cases lookup : getDestination current prepared with
              | stop reason before | escape address carriers before | jump target kind before =>
                  exact ⟨[], .destinationInterrupted elementFuel destination current opened prepared _ allocation
                    rfl renewal lookup (by intros; intro impossible; cases impossible)⟩
              | ok pending before =>
                  cases elementType : Goose.Construct.elementType pending.capability.logicalType with
                  | none => exact ⟨[], .missingElement elementFuel destination current opened prepared before
                      pending allocation rfl renewal lookup elementType⟩
                  | some element =>
                      obtain ⟨visited, trace⟩ := runOperandLoop_trace
                        (fun operand => buildElement elementFuel config environment current element operand)
                        operands before _ rfl
                      exact ⟨visited, .operands elementFuel destination current opened prepared before pending
                        element _ visited allocation rfl renewal lookup elementType rfl trace⟩

theorem evalValue_nonfixedArray_operand_cost_prefix {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {ty : Ty} {operands : List Expr}
    {origin : Goose.Core.OriginId} {initial : ExecutionState} {outcome : ExecutionStep Value}
    (cost : NonfixedArrayOperandCost fuel config environment ty operands origin initial outcome) :
    ∃ visited, SourcePrefix visited operands ∧ visited.length ≤ operands.length := by
  obtain ⟨visited, trace⟩ := cost.traversal
  exact ⟨visited, nonfixedArrayOperandTraversal_prefix trace,
    sourcePrefix_length_le (nonfixedArrayOperandTraversal_prefix trace)⟩

end Goose.Proofs.ConstructionExecution
