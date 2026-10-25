import Goose.Lower.Validation.SourceReadyObservationTypedControl
import Goose.Lower.Validation.SourceReadyObservationTypedLoopsWhile
import Goose.Lower.Validation.SourceReadyObservationTypedLoopsRangeFrames
import Goose.Lower.Validation.SourceReadyObservationTypedControlBoolean
import Goose.Lower.Validation.SourceReadyObservationTypedControlConditional
import Goose.Lower.Validation.SourceReadyObservationTypedBlocks
import Goose.Lower.Validation.SourceReadyObservationTypedControlStatements
import Goose.Lower.Validation.SourceReadyObservationTypedStatementsFrames
import Goose.Lower.Validation.SourceReadyObservationTypedArguments
import Goose.Lower.Validation.SourceReadyObservationTypedLists
import Goose.Lower.Validation.SourceReadyObservationOutput
import Goose.Lower.Validation.SourceReadyObservedCalls
import Goose.Lower.Validation.SourceReadyObservedReads
import Goose.Lower.Validation.SourceReadyObservedStopped
import Goose.Lower.Validation.SourceReadyObservationTypedValuesArithmetic
import Goose.Lower.Validation.SourceReadyObservationTypedValuesConstructors
import Goose.Lower.Validation.SourceReadyObservationTypedValuesOwners
import Goose.Lower.Validation.SourceReadyObservationTypedValuesReferences
import Goose.Lower.Validation.SourceReadyObservationTypedValuesSlices
import Goose.Lower.Validation.SourceReadyObservationTypedAccessPlaces
import Goose.Lower.Validation.SourceReadyObservationTypedAccessViews
import Goose.Lower.Validation.SourceReadyInductionCalls
import Goose.Lower.Validation.SourceReadyInductionPlaces
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyStopped
import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

mutual

theorem source_expression_ready (expression : Expr) (facts : SourceReadyFunction)
    {typingEnv : TEnv} {type : Ty} {start finish : Nat} {results : List Ty} {before : LS}
    (tables : SourceRootTables typingEnv facts.source)
    (source : Core.tyExpr typingEnv expression start = .ok (type, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (visible : before.cur.isSome = true → VisibleSlotsReady typingEnv facts.state) :
    ValueReadyAt facts.state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  apply value_ready_with_observations_of_live (SummaryPreservation.stopped_lowerExpr expression)
  intro live
  have slots := visible live
  cases expressionShape : expression with
  | lit integer number =>
    simp only [expressionShape] at source native extension allocated ⊢
    exact ⟨facts.frame.literal rfl extension allocated generated.live, ReadyCallObservations.literal integer number⟩
  | bool boolean =>
    simp only [expressionShape] at source native extension allocated ⊢
    exact ⟨facts.frame.boolean rfl extension allocated generated.live, ReadyCallObservations.boolean boolean⟩
  | read place =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply facts.read_with_observations tables source generated native slots extension allocated
    intro info childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | ref mutability place =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.reference facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | len view =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.length facts.frame source generated native extension allocated slots
    intro childType writable childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_view_ready view facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | un operation operand origin =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.unary facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready operand facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | not operand =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.logicalNot facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready operand facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | conv kind target operand origin =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.conversion facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready operand facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | fill target operand =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.fill facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready operand facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | pop place origin =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.pop facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | bin operation left right origin =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.binary facts.frame source generated native extension allocated slots
    · intro childType childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready left facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready right facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | cmp operation left right =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.comparison facts.frame source generated native extension allocated slots
    · intro childType childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready left facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready right facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | push place operand origin =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.push facts.frame source generated native extension allocated slots
    · intro childType childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready operand facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | call index arguments origin =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply facts.call_with_observations tables source generated native extension allocated slots
    intro implementation argsStart argsFinish argumentsSource arity argumentsGenerated argumentsNative argumentsExtension argumentsAllocated argumentsVisible
    apply SourceReadyArgumentObservations.typedArguments facts.frame argumentsSource arity argumentsGenerated argumentsNative argumentsExtension argumentsAllocated argumentsVisible
    · intro earlier operand later split childType childStart childFinish childSource
      have operandMember : Arg.byVal operand ∈ arguments := by rw [split]; simp
      have operandSize := Nat.lt_trans (by simp : sizeOf operand < sizeOf (Arg.byVal operand)) (List.sizeOf_lt_of_mem operandMember)
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready operand facts tables
        childSource childGenerated childNative childExtension childAllocated (fun _ => childVisible)
    · intro earlier mutability place later split info childStart childFinish childSource
      have placeMember : Arg.byRef mutability place ∈ arguments := by rw [split]; simp
      have placeSize := Nat.lt_trans (by simp +arith : sizeOf place < sizeOf (Arg.byRef mutability place)) (List.sizeOf_lt_of_mem placeMember)
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_place_ready place facts tables
        childSource childGenerated childNative childExtension childAllocated (fun _ => childVisible)
  | slice mutability view low high origin =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.slice facts.frame source generated native extension allocated slots
    · intro element writable childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_view_ready view facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_bound_ready low facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_bound_ready high facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | arrLit arrayType expressions =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.array facts.frame source generated native extension allocated slots
    intro childTypes childStart childFinish childrenSource childrenGenerated childrenNative childrenExtension childrenAllocated childrenVisible
    apply SourceReadyExpressionListObservations.typedExpressionsAs childrenSource childrenGenerated childrenNative childrenExtension childrenAllocated childrenVisible
    intro earlier expression later split childType expressionStart expressionFinish expressionSource
    have expressionMember : expression ∈ expressions := by rw [split]; simp
    have expressionSize := List.sizeOf_lt_of_mem expressionMember
    try dsimp only
    intro expressionGenerated expressionNative expressionExtension expressionAllocated expressionVisible
    exact source_expression_ready expression facts tables expressionSource expressionGenerated expressionNative
      expressionExtension expressionAllocated (fun _ => expressionVisible)
  | structLit structureType expressions =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.structure facts.frame source generated native extension allocated slots
    intro childTypes childStart childFinish childrenSource childrenGenerated childrenNative childrenExtension childrenAllocated childrenVisible
    apply SourceReadyExpressionListObservations.typedStructExpressions childrenSource childrenGenerated childrenNative childrenExtension childrenAllocated childrenVisible
    intro earlier expression later split childType expressionStart expressionFinish expressionSource
    have expressionMember : expression ∈ expressions := by rw [split]; simp
    have expressionSize := List.sizeOf_lt_of_mem expressionMember
    try dsimp only
    intro expressionGenerated expressionNative expressionExtension expressionAllocated expressionVisible
    exact source_expression_ready expression facts tables expressionSource expressionGenerated expressionNative
      expressionExtension expressionAllocated (fun _ => expressionVisible)
  | and left right =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply facts.frame.observedTypedShortCircuit (isAnd := true) source generated native extension allocated slots
    · intro next checked childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready left facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro next checked
      try dsimp only
      intro testedLive childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready right facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | or left right =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply facts.frame.observedTypedShortCircuit (isAnd := false) source generated native extension allocated slots
    · intro next checked childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready left facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro next checked
      try dsimp only
      intro testedLive childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready right facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | ifE condition yes no =>
    simp only [expressionShape] at source native extension allocated ⊢
    apply facts.frame.observedTypedIfExpression source generated native extension allocated slots
    · intro next checked childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready condition facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro next last checked
      try dsimp only
      intro testedLive childGenerated childNative childExtension childAllocated childVisible
      have pair := source_block_ready yes facts (typingEnv := Core.exprEnv typingEnv)
        (sourcePre := []) (pre := []) (loop := none) (want := true)
        ⟨tables.moduleEq, tables.variablesEq⟩ checked childGenerated trivial childNative childExtension childAllocated
        (fun _ => childVisible) (by intro _ _ member; cases member)
        (by intro _ _ _ member; cases member) (by intro _ _ _ _ member; cases member)
        (by intro _ _ _ _ same; cases same)
      exact ⟨⟨pair.1.1, pair.1.2 rfl⟩, pair.2⟩
    · intro next checked
      try dsimp only
      intro testedLive childGenerated childNative childExtension childAllocated childVisible
      have pair := source_block_ready no facts (typingEnv := Core.exprEnv typingEnv)
        (sourcePre := []) (pre := []) (loop := none) (want := true)
        ⟨tables.moduleEq, tables.variablesEq⟩ checked childGenerated trivial childNative childExtension childAllocated
        (fun _ => childVisible) (by intro _ _ member; cases member)
        (by intro _ _ _ member; cases member) (by intro _ _ _ _ member; cases member)
        (by intro _ _ _ _ same; cases same)
      exact ⟨⟨pair.1.1, pair.1.2 rfl⟩, pair.2⟩
  | blockE body =>
    simp only [expressionShape] at source native extension allocated ⊢
    have pair := source_block_ready body facts (typingEnv := Core.exprEnv typingEnv)
      (sourcePre := []) (pre := []) (loop := none) (want := true)
      ⟨tables.moduleEq, tables.variablesEq⟩ source generated trivial native extension allocated
      (fun _ => slots) (by intro _ _ member; cases member)
      (by intro _ _ _ member; cases member) (by intro _ _ _ _ member; cases member)
      (by intro _ _ _ _ same; cases same)
    exact ⟨⟨pair.1.1, pair.1.2 rfl⟩, pair.2⟩
termination_by sizeOf expression
decreasing_by all_goals (simp only [expressionShape] <;> simp_wf <;> omega)

theorem source_place_ready (place : Place) (facts : SourceReadyFunction)
    {typingEnv : TEnv} {info : PlaceInfo} {start finish : Nat} {results : List Ty} {before : LS}
    (tables : SourceRootTables typingEnv facts.source)
    (source : Core.tyPlace typingEnv place start = .ok (info, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (visible : before.cur.isSome = true → VisibleSlotsReady typingEnv facts.state) :
    ValueReadyAt facts.state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  apply value_ready_with_observations_of_live (SummaryPreservation.stopped_lowerPlace place)
  intro live
  have slots := visible live
  cases placeShape : place with
  | var variableId =>
    simp only [placeShape] at source native extension allocated ⊢
    exact ⟨facts.frame.variablePlace rfl extension allocated generated.live, ReadyCallObservations.placeVariable variableId⟩
  | global globalId =>
    simp only [placeShape] at source native extension allocated ⊢
    exact ⟨facts.frame.globalPlace rfl extension allocated generated.live, ReadyCallObservations.placeGlobal globalId⟩
  | deref expression =>
    simp only [placeShape] at source native extension allocated ⊢
    apply facts.dereference_with_observations source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | field owner index =>
    simp only [placeShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.field facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_place_ready owner facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | elem view index origin =>
    simp only [placeShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.element facts.frame source generated native extension allocated slots
    · intro element writable childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_view_ready view facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType childStart childFinish childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready index facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
termination_by sizeOf place
decreasing_by all_goals (simp only [placeShape] <;> simp_wf <;> omega)

theorem source_view_ready (view : View) (facts : SourceReadyFunction)
    {typingEnv : TEnv} {element : Ty} {writable : Bool} {start finish : Nat} {results : List Ty} {before : LS}
    (tables : SourceRootTables typingEnv facts.source)
    (source : Core.tyView typingEnv view start = .ok ((element, writable), finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (visible : before.cur.isSome = true → VisibleSlotsReady typingEnv facts.state) :
    ValueReadyAt facts.state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  apply value_ready_with_observations_of_live (SummaryPreservation.stopped_lowerView view)
  intro live
  have slots := visible live
  cases viewShape : view with
  | of place =>
    simp only [viewShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.viewOf facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | val expression =>
    simp only [viewShape] at source native extension allocated ⊢
    apply SourceReadyValueObservations.viewValue facts.frame source generated native extension allocated slots
    intro childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
termination_by sizeOf view
decreasing_by all_goals (simp only [viewShape] <;> simp_wf <;> omega)

theorem source_bound_ready (bound : Bound) (facts : SourceReadyFunction)
    {typingEnv : TEnv} {start finish : Nat} {results : List Ty} {before : LS}
    (tables : SourceRootTables typingEnv facts.source)
    (source : Core.tyBound typingEnv bound start = .ok ((), finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerBound bound (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerBound bound (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerBound bound (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (visible : before.cur.isSome = true → VisibleSlotsReady typingEnv facts.state) :
    BoundaryReadyAt facts.state bound (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerBound bound (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  cases current : before.cur with
  | none =>
    have stopped := SummaryPreservation.stopped_lowerBound bound
      (lowerEnv typingEnv.mod typingEnv.vars results) before _ _ rfl current
    exact ⟨⟨.of_blocks stopped.2.1, by intro active; exact Bool.noConfusion ((congrArg Option.isSome stopped.1).symm.trans active)⟩, .of_blocks stopped.2.1⟩
  | some block =>
    apply SourceReadyValueObservations.boundary source generated native extension allocated (visible (by simp [current]))
    intro expression shape childType childStart childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    rcases shape with shape | shape
    all_goals have smaller : sizeOf expression < sizeOf bound := by rw [shape]; simp
    all_goals exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated (fun _ => childVisible)
termination_by sizeOf bound
decreasing_by all_goals omega

theorem source_statements_ready (statements : List Stmt) (facts : SourceReadyFunction)
    {typingEnv output : TEnv} {scope start finish : Nat} {results : List Ty} {before : LS} {loop : Option LoopCtx}
    (tables : SourceRootTables typingEnv facts.source)
    (source : Core.tyStmts typingEnv scope statements start = .ok (output, finish))
    (generated : GeneratedBuilderState before) (targets : LoopBuilderTargets loop before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerStmts loop statements (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmts loop statements (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerStmts loop statements (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (visible : before.cur.isSome = true → VisibleSlotsReady typingEnv facts.state)
    (counter : ∀ context header integer index, loop = some context → context.cont = .next header integer index →
      flowAt facts.state.values index ≠ .pending) :
    (EmitsOnly (ReadyOperands facts.state) before
      (lowerStmts loop statements (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmts loop statements (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output facts.state)) ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerStmts loop statements (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  cases statementsShape : statements with
  | nil =>
    simp only [statementsShape] at source native extension allocated ⊢
    have same : output = typingEnv := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    subst output
    exact ⟨⟨.refl _ _, visible⟩, .refl _ _⟩
  | cons statement rest =>
    simp only [statementsShape] at source native extension allocated ⊢
    cases current : before.cur with
    | none =>
      have stopped := SummaryPreservation.stopped_lowerStmts loop (statement :: rest)
        (lowerEnv typingEnv.mod typingEnv.vars results) before _ _ rfl current
      exact ⟨⟨.of_blocks stopped.2.1, by intro active; exact Bool.noConfusion ((congrArg Option.isSome stopped.1).symm.trans active)⟩, .of_blocks stopped.2.1⟩
    | some block =>
      obtain ⟨middle, next, firstSource, restSource⟩ := tyStmts_cons_children source
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let first := lowerStmt loop statement env before
      let remaining := lowerStmts loop rest env first.2
      have run : lowerStmts loop (statement :: rest) env before = remaining := by
        simp only [lowerStmts, bind_run, isLive_run current, reduceIte]
        rfl
      have restNative : SummaryPreservation.NativeRows facts.types remaining.2 := by
        rw [← run]
        exact native
      have restExtension : remaining.2.Ext facts.completed := by rw [← run]; exact extension
      have restAllocated : remaining.2.vals.size ≤ facts.completed.vals.size := by rw [← run]; exact allocated
      have tailAdvance : first.2.Adv remaining.2 := advB_lowerStmts loop rest env first.2 _ _ rfl
      have firstNative := restNative.of_prefix (types_lowerStmts loop rest env first.2 _ _ rfl)
      have head := source_statement_ready statement facts tables firstSource generated targets firstNative
        (tailAdvance.ext.trans restExtension) (Nat.le_trans tailAdvance.vals restAllocated)
        (by simp [current]) (visible (by simp [current])) counter
      have changed := tyStmt_tables statement firstSource
      have middleTables : SourceRootTables middle facts.source :=
        ⟨tables.moduleEq.trans changed.1.symm, tables.variablesEq.trans changed.2.1.symm⟩
      have envEq : lowerEnv middle.mod middle.vars results = env := by simp only [changed.1, changed.2.1, env]
      have tail := source_statements_ready rest facts middleTables restSource
        (generated.lowerStmt loop statement targets rfl)
        (targets.mono (advB_lowerStmt loop statement env before _ _ rfl).ext.1)
        (by rw [envEq]; exact restNative) (by rw [envEq]; exact restExtension)
        (by rw [envEq]; exact restAllocated) head.1.2 counter
      rw [envEq] at tail
      change (EmitsOnly (ReadyOperands facts.state) before (lowerStmts loop (statement :: rest) env before).2 ∧ _) ∧ _
      rw [run]
      exact ⟨⟨head.1.1.trans tail.1.1, tail.1.2⟩, head.2.trans tail.2⟩
termination_by sizeOf statements
decreasing_by all_goals (simp only [statementsShape] <;> simp_wf <;> omega)

theorem source_block_ready (body : Core.Block) (facts : SourceReadyFunction)
    {typingEnv : TEnv} {type : Ty} {start finish : Nat} {results : List Ty} {before : LS}
    {sourcePre : List (VarId × Ty)} {pre : List (SlotId × ValueId × OriginId)}
    {loop : Option LoopCtx} {want : Bool}
    (tables : SourceRootTables typingEnv facts.source)
    (source : Core.tyBlock typingEnv sourcePre body start = .ok (type, finish))
    (generated : GeneratedBuilderState before) (targets : LoopBuilderTargets loop before)
    (native : SummaryPreservation.NativeRows facts.types
      (Lower.lowerBlock loop pre want body (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (Lower.lowerBlock loop pre want body (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (Lower.lowerBlock loop pre want body (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (visible : before.cur.isSome = true → VisibleSlotsReady typingEnv facts.state)
    (preCorrespondence : ∀ slot type, (slot, type) ∈ sourcePre → ∃ input origin, (slot, input, origin) ∈ pre)
    (preSlots : ∀ slot input origin, (slot, input, origin) ∈ pre → slot < facts.func.slots.size)
    (preReady : before.cur.isSome = true → ∀ slot input origin, (slot, input, origin) ∈ pre →
      flowAt facts.state.values input ≠ .pending)
    (counter : ∀ context header integer index, loop = some context → context.cont = .next header integer index →
      flowAt facts.state.values index ≠ .pending) :
    (EmitsOnly (ReadyOperands facts.state) before
      (Lower.lowerBlock loop pre want body (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      (want = true → (Lower.lowerBlock loop pre want body (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        flowAt facts.state.values (Lower.lowerBlock loop pre want body (lowerEnv typingEnv.mod typingEnv.vars results) before).1 ≠ .pending)) ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (Lower.lowerBlock loop pre want body (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  cases current : before.cur with
  | none =>
    have stopped := SummaryPreservation.stopped_lowerBlock loop pre want body
      (lowerEnv typingEnv.mod typingEnv.vars results) before _ _ rfl current
    exact ⟨⟨.of_blocks stopped.2.1, by intro wanted live; simp [stopped.1] at live⟩, .of_blocks stopped.2.1⟩
  | some block =>
    cases bodyShape : body with
    | mk scope statements value =>
      simp only [bodyShape] at source native extension allocated ⊢
      refine (fun pair => And.intro pair.1.1 pair.2)
        (facts.frame.observedTypedBlock source generated targets native extension allocated
          (visible (by simp [current])) preCorrespondence preSlots preReady counter ?_ ?_)
      · intro declared output statementStart valueStart declaration checked
        try dsimp only
        intro initializedGenerated initializedTargets statementsNative statementsExtension statementsAllocated declaredVisible statementsCounter
        have changed := declarePre_tables sourcePre declaration
        have declaredTables : SourceRootTables declared facts.source :=
          ⟨tables.moduleEq.trans changed.1.symm, tables.variablesEq.trans changed.2.1.symm⟩
        have envEq : lowerEnv declared.mod declared.vars results = lowerEnv typingEnv.mod typingEnv.vars results := by
          simp only [changed.1, changed.2.1]
        have result := source_statements_ready statements facts declaredTables checked initializedGenerated initializedTargets
          (by rw [envEq]; exact statementsNative) (by rw [envEq]; exact statementsExtension)
          (by rw [envEq]; exact statementsAllocated) declaredVisible statementsCounter
        simpa only [envEq] using result
      · intro declared output statementStart valueStart expression declaration checked selected expressionSource
        try dsimp only
        intro executedGenerated expressionNative expressionExtension expressionAllocated outputVisible
        have expressionSize : sizeOf expression < sizeOf value := by rw [selected]; simp
        have declaredChanged := declarePre_tables sourcePre declaration
        have outputChanged := tyStmts_tables statements checked
        have outputTables : SourceRootTables output facts.source :=
          ⟨tables.moduleEq.trans (outputChanged.1.trans declaredChanged.1).symm,
            tables.variablesEq.trans (outputChanged.2.1.trans declaredChanged.2.1).symm⟩
        have envEq : lowerEnv output.mod output.vars results = lowerEnv typingEnv.mod typingEnv.vars results := by
          simp only [outputChanged.1, outputChanged.2.1, declaredChanged.1, declaredChanged.2.1]
        have result := source_expression_ready expression facts outputTables expressionSource executedGenerated
          (by rw [envEq]; exact expressionNative) (by rw [envEq]; exact expressionExtension)
          (by rw [envEq]; exact expressionAllocated) outputVisible
        simpa only [envEq] using result
termination_by sizeOf body
decreasing_by all_goals (simp only [bodyShape] <;> simp_wf <;> omega)

theorem source_statement_ready (statement : Stmt) (facts : SourceReadyFunction)
    {typingEnv output : TEnv} {scope start finish : Nat} {results : List Ty} {before : LS} {loop : Option LoopCtx}
    (tables : SourceRootTables typingEnv facts.source)
    (source : Core.tyStmt typingEnv scope statement start = .ok (output, finish))
    (generated : GeneratedBuilderState before) (targets : LoopBuilderTargets loop before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerStmt loop statement (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop statement (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerStmt loop statement (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (live : before.cur.isSome = true)
    (visible : VisibleSlotsReady typingEnv facts.state)
    (counter : ∀ context header integer index, loop = some context → context.cont = .next header integer index →
      flowAt facts.state.values index ≠ .pending) :
    (EmitsOnly (ReadyOperands facts.state) before
      (lowerStmt loop statement (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop statement (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output facts.state)) ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerStmt loop statement (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  cases statementShape : statement with
  | abort message origin =>
    simp only [statementShape] at source native extension allocated ⊢
    exact ⟨typed_ready_abort source visible, ReadyCallObservations.statement_abort message origin⟩
  | brk origin =>
    simp only [statementShape] at source native extension allocated ⊢
    exact ⟨typed_ready_break source visible, ReadyCallObservations.statement_break origin⟩
  | cont origin =>
    simp only [statementShape] at source native extension allocated ⊢
    exact ⟨facts.frame.typedContinue source generated extension allocated visible
      (fun context same header integer index next _ => counter context header integer index same next),
      ReadyCallObservations.statement_continue origin⟩
  | ret expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    cases expressionShape : expression with
    | none =>
      simp only [expressionShape] at source native extension allocated ⊢
      exact ⟨typed_ready_return_none source visible, ReadyCallObservations.statement_return_none origin⟩
    | some expression =>
      simp only [expressionShape] at source native extension allocated ⊢
      apply SourceReadyStatementObservations.returnSome facts.frame source generated native extension allocated visible
      intro childType childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | letS slot expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.letS facts.frame source generated (facts.sourceSlotCount tables) native extension allocated visible
    intro childType childFinish childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | rebind slot expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.rebind facts.frame source generated native extension allocated visible
    intro childType childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | expr expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.expression source generated native extension allocated visible
    intro childType childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | assertS expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.assertS source generated native extension allocated visible
    intro  childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | exit expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.exit source generated native extension allocated visible
    intro integer childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | clear place origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.clear source generated native extension allocated visible
    intro info childSource
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | assign place expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.assign source generated native extension allocated visible
    · intro info next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | popN place expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.popN source generated native extension allocated visible
    · intro info next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro integer next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | append place view origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.append source generated native extension allocated visible
    · intro info next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro element writable next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_view_ready view facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | assignWhole place expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.assignWhole source generated native extension allocated visible
    · intro info next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | assignOp operation place expression origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.assignOp facts.frame source generated native extension allocated visible
    · intro info next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro integer next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | resize place size fill origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.resize source generated native extension allocated visible
    · intro info next childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_place_ready place facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro integer next last childSource
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready size facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro expression childType next selected childSource
      have fillSize : sizeOf expression < sizeOf fill := by rw [selected]; simp
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
  | print arguments origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply SourceReadyStatementObservations.print source generated native extension allocated visible
    intro earlier expression later childType next last split prefixSource childSource
    have expressionMember : PrintArg.expr expression ∈ arguments := by rw [split]; simp
    have expressionSize := Nat.lt_trans (by simp : sizeOf expression < sizeOf (PrintArg.expr expression)) (List.sizeOf_lt_of_mem expressionMember)
    try dsimp only
    intro childGenerated childNative childExtension childAllocated childVisible
    exact source_expression_ready expression facts tables childSource childGenerated childNative childExtension childAllocated
      (fun _ => childVisible)
  | ifS condition yes no origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply facts.frame.observedTypedIfStatement source generated targets native extension allocated visible counter
    · intro next checked childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready condition facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType next last initial checked childGenerated childTargets childNative childExtension childAllocated childVisible childCounter
      have pair := source_block_ready yes facts tables checked childGenerated childTargets childNative childExtension childAllocated
        (fun _ => childVisible) (by intro _ _ member; cases member)
        (by intro _ _ _ member; cases member) (by intro _ _ _ _ member; cases member) childCounter
      exact ⟨pair.1.1, pair.2⟩
    · intro body childType next initial selected checked childGenerated childTargets childNative childExtension childAllocated childVisible childCounter
      have bodySize : sizeOf body < sizeOf no := by rw [selected]; simp
      have pair := source_block_ready body facts tables checked childGenerated childTargets childNative childExtension childAllocated
        (fun _ => childVisible) (by intro _ _ member; cases member)
        (by intro _ _ _ member; cases member) (by intro _ _ _ _ member; cases member) childCounter
      exact ⟨pair.1.1, pair.2⟩
  | «while» condition body origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply facts.frame.observedTypedWhileStatement source generated native extension allocated visible
    · intro next checked
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready condition facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType next context initial checked childGenerated childTargets childNative childExtension childAllocated childVisible childCounter
      have pair := source_block_ready body facts
        (typingEnv := { typingEnv with loops := typingEnv.loops + 1 })
        ⟨tables.moduleEq, tables.variablesEq⟩ checked childGenerated childTargets childNative childExtension childAllocated
        (fun _ => childVisible) (by intro _ _ member; cases member)
        (by intro _ _ _ member; cases member) (by intro _ _ _ _ member; cases member)
        (by intro selected header integer index same next; cases same; exact childCounter header integer index next)
      exact ⟨pair.1.1, pair.2⟩
  | forRange slot low high body origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply facts.frame.observedTypedRangeFrames source generated (facts.sourceSlotCount tables) native extension allocated visible
    · intro integer next last checked childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready low facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro integer next last checked
      try dsimp only
      intro childGenerated childNative childExtension childAllocated childVisible
      exact source_expression_ready high facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro childType next context pre initial checked childGenerated childTargets childNative childExtension childAllocated childVisible preSlots preReady childCounter
      have pair := source_block_ready body facts
        (typingEnv := { typingEnv with loops := typingEnv.loops + 1, visible := slot :: typingEnv.visible })
        ⟨tables.moduleEq, tables.variablesEq⟩ checked childGenerated childTargets childNative childExtension childAllocated
        (fun _ => childVisible) (by intro _ _ member; cases member) preSlots (fun _ => preReady)
        (by intro selected header integer index same next; cases same; exact childCounter header integer index next)
      exact ⟨pair.1.1, pair.2⟩
  | forEach slot indexSlot view byReference body origin =>
    simp only [statementShape] at source native extension allocated ⊢
    apply facts.frame.observedTypedEachFrames source generated (facts.readable tables) (facts.sourceSlotCount tables)
      native extension allocated visible
    · intro element writable next last checked childGenerated childNative childExtension childAllocated childVisible
      exact source_view_ready view facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
    · intro place info next last selected checked childGenerated childNative childExtension childAllocated childVisible
      have placeSize : sizeOf place < sizeOf view := by rw [selected]; simp
      have pair := source_place_ready place facts tables checked childGenerated childNative childExtension childAllocated
        (fun _ => childVisible)
      exact pair
    · intro childType next context pre initial checked childGenerated childTargets childNative childExtension childAllocated childVisible preSlots preReady childCounter
      have pair := source_block_ready body facts
        (typingEnv := { typingEnv with loops := typingEnv.loops + 1, visible := slot :: indexSlot.toList ++ typingEnv.visible })
        ⟨tables.moduleEq, tables.variablesEq⟩ checked childGenerated childTargets childNative childExtension childAllocated
        (fun _ => childVisible) (by intro _ _ member; cases member) preSlots (fun _ => preReady)
        (by intro selected header integer index same next; cases same; exact childCounter header integer index next)
      exact ⟨pair.1.1, pair.2⟩
termination_by sizeOf statement
decreasing_by all_goals (simp only [statementShape] <;> (try simp only [expressionShape]) <;> simp_wf <;> omega)

end

#print axioms source_expression_ready
#print axioms source_place_ready
#print axioms source_view_ready
#print axioms source_bound_ready
#print axioms source_statements_ready
#print axioms source_block_ready
#print axioms source_statement_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
