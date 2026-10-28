import Goose.Proofs.ConstructionGhostMaterialization

namespace Goose.Proofs.ConstructionGhostArguments
open Goose.Construct Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionGhostMaterialization

def argumentValue (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parameterVars : Array LocalVar) (parameter : Param) (argument : Arg) : EvalM Value := do
  match argument with
  | .byRef _ place => pure (.ref (← evalPlace fuel config environment place))
  | .byVal operand => evalValue fuel config environment operand
  | .construct operand =>
      let some localVar := parameterVars[parameter.var]? | fault .unbound
      let materialized ← materializeProducer fuel ⟨config.module, environment.vars⟩ operand
        (evalValue fuel config environment operand)
      let carrier ← match materialized with
        | some values => do
            let destination ← materializedDestination fuel config.layout environment.act localVar.ty
              (expressionOrigin operand) values.size (.fixed values)
            publishCarriers (expressionOrigin operand) [.completed destination]
            pure (Carrier.completed destination)
        | none =>
            constructLocal ⟨config.module, environment.vars⟩ environment.act localVar.ty (expressionOrigin operand) operand
              (fun destination => buildExpr fuel config environment destination operand)
      carrierValue carrier

def constructedArgumentContinuation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : LocalVar) (operand : Expr) (result : ExecutionStep (Option (Array Value))) : ExecutionStep Value :=
  match result with
  | .ok materialized state => (do
      let carrier ← match materialized with
        | some values => do
            let destination ← materializedDestination fuel config.layout environment.act localVar.ty
              (expressionOrigin operand) values.size (.fixed values)
            publishCarriers (expressionOrigin operand) [.completed destination]
            pure (Carrier.completed destination)
        | none =>
            constructLocal ⟨config.module, environment.vars⟩ environment.act localVar.ty (expressionOrigin operand) operand
              (fun destination => buildExpr fuel config environment destination operand)
      carrierValue carrier) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem constructedArgument_execution (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parameterVars : Array LocalVar) (parameter : Param) (operand : Expr) (before : ExecutionState)
    (localVar : LocalVar) (found : parameterVars[parameter.var]? = some localVar) :
    argumentValue fuel config environment parameterVars parameter (.construct operand) before =
      constructedArgumentContinuation fuel config environment localVar operand
        (materializeProducer fuel ⟨config.module, environment.vars⟩ operand
          (evalValue fuel config environment operand) before) := by
  simp only [argumentValue, found, bind, constructedArgumentContinuation]
  cases materializeProducer fuel ⟨config.module, environment.vars⟩ operand
    (evalValue fuel config environment operand) before <;> rfl

#print axioms constructedArgument_execution
structure ArgumentInvocation where
  activation : Goose.Core.ActId
  ordinal : Nat
  fuel : Nat
  parameter : Param
  argument : Arg
  before : ExecutionState
  outcome : ExecutionStep Value

def prependValue (value : Value) : ExecutionStep (List Value) → ExecutionStep (List Value)
  | .ok values state => .ok (value :: values) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

inductive ArgumentReplay (config : EvalConfig) (environment : RuntimeActivation) (parameterVars : Array LocalVar) :
    Nat → Nat → List Param → List Arg → ExecutionState → ExecutionStep (List Value) → List ArgumentInvocation → Prop
  | timeout (offset : Nat) (parameters : List Param) (arguments : List Arg) (state : ExecutionState) :
      ArgumentReplay config environment parameterVars 0 offset parameters arguments state (.stop .timeout state) []
  | done (fuel offset : Nat) (state : ExecutionState) :
      ArgumentReplay config environment parameterVars (fuel + 1) offset [] [] state (.ok [] state) []
  | arityLeft (fuel offset : Nat) (parameter : Param) (parameters : List Param) (state : ExecutionState) :
      ArgumentReplay config environment parameterVars (fuel + 1) offset (parameter :: parameters) [] state (.stop (.fault .arity) state) []
  | arityRight (fuel offset : Nat) (argument : Arg) (arguments : List Arg) (state : ExecutionState) :
      ArgumentReplay config environment parameterVars (fuel + 1) offset [] (argument :: arguments) state (.stop (.fault .arity) state) []
  | next {fuel offset : Nat} {parameter : Param} {parameters : List Param} {argument : Arg} {arguments : List Arg}
      {before middle : ExecutionState} {value : Value} {outcome : ExecutionStep (List Value)} {visits : List ArgumentInvocation}
      (head : argumentValue fuel config environment parameterVars parameter argument before = .ok value middle)
      (tail : ArgumentReplay config environment parameterVars fuel (offset + 1) parameters arguments middle outcome visits) :
      ArgumentReplay config environment parameterVars (fuel + 1) offset (parameter :: parameters) (argument :: arguments) before
        (prependValue value outcome)
        (⟨environment.act, offset, fuel, parameter, argument, before, .ok value middle⟩ :: visits)
  | stopped {fuel offset : Nat} {parameter : Param} {parameters : List Param} {argument : Arg} {arguments : List Arg}
      {before after : ExecutionState} {reason : Goose.Core.Stop}
      (head : argumentValue fuel config environment parameterVars parameter argument before = .stop reason after) :
      ArgumentReplay config environment parameterVars (fuel + 1) offset (parameter :: parameters) (argument :: arguments) before
        (.stop reason after) [⟨environment.act, offset, fuel, parameter, argument, before, .stop reason after⟩]
  | escaped {fuel offset : Nat} {parameter : Param} {parameters : List Param} {argument : Arg} {arguments : List Arg}
      {before after : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
      (head : argumentValue fuel config environment parameterVars parameter argument before = .escape address carriers after) :
      ArgumentReplay config environment parameterVars (fuel + 1) offset (parameter :: parameters) (argument :: arguments) before
        (.escape address carriers after) [⟨environment.act, offset, fuel, parameter, argument, before, .escape address carriers after⟩]
  | jumped {fuel offset : Nat} {parameter : Param} {parameters : List Param} {argument : Arg} {arguments : List Arg}
      {before after : ExecutionState} {target : Nat} {kind : JumpKind}
      (head : argumentValue fuel config environment parameterVars parameter argument before = .jump target kind after) :
      ArgumentReplay config environment parameterVars (fuel + 1) offset (parameter :: parameters) (argument :: arguments) before
        (.jump target kind after) [⟨environment.act, offset, fuel, parameter, argument, before, .jump target kind after⟩]

theorem evalArguments_step (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parameterVars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (argument : Arg) (arguments : List Arg) (before : ExecutionState) :
    evalArguments (fuel + 1) config environment parameterVars (parameter :: parameters) (argument :: arguments) before =
      (do let value ← argumentValue fuel config environment parameterVars parameter argument
          pure (value :: (← evalArguments fuel config environment parameterVars parameters arguments))) before := by
  cases argument <;> simp [evalArguments, argumentValue, bind, pure]
  all_goals cases found : parameterVars[parameter.var]? <;> try simp_all [bind, pure]
  all_goals repeat' (split <;> try simp_all [bind, pure])

theorem argumentReplay_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parameterVars : Array LocalVar) (offset : Nat) (parameters : List Param) (arguments : List Arg) (before : ExecutionState) :
    ∃ visits, ArgumentReplay config environment parameterVars fuel offset parameters arguments before
      (evalArguments fuel config environment parameterVars parameters arguments before) visits := by
  induction fuel generalizing offset parameters arguments before with
  | zero => simpa [evalArguments, timeout, EvalM.stop] using
      (show ∃ visits, ArgumentReplay config environment parameterVars 0 offset parameters arguments before (.stop .timeout before) visits from
        ⟨[], .timeout offset parameters arguments before⟩)
  | succ fuel ih =>
    cases parameters with
    | nil =>
      cases arguments with
      | nil => simpa [evalArguments, pure] using
          (show ∃ visits, ArgumentReplay config environment parameterVars (fuel + 1) offset [] [] before (.ok [] before) visits from
            ⟨[], .done fuel offset before⟩)
      | cons argument arguments => simpa [evalArguments, fault, EvalM.stop] using
          (show ∃ visits, ArgumentReplay config environment parameterVars (fuel + 1) offset [] (argument :: arguments) before (.stop (.fault .arity) before) visits from
            ⟨[], .arityRight fuel offset argument arguments before⟩)
    | cons parameter parameters =>
      cases arguments with
      | nil => simpa [evalArguments, fault, EvalM.stop] using
          (show ∃ visits, ArgumentReplay config environment parameterVars (fuel + 1) offset (parameter :: parameters) [] before (.stop (.fault .arity) before) visits from
            ⟨[], .arityLeft fuel offset parameter parameters before⟩)
      | cons argument arguments =>
        rw [evalArguments_step fuel config environment parameterVars parameter parameters argument arguments before]
        cases head : argumentValue fuel config environment parameterVars parameter argument before with
        | ok value middle =>
          obtain ⟨visits, tail⟩ := ih (offset + 1) parameters arguments middle
          simp only [bind, head, pure]
          cases result : evalArguments fuel config environment parameterVars parameters arguments middle <;>
            simp only [result] at tail ⊢ <;> exact ⟨_, .next head tail⟩
        | stop reason after => simp only [bind, head]; exact ⟨_, .stopped head⟩
        | escape address carriers after => simp only [bind, head]; exact ⟨_, .escaped head⟩
        | jump target kind after => simp only [bind, head]; exact ⟨_, .jumped head⟩

theorem ArgumentReplay.sound
    (replay : ArgumentReplay config environment parameterVars fuel offset parameters arguments before outcome visits) :
    evalArguments fuel config environment parameterVars parameters arguments before = outcome := by
  induction replay with
  | timeout => simp [evalArguments, Goose.Construct.timeout, EvalM.stop]
  | done => simp [evalArguments, pure]
  | arityLeft | arityRight => simp [evalArguments, fault, EvalM.stop]
  | @next fuel offset parameter parameters argument arguments before middle value outcome visits head tail ih =>
    rw [evalArguments_step fuel config environment parameterVars parameter parameters argument arguments before]
    simp only [bind, head]
    rw [ih]
    cases outcome <;> rfl
  | @stopped fuel offset parameter parameters argument arguments before after reason head =>
    rw [evalArguments_step fuel config environment parameterVars parameter parameters argument arguments before]
    simp only [bind, head]
  | @escaped fuel offset parameter parameters argument arguments before after address carriers head =>
    rw [evalArguments_step fuel config environment parameterVars parameter parameters argument arguments before]
    simp only [bind, head]
  | @jumped fuel offset parameter parameters argument arguments before after target kind head =>
    rw [evalArguments_step fuel config environment parameterVars parameter parameters argument arguments before]
    simp only [bind, head]

theorem ArgumentReplay.sourceOrder
    (replay : ArgumentReplay config environment parameterVars fuel offset parameters arguments before outcome visits) :
    visits.map ArgumentInvocation.argument = arguments.take visits.length := by
  induction replay <;> simp_all

theorem ArgumentReplay.ordinals
    (replay : ArgumentReplay config environment parameterVars fuel offset parameters arguments before outcome visits) :
    visits.map ArgumentInvocation.ordinal = List.range' offset visits.length := by
  induction replay with
  | timeout | done | arityLeft | arityRight => rfl
  | next head tail ih => simpa [List.range'_succ] using congrArg (offset :: ·) ih
  | stopped | escaped | jumped => simp [List.range'_succ]

theorem ArgumentReplay.once
    (replay : ArgumentReplay config environment parameterVars fuel offset parameters arguments before outcome visits) :
    (visits.map ArgumentInvocation.ordinal).Nodup := by
  rw [replay.ordinals]
  exact List.nodup_range'

theorem ArgumentReplay.visitExecutes
    (replay : ArgumentReplay config environment parameterVars fuel offset parameters arguments before outcome visits)
    (visit : ArgumentInvocation) (member : visit ∈ visits) :
    argumentValue visit.fuel config environment parameterVars visit.parameter visit.argument visit.before = visit.outcome := by
  induction replay with
  | timeout | done | arityLeft | arityRight => simp at member
  | next head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst visit; exact head
    · exact ih later
  | stopped head | escaped head | jumped head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact head

theorem ArgumentReplay.byValueSource
    (replay : ArgumentReplay config environment parameterVars fuel offset parameters arguments before outcome visits)
    (visit : ArgumentInvocation) (member : visit ∈ visits) (operand : Expr)
    (byValue : visit.argument = .byVal operand) :
    EvaluationTree config environment visit.fuel [environment.act, visit.ordinal, 0] operand visit.before visit.outcome := by
  have actual := replay.visitExecutes visit member
  rw [byValue] at actual
  simp only [argumentValue] at actual
  rw [← actual]
  exact evaluationTree_exists visit.fuel config environment _ operand visit.before

theorem ArgumentReplay.materializedSource
    (replay : ArgumentReplay config environment parameterVars fuel offset parameters arguments before outcome visits)
    (visit : ArgumentInvocation) (member : visit ∈ visits) (operand : Expr) (localVar : LocalVar) (count : Nat)
    (constructed : visit.argument = .construct operand) (found : parameterVars[visit.parameter.var]? = some localVar)
    (materialized : ordinaryProducerCount? visit.fuel ⟨config.module, environment.vars⟩ operand = some count) :
    EvaluationTree config environment visit.fuel [environment.act, visit.ordinal, 0] operand visit.before
      (evalValue visit.fuel config environment operand visit.before) ∧
    visit.outcome = constructedArgumentContinuation visit.fuel config environment localVar operand
      (materializationContinuation (evalValue visit.fuel config environment operand visit.before)) := by
  obtain ⟨tree, materialization⟩ := materializeProducer_source_ghost visit.fuel config environment
    [environment.act, visit.ordinal] operand visit.before count materialized
  have actual := replay.visitExecutes visit member
  rw [constructed, constructedArgument_execution visit.fuel config environment parameterVars visit.parameter operand visit.before localVar found,
    materialization] at actual
  exact ⟨tree, actual.symm⟩

#print axioms ArgumentReplay.materializedSource
private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 4, #[], [], []⟩
private def witnessArguments : List Arg :=
  [.byVal (.blockE (.mk 0 [.print [.text "first"] 0] (some (.lit .i64 7))) 0),
   .byVal (.blockE (.mk 1 [.print [.text "second"] 0] (some (.lit .i64 8))) 0)]
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem argumentWitness_sideEffect :
    ∃ state, evalArguments 40 witnessConfig witnessEnvironment #[]
      [⟨0, .byValue⟩, ⟨1, .byValue⟩] witnessArguments .initial =
        .ok [.int .i64 7, .int .i64 8] state ∧
      state.construction.stdout.data.toList =
        [102, 105, 114, 115, 116, 10, 115, 101, 99, 111, 110, 100, 10] := by
  refine ⟨stepState (evalArguments 40 witnessConfig witnessEnvironment #[]
    [⟨0, .byValue⟩, ⟨1, .byValue⟩] witnessArguments .initial), ?_, ?_⟩ <;>
    unfold witnessConfig witnessEnvironment witnessArguments stepState <;> cbv

private def constructedWitnessExpression : Expr := .blockE
  (.mk 1 [.print [.text "once"] 0]
    (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0
private def constructedWitness : ExecutionStep (List Value) :=
  evalArguments 40 witnessConfig witnessEnvironment #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩]
    [⟨0, .byValue⟩] [.construct constructedWitnessExpression] .initial

theorem constructedArgumentWitness :
    ordinaryProducerCount? 39 ⟨witnessConfig.module, witnessEnvironment.vars⟩ constructedWitnessExpression = some 2 ∧
    ∃ value state, constructedWitness = .ok [value] state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  constructor
  · unfold witnessConfig witnessEnvironment constructedWitnessExpression; cbv
  · refine ⟨(match constructedWitness with | .ok [value] _ => value | _ => .unit), stepState constructedWitness, ?_, ?_⟩ <;>
      unfold constructedWitness witnessConfig witnessEnvironment constructedWitnessExpression stepState <;> cbv

#print axioms constructedArgumentWitness
#print axioms argumentWitness_sideEffect
#print axioms ArgumentReplay.byValueSource
#print axioms ArgumentReplay.once
#print axioms ArgumentReplay.sound
#print axioms ArgumentReplay.sourceOrder
#print axioms argumentReplay_exists
end Goose.Proofs.ConstructionGhostArguments
