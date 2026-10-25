import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionArgumentOrigins

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem argumentCons_escape_origin (head : Value) (action : EvalM (List Value))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : ((do pure (head :: (← action))) : EvalM (List Value)) initial = .escape address carriers final) :
    action initial = .escape address carriers final := by
  cases result : action initial <;> simp only [bind, result, pure] at escaped
  case escape target returned after => cases escaped; rfl
  all_goals cases escaped

private theorem argumentBind_escape_origin (action : EvalM α) (next : α → EvalM β)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (safe : ProducerNeverEscapes action)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    ∃ value middle, action initial = .ok value middle ∧ next value middle = .escape address carriers final := by
  cases evaluated : action initial <;> simp only [bind, evaluated] at escaped
  case ok value middle => exact ⟨value, middle, rfl, escaped⟩
  case escape target returned after => exact False.elim (safe _ _ _ _ evaluated)
  all_goals cases escaped

private theorem argumentPublish_neverEscapes (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    ProducerNeverEscapes (publishCarriers origin carriers) := by
  unfold publishCarriers
  producer_never_escapes_base

private theorem argumentMaterialized_neverEscapes (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (descriptor : LocalVar) (operand : Expr) (values : Array Value) :
    ProducerNeverEscapes (materializedDestination fuel config.layout environment.act descriptor.ty
      (expressionOrigin operand) values.size (.fixed values)) := by
  unfold materializedDestination
  apply producerNeverEscapes_bind
  · exact producerNeverEscapes_newDestination _ _ _ _ _ _ _
  · intro destination
    apply producerNeverEscapes_bind
    · exact producerNeverEscapes_copyValue _ _ _ _ _ _
    · intro _
      exact producerNeverEscapes_completedReceivingDestination _

private theorem argumentMaterialize_none (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operand : Expr) (initial final : ExecutionState)
    (normal : materializeProducer fuel ⟨config.module, environment.vars⟩ operand
      (evalValue fuel config environment operand) initial = .ok none final) :
    ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none ∧ final = initial := by
  cases count : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand with
  | none =>
      simp only [materializeProducer, count, pure] at normal
      cases normal
      exact ⟨rfl, rfl⟩
  | some countValue =>
      simp only [materializeProducer, count, bind] at normal
      cases evaluated : evalValue fuel config environment operand initial with
      | ok value after =>
          cases value <;> simp only [evaluated, pure, fault, EvalM.stop] at normal <;> cases normal
      | escape target returned after | stop reason after | jump target kind after =>
          simp only [evaluated] at normal
          cases normal

private theorem argumentsValue_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.byVal operand :: arguments)
      initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitCallSite config (.arguments (fuel + 1) environment vars (parameter :: parameters) (.byVal operand :: arguments))
        initial child prepared ∧ child.action config prepared = .escape address carriers final := by
  simp only [evalArguments] at escaped
  cases evaluated : evalValue fuel config environment operand initial with
  | ok head middle =>
      simp only [bind, evaluated] at escaped
      exact ⟨List Value, .arguments fuel environment vars parameters arguments, middle,
        .argumentsTail fuel environment vars parameter parameters (.byVal operand) arguments initial middle head
          (.value operand initial middle head evaluated),
        argumentCons_escape_origin head _ middle final address carriers escaped⟩
  | escape target returned after =>
      simp only [bind, evaluated] at escaped
      cases escaped
      exact ⟨Value, .value fuel environment operand, initial,
        .argumentValue fuel environment vars parameter parameters operand arguments initial, evaluated⟩
  | stop reason after | jump target kind after =>
      simp only [bind, evaluated] at escaped
      cases escaped

private theorem argumentsReference_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param) (mutability : Goose.Core.Mutability)
    (place : Place) (arguments : List Arg) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.byRef mutability place :: arguments)
      initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitCallSite config (.arguments (fuel + 1) environment vars (parameter :: parameters) (.byRef mutability place :: arguments))
        initial child prepared ∧ child.action config prepared = .escape address carriers final := by
  simp only [evalArguments, bind] at escaped
  cases evaluated : evalPlace fuel config environment place initial with
  | ok location middle =>
      simp only [evaluated, pure] at escaped
      exact ⟨List Value, .arguments fuel environment vars parameters arguments, middle,
        .argumentsTail fuel environment vars parameter parameters (.byRef mutability place) arguments initial middle (.ref location)
          (.reference mutability place initial middle location evaluated),
        argumentCons_escape_origin (.ref location) _ middle final address carriers escaped⟩
  | escape target returned after =>
      simp only [evaluated] at escaped
      cases escaped
      exact ⟨Goose.Core.Loc, .place fuel environment place, initial,
        .argumentReference fuel environment vars parameter parameters mutability place arguments initial, evaluated⟩
  | stop reason after | jump target kind after =>
      simp only [evaluated] at escaped
      cases escaped

private theorem argumentsConstruct_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.construct operand :: arguments)
      initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitCallSite config (.arguments (fuel + 1) environment vars (parameter :: parameters) (.construct operand :: arguments))
        initial child prepared ∧ child.action config prepared = .escape address carriers final := by
  simp only [evalArguments] at escaped
  cases lookup : vars[parameter.var]? with
  | none =>
      simp only [lookup, fault, bind, EvalM.stop] at escaped
      cases escaped
  | some descriptor =>
      simp only [lookup] at escaped
      cases materialized : materializeProducer fuel ⟨config.module, environment.vars⟩ operand
          (evalValue fuel config environment operand) initial with
      | escape target returned after =>
          simp only [bind, materialized] at escaped
          cases escaped
          obtain ⟨count, ordinary, evaluated⟩ := materializeProducer_escape_value fuel config environment operand
            initial final address carriers materialized
          exact ⟨Value, .value fuel environment operand, initial,
            .argumentMaterialize fuel environment vars parameter parameters operand arguments initial descriptor count lookup ordinary,
            evaluated⟩
      | stop reason after | jump target kind after =>
          simp only [bind, materialized] at escaped
          cases escaped
      | ok values evaluated =>
          simp only [bind, materialized] at escaped
          cases values with
          | none =>
              obtain ⟨ordinary, sameState⟩ := argumentMaterialize_none fuel config environment operand initial evaluated materialized
              subst evaluated
              cases constructed : constructLocal ⟨config.module, environment.vars⟩ environment.act descriptor.ty
                  (expressionOrigin operand) operand (fun destination => buildExpr fuel config environment destination operand) initial with
              | escape target returned after =>
                  simp only [constructed] at escaped
                  cases escaped
                  obtain ⟨destination, prepared, allocated, fromBuild⟩ := constructLocal_escape_call
                    ⟨config.module, environment.vars⟩ environment.act descriptor.ty (expressionOrigin operand) operand
                    (fun destination => buildExpr fuel config environment destination operand) initial final address carriers constructed
                  exact ⟨Unit, .build fuel environment destination operand, prepared,
                    .argumentBuild fuel environment vars parameter parameters operand arguments initial prepared descriptor destination
                      lookup ordinary allocated, fromBuild⟩
              | stop reason after | jump target kind after =>
                  simp only [constructed] at escaped
                  cases escaped
              | ok carrier constructedState =>
                  simp only [constructed] at escaped
                  obtain ⟨value, middle, converted, remaining⟩ := argumentBind_escape_origin _ _ constructedState final address carriers
                    (producerNeverEscapes_carrierValue carrier) escaped
                  exact ⟨List Value, .arguments fuel environment vars parameters arguments, middle,
                    .argumentsTail fuel environment vars parameter parameters (.construct operand) arguments initial middle value
                      (.constructed operand descriptor carrier value initial initial constructedState middle lookup materialized constructed converted),
                    argumentCons_escape_origin value _ middle final address carriers remaining⟩
          | some values =>
              obtain ⟨destination, stored, storedNormally, remaining⟩ := argumentBind_escape_origin _ _ evaluated final address carriers
                (argumentMaterialized_neverEscapes fuel config environment descriptor operand values) escaped
              obtain ⟨unitValue, published, publishedNormally, remaining⟩ := argumentBind_escape_origin _ _ stored final address carriers
                (argumentPublish_neverEscapes (expressionOrigin operand) [.completed destination]) remaining
              simp only [pure] at remaining
              obtain ⟨value, middle, converted, remaining⟩ := argumentBind_escape_origin _ _ published final address carriers
                (producerNeverEscapes_carrierValue (.completed destination)) remaining
              exact ⟨List Value, .arguments fuel environment vars parameters arguments, middle,
                .argumentsTail fuel environment vars parameter parameters (.construct operand) arguments initial middle value
                  (.materialized operand descriptor values destination value initial evaluated stored published middle
                    lookup materialized storedNormally publishedNormally converted),
                argumentCons_escape_origin value _ middle final address carriers remaining⟩

theorem argumentsInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalArguments fuel config environment vars parameters arguments initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitCallSite config (.arguments fuel environment vars parameters arguments) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  cases fuel with
  | zero =>
      simp only [evalArguments, timeout, EvalM.stop] at escaped
      cases escaped
  | succ fuel =>
      cases parameters with
      | nil =>
          cases arguments <;> simp only [evalArguments, pure, fault, EvalM.stop] at escaped <;> cases escaped
      | cons parameter parameters =>
          cases arguments with
          | nil =>
              simp only [evalArguments, fault, EvalM.stop] at escaped
              cases escaped
          | cons argument arguments =>
              cases argument with
              | byVal operand =>
                  exact argumentsValue_escape_inv fuel config environment vars parameter parameters operand arguments
                    initial final address carriers escaped
              | byRef mutability place =>
                  exact argumentsReference_escape_inv fuel config environment vars parameter parameters mutability place arguments
                    initial final address carriers escaped
              | construct operand =>
                  exact argumentsConstruct_escape_inv fuel config environment vars parameter parameters operand arguments
                    initial final address carriers escaped

#print axioms argumentsInvocation_escape_inv

#print axioms argumentsValue_escape_inv
#print axioms argumentsReference_escape_inv
#print axioms argumentsConstruct_escape_inv

end Goose.Proofs.ExitExecution
