import Goose.Proofs.ExitExecutionInvocationStatementsCauses
import Goose.Proofs.ExitExecutionInvocationValuesNative
import Goose.Proofs.ExitExecutionArgumentOrigins

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

local macro "let_cause_native" : tactic => `(tactic|
  repeat' first
    | with_reducible exact producerNeverEscapes_copyValue _ _ _ _ _ _
    | with_reducible exact producerNeverEscapes_storedDestination _
    | with_reducible exact producerNeverEscapes_completedReceivingDestination _
    | with_reducible exact valueNeverEscapes_publishCarriers _ _
    | with_reducible exact valueNeverEscapes_bindRoot _ _
    | value_never_escapes_step)

private theorem letCause_bind_step (action : EvalM α) (next : α → EvalM β) (state : ExecutionState) :
    (action >>= next) state = match action state with
      | .ok value after => next value after
      | .stop reason after => .stop reason after
      | .escape address carriers after => .escape address carriers after
      | .jump target kind after => .jump target kind after := rfl

private theorem letCause_bind_pure (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

private theorem letCause_bind_right (action : EvalM α) (next : α → EvalM β)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (native : ProducerNeverEscapes action)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    ∃ value prepared, action initial = .ok value prepared ∧ next value prepared = .escape address carriers final := by
  cases evaluated : action initial with
  | ok value prepared => exact ⟨value, prepared, rfl, by simpa only [bind, evaluated] using escaped⟩
  | escape target payload state => exact False.elim (native initial target payload state evaluated)
  | stop reason state | jump target kind state => simp only [bind, evaluated] at escaped; cases escaped

private theorem letCause_bind_left (action : EvalM α) (next : α → EvalM β)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (action >>= next) initial = .escape address carriers final)
    (native : ∀ value, ProducerNeverEscapes (next value)) :
    action initial = .escape address carriers final := by
  cases evaluated : action initial with
  | ok value prepared =>
    exact False.elim (native value prepared address carriers final (by simpa only [bind, evaluated] using escaped))
  | escape target payload state =>
    simp only [bind, evaluated] at escaped
    cases escaped
    rfl
  | stop reason state | jump target kind state => simp only [bind, evaluated] at escaped; cases escaped

private theorem letCause_native_impossible (action : EvalM α) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : action initial = .escape address carriers final) (native : ProducerNeverEscapes action) : False :=
  native initial address carriers final escaped

private theorem letCause_afterNamed (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (initial selected final : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst)
    (named : Option (ResultDescriptor × Nat))
    (namedPrefix : StatementLetNamedPrefix config environment localVar origin initial descriptor root named selected)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : ((do
      let materialized ← if named.isNone then
          materializeProducer fuel ⟨config.module, environment.vars⟩ expression (evalValue fuel config environment expression)
        else pure none
      let destination ← match named with
        | some (_, index) => match environment.channels[index]? with
          | some (.construct destination) => liftConstruction origin (renewReceivingDestination destination)
          | _ => fault .flow
        | none => (newDestination config.layout environment.act descriptor.ty .value origin none
            (materialized.map Array.size <|> producerCount? ⟨config.module, environment.vars⟩ expression))
      if named.isSome then liftConstruction origin (prepareNamedBinding destination descriptor.ty)
      match materialized with
      | some values => copyValue fuel config.layout destination (.fixed values) origin none
      | none => buildExpr fuel config environment destination expression
      let destination ← completedReceivingDestination destination
      if named.isNone then publishCarriers origin [.completed destination]
      let stored ← storedDestination destination
      let object ← if named.isSome then do pure (some (← liftConstruction origin reserveStorage)) else pure none
      bindRoot root (.stored { stored with ty := descriptor.ty, object := object })
      pure (Flow.normal .unit)) : EvalM Flow) selected =
        .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (.letS localVar expression origin)) initial address carriers := by
  cases named with
  | none =>
    simp only [Option.isNone, Option.isSome, Bool.false_eq_true, ite_true, ite_false] at escaped
    cases materialization : materializeProducer fuel ⟨config.module, environment.vars⟩ expression
        (evalValue fuel config environment expression) selected with
    | stop reason state | jump target kind state =>
      rw [letCause_bind_step, materialization] at escaped
      cases escaped
    | escape target payload state =>
      rw [letCause_bind_step, materialization] at escaped
      cases escaped
      obtain ⟨count, countFound, childEscape⟩ :=
        materializeProducer_escape_value fuel config environment expression selected final address carriers materialization
      exact ⟨Value, .value fuel environment expression, selected, final,
        .letMaterialize fuel environment localVar expression origin initial selected descriptor root count namedPrefix countFound,
        childEscape⟩
    | ok materialized materializedState =>
      rw [letCause_bind_step, materialization] at escaped
      dsimp only [] at escaped
      obtain ⟨destination, allocated, allocation, remaining⟩ :=
        letCause_bind_right _ _ materializedState final address carriers
          (producerNeverEscapes_newDestination _ _ _ _ _ _ _) escaped
      cases materialized with
      | some values =>
        exact False.elim (letCause_native_impossible _ allocated final address carriers remaining (by let_cause_native))
      | none =>
        simp only [letCause_bind_pure] at remaining
        have childEscape := letCause_bind_left _ _ allocated final address carriers remaining
          (fun _ => by let_cause_native)
        change buildExpr fuel config environment destination expression allocated = .escape address carriers final at childEscape
        change newDestination config.layout environment.act descriptor.ty .value origin none
          (producerCount? ⟨config.module, environment.vars⟩ expression) materializedState = .ok destination allocated at allocation
        refine ⟨Unit, .build fuel environment destination expression, allocated, final,
          .letBuild fuel environment localVar expression origin initial allocated destination ?_, childEscape⟩
        exact .actual initial selected materializedState allocated allocated descriptor root none destination namedPrefix
          materialization allocation rfl
  | some pair =>
    rcases pair with ⟨result, index⟩
    simp only [Option.isNone, Option.isSome, Bool.false_eq_true, ite_true, ite_false, letCause_bind_pure] at escaped
    cases channelFound : environment.channels[index]? with
    | none =>
      simp only [channelFound, fault, EvalM.stop, bind] at escaped
      cases escaped
    | some channel =>
      cases channel with
      | register ty | completion token =>
        simp only [channelFound, fault, EvalM.stop, bind] at escaped
        cases escaped
      | construct incoming =>
        simp only [channelFound] at escaped
        obtain ⟨destination, allocated, allocation, remaining⟩ :=
          letCause_bind_right _ _ selected final address carriers (producerNeverEscapes_liftConstruction _ _) escaped
        obtain ⟨unitValue, prepared, preparation, remaining⟩ :=
          letCause_bind_right _ _ allocated final address carriers (producerNeverEscapes_liftConstruction _ _) remaining
        cases unitValue
        have childEscape := letCause_bind_left _ _ prepared final address carriers remaining
          (fun _ => by let_cause_native)
        change buildExpr fuel config environment destination expression prepared = .escape address carriers final at childEscape
        refine ⟨Unit, .build fuel environment destination expression, prepared, final,
          .letBuild fuel environment localVar expression origin initial prepared destination ?_, childEscape⟩
        refine .actual initial selected selected allocated prepared descriptor root (some (result, index)) destination
          namedPrefix rfl ?_ preparation
        simpa only [channelFound] using allocation

theorem statementInvocation_letS_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.letS localVar expression origin) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (.letS localVar expression origin)) initial address carriers := by
  cases lookup : environment.vars[localVar]? with
  | none =>
    simp only [execStmt, lookup, fault, EvalM.stop] at escaped
    cases escaped
  | some descriptor =>
    simp only [execStmt, lookup] at escaped
    obtain ⟨root, rooted, rootSelected, afterRoot⟩ :=
      letCause_bind_right _ _ initial final address carriers (producerNeverEscapes_rootOf environment localVar) escaped
    cases nonfixed : descriptor.ty.nonfixed with
    | false =>
      simp only [nonfixed, Bool.false_eq_true, ite_false] at afterRoot
      have childEscape := letCause_bind_left _ _ rooted final address carriers afterRoot (fun _ => by let_cause_native)
      exact ⟨Value, .value fuel environment expression, rooted, final,
        .letValue fuel environment localVar expression origin initial rooted descriptor root lookup nonfixed rootSelected,
        childEscape⟩
    | true =>
      have valueEscape := afterRoot
      simp only [nonfixed, ite_true] at valueEscape
      cases implementationLookup : config.module.impls[environment.implementation]? with
      | none =>
        simp only [implementationLookup, fault] at valueEscape
        cases valueEscape
      | some implementation =>
        simp only [implementationLookup] at valueEscape
        cases candidate : implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar) with
        | none =>
          simp only [candidate, letCause_bind_pure] at valueEscape
          exact letCause_afterNamed fuel config environment localVar expression origin initial rooted final descriptor root
            none (.absent initial rooted descriptor root implementation lookup nonfixed rootSelected implementationLookup candidate)
            address carriers valueEscape
        | some pair =>
          rcases pair with ⟨result, index⟩
          simp only [candidate] at valueEscape
          cases channelFound : environment.channels[index]? with
          | none =>
            simp only [channelFound, fault, EvalM.stop, bind] at valueEscape
            cases valueEscape
          | some channel =>
            cases channel with
            | register ty | completion token =>
              simp only [channelFound, fault, EvalM.stop, bind] at valueEscape
              cases valueEscape
            | construct incoming =>
              simp only [channelFound] at valueEscape
              obtain ⟨destination, renewed, renewal, afterRenewal⟩ :=
                letCause_bind_right _ _ rooted final address carriers (producerNeverEscapes_liftConstruction _ _) valueEscape
              obtain ⟨receiving, selected, selection, afterSelection⟩ :=
                letCause_bind_right _ _ renewed final address carriers (producerNeverEscapes_getDestination _) afterRenewal
              cases request : (receiving.capability.request == .value) with
              | false =>
                simp only [request, Bool.false_eq_true, ite_false, letCause_bind_pure] at afterSelection
                exact letCause_afterNamed fuel config environment localVar expression origin initial selected final descriptor root
                  none (.other initial rooted renewed selected descriptor root implementation result index incoming destination receiving
                    lookup nonfixed rootSelected implementationLookup candidate channelFound renewal selection request)
                  address carriers afterSelection
              | true =>
                simp only [request, ite_true, letCause_bind_pure] at afterSelection
                exact letCause_afterNamed fuel config environment localVar expression origin initial selected final descriptor root
                  (some (result, index))
                  (.receiving initial rooted renewed selected descriptor root implementation result index incoming destination receiving
                    lookup nonfixed rootSelected implementationLookup candidate channelFound renewal selection request)
                  address carriers afterSelection

end Goose.Proofs.ExitExecution
