import Goose.Proofs.ConstructionAcceptedNestedParameterSource
import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem rpArgs_singleByValue_nextVar {env : PEnv} {expression : Expr} {before middle after : RState}
    {roots : List RootRef} {argumentRoots : List (List RootRef)}
    (operand : rpExpr env expression before = .ok (roots, middle))
    (checked : rpArgs env [.byVal expression] before = .ok (argumentRoots, after)) : after.nextVar = middle.nextVar := by
  exact (rpArgs_singleByValue_state operand checked).2

theorem rpExpr_singleByValue_nextVar {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {expression : Expr} {before middle after : RState} {roots : List RootRef}
    {argumentRoots : List (List RootRef)} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter])
    (arguments : rpArgs env [.byVal expression] before = .ok (argumentRoots, middle))
    (checked : rpExpr env (.call target [.byVal expression] origin) before = .ok (roots, after)) :
    after.nextVar = middle.nextVar := by
  unfold rpExpr at checked
  simp only [arguments, bind, StateT.bind, Except.bind, contextAt, calleeAt, parameters,
    List.zip, List.zipWith, List.forIn_cons, List.forIn_nil, pure, StateT.pure, Except.pure] at checked
  cases content : checkContents env target [.byVal expression] argumentRoots with
  | error failure => simp [content, liftV] at checked
  | ok result =>
    cases result
    simp only [content, liftV] at checked
    split at checked
    · simp only [bind, StateT.bind] at checked
      cases updated : noteResultConstruction env middle with
      | error failure => simp [updated, Except.bind] at checked
      | ok pair =>
        have call : rpCall env target argumentRoots pair.2 = .ok (roots, after) := by
          simpa [updated, Except.bind] using checked
        have same : pair.2.nextVar = middle.nextVar := by
          simp [noteResultConstruction, modify] at updated
          cases updated
          rfl
        exact (rpCall_nextVar call).trans same
    · exact rpCall_nextVar checked

theorem typeExpr_singleByValueRegisterCall_after (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (expression : Expr) (ty : Ty) (before middle after : Nat)
    (types : List Ty) (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee) (parameters : callee.params = #[parameter])
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ integer, ty = .int integer) ∨ ty = .bool)
    (requests : environment.resultRequests = [] ∨ environment.resultRequests = [.register])
    (arguments : typeArguments (fuel + 1) environment callee [parameter] [.byVal expression] before = .ok ((), middle))
    (checked : typeExpr (fuel + 2) environment (.call contextId [.byVal expression] origin) before = .ok (types, after)) :
    after = middle := by
  rcases requests with requests | requests <;> rcases scalar with ⟨integer, rfl⟩ | rfl <;>
    simp [typeExpr, contextAt, calleeAt, parameters, arguments, results, requests, Ty.nonfixed,
      bind, StateT.bind, pure, StateT.pure, Except.pure] at checked <;> cases checked <;> rfl

theorem nestedParameterExpression_rootCursor {config : EvalConfig} {integer : Goose.Core.IntTy} {implementation : Impl} {expression : Expr}
    (form : NestedParameterExpression config integer implementation expression) :
    ∀ (frame : ConstructionSourceFrame) (roots : List RootRef) (after : RState), frame.source.mod = config.module →
      rpExpr frame.source expression frame.rootCursor = .ok (roots, after) → after.nextVar = frame.rootCursor.nextVar := by
  induction form with
  | literal value =>
    intro frame roots after moduleEq rooted
    change Except.ok ([], frame.rootCursor) = Except.ok (roots, after) at rooted
    cases rooted
    rfl
  | localRead id descriptor declared scalar =>
    intro frame roots after moduleEq rooted
    exact localRead_provenance_nextVar frame id roots after rooted
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    intro frame roots after moduleEq rooted
    obtain ⟨_, leftRoots, rightRoots, middle, final, leftRooted, rightRooted, _, _⟩ :=
      rpExpr_bin_operands frame.source operation left right origin frame.rootCursor after roots rooted
    have first := leftIH frame leftRoots middle moduleEq leftRooted
    have second := rightIH { frame with rootCursor := middle } rightRoots final moduleEq rightRooted
    have last := nestedBin_final_nextVar frame operation left right origin roots leftRoots rightRoots after middle final rooted leftRooted rightRooted
    exact last.trans (second.trans first)
  | @call argument target origin context callee parameter summary contextAt calleeAt parameters results known argumentForm ih =>
    intro frame roots after moduleEq rooted
    have contextFound : frame.source.mod.contexts[target]? = some context := by simpa [moduleEq] using contextAt
    have calleeFound : frame.source.mod.impls[context.impl]? = some callee := by simpa [moduleEq] using calleeAt
    obtain ⟨selected, actual, argumentRoots, middle, selectedAt, actualAt, arguments, contents⟩ := rpExpr_call_argumentChecks rooted
    have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans contextFound)
    subst selected
    have sameCallee : actual = callee := Option.some.inj (actualAt.symm.trans calleeFound)
    subst actual
    obtain ⟨operandRoots, operandAfter, remainingRoots, remainingAfter, operand, tail⟩ :=
      rpArgs_byValue_cons frame.source argument [] frame.rootCursor middle argumentRoots arguments
    have first := ih frame operandRoots operandAfter moduleEq operand
    have second := rpArgs_singleByValue_nextVar operand arguments
    have last := rpExpr_singleByValue_nextVar contextFound calleeFound parameters arguments rooted
    exact last.trans (second.trans first)

theorem typeArguments_singleByValue_operand (fuel : Nat) (environment : TypingEnv) (callee : Impl)
    (parameter : Param) (expression : Expr) (before after : Nat)
    (checked : typeArguments (fuel + 1) environment callee [parameter] [.byVal expression] before = .ok ((), after)) :
    ∃ ty middle, typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before = .ok ([ty], middle) ∧ after = middle := by
  cases declared : callee.vars[parameter.var]? with
  | none =>
    simp only [typeArguments, declared] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked
  | some descriptor =>
    cases mode : parameter.mode with
    | byRef =>
      simp only [typeArguments, declared, mode, bind, StateT.bind] at checked
      change Except.error _ = Except.ok _ at checked
      cases checked
    | byValue =>
      simp only [typeArguments, declared, mode, bind, StateT.bind] at checked
      cases nonfixed : descriptor.ty.nonfixed with
      | true =>
        simp only [nonfixed] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      | false =>
        simp only [nonfixed] at checked
        change (typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } expression before).bind _ = _ at checked
        cases operand : typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } expression before with
        | error failure => simp only [operand, Except.bind] at checked; cases checked
        | ok result =>
          obtain ⟨types, middle⟩ := result
          simp only [operand, Except.bind] at checked
          cases types with
          | nil => change Except.error _ = Except.ok _ at checked; cases checked
          | cons ty rest =>
            cases rest with
            | cons other remaining => change Except.error _ = Except.ok _ at checked; cases checked
            | nil =>
              unfold_scalar_typing_helpers
              cases passes : ty.passesTo descriptor.ty with
              | false =>
                simp only [pure, StateT.pure, Except.pure, passes, Bool.false_eq_true, ↓reduceIte] at checked
                change Except.error _ = Except.ok _ at checked
                cases checked
              | true =>
                simp only [pure, StateT.pure, Except.pure, passes, ↓reduceIte] at checked
                cases fuel with
                | zero =>
                  change Except.error _ = Except.ok _ at checked
                  cases checked
                | succ fuel =>
                  have same : after = middle := by simpa [typeArguments, pure, StateT.pure, Except.pure] using checked.symm
                  exact ⟨ty, middle, rfl, same⟩

theorem nestedParameterExpression_typingCursor {config : EvalConfig} {integer : Goose.Core.IntTy} {implementation : Impl} {expression : Expr}
    (form : NestedParameterExpression config integer implementation expression) :
    ∀ (fuel : Nat) (environment : TypingEnv) (before after : Nat) (ty : Ty), environment.module = config.module →
      (environment.resultRequests = [] ∨ environment.resultRequests = [.register]) →
      typeExpr fuel environment expression before = .ok ([ty], after) → after = before := by
  induction form with
  | literal value =>
    intro fuel environment before after ty moduleEq requests checked
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel => change Except.ok ([.int integer], before) = Except.ok ([ty], after) at checked; cases checked; rfl
  | localRead id descriptor declared scalar =>
    intro fuel environment before after ty moduleEq requests checked
    obtain ⟨found, visible, present, sameTy, sameCounter, fixed⟩ :=
      typeExpr_localRead_descriptor fuel environment id before after ty checked
    exact sameCounter
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    intro fuel environment before after ty moduleEq requests checked
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      obtain ⟨operandInteger, middle, sameTy, leftTyped, rightTyped⟩ :=
        typeExpr_bin_operands fuel environment operation left right origin before after ty checked
      have first := leftIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
        before middle (.int operandInteger) moduleEq (Or.inl rfl) leftTyped
      have second := rightIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
        middle after (.int operandInteger) moduleEq (Or.inl rfl) rightTyped
      exact second.trans first
  | @call argument target origin context callee parameter summary contextAt calleeAt parameters results known argumentForm ih =>
    intro fuel environment before after ty moduleEq requests checked
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      cases fuel with
      | zero =>
        simp only [typeExpr, moduleEq, contextAt, calleeAt, parameters, typeArguments, bind, StateT.bind, Except.bind] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      | succ fuel =>
        have contextFound : environment.module.contexts[target]? = some context := by simpa [moduleEq] using contextAt
        have calleeFound : environment.module.impls[context.impl]? = some callee := by simpa [moduleEq] using calleeAt
        obtain ⟨argumentsAfter, arguments⟩ := typeExpr_call_arguments (fuel + 1) environment target context callee
          [.byVal argument] origin before after [ty] contextFound calleeFound checked
        have arguments' : typeArguments (fuel + 1) environment callee [parameter] [.byVal argument] before = .ok ((), argumentsAfter) := by
          simpa [parameters] using arguments
        obtain ⟨argumentTy, operandAfter, operand, same⟩ := typeArguments_singleByValue_operand fuel environment callee parameter argument
          before argumentsAfter arguments'
        have first := ih fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
          before operandAfter argumentTy moduleEq (Or.inl rfl) operand
        have last := typeExpr_singleByValueRegisterCall_after fuel environment target origin context callee parameter argument (.int integer)
          before argumentsAfter after [ty] contextFound calleeFound parameters results (Or.inl ⟨integer, rfl⟩) requests arguments' checked
        exact last.trans (same.trans first)

#print axioms nestedParameterExpression_typingCursor
#print axioms typeArguments_singleByValue_operand
#print axioms nestedParameterExpression_rootCursor
#print axioms typeExpr_singleByValueRegisterCall_after
#print axioms rpExpr_singleByValue_nextVar
#print axioms rpArgs_singleByValue_nextVar
end Goose.Proofs.ConstructionAcceptedExecution
