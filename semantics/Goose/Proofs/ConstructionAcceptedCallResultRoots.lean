import Goose.Proofs.ConstructionAcceptedCallCheckedEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def Returns (expected : Goose.Core.V α) (action : P α) : Prop :=
  ∀ before result after, action before = .ok (result, after) → expected = .ok result

private theorem returns_bind (expected : Goose.Core.V β) (action : P α) (next : α → P β)
    (remaining : ∀ value, Returns expected (next value)) : Returns expected (action >>= next) := by
  intro before result after checked
  cases initial : action before with
  | error error => simp [bind, StateT.bind, Except.bind, initial] at checked
  | ok pair =>
    apply remaining pair.1 pair.2 result after
    simpa [bind, StateT.bind, Except.bind, initial] using checked

private theorem returns_lift (expected : Goose.Core.V α) : Returns expected (liftV expected) := by
  intro before result after checked
  cases h : expected with
  | error failure => simp [liftV, h] at checked
  | ok value =>
    simp [liftV, h] at checked
    exact congrArg Except.ok checked.1

private theorem returns_reject (expected : Goose.Core.V α) (rule : Goose.Core.Rule) (message : String) :
    Returns expected (rejP rule message) := by
  intro before result after checked
  cases checked

local macro "returns_result" : tactic => `(tactic|
  repeat' first
  | exact returns_lift _
  | exact returns_reject _ _ _
  | refine returns_bind _ _ _ (fun _ => ?_)
  | split)

theorem rpCall_resultRoots {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {before after : RState} {roots : List RootRef} (arguments : List (List RootRef))
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (checked : rpCall env target arguments before = .ok (roots, after)) : callResultRoots callee context arguments = .ok roots := by
  have result : Returns (callResultRoots callee context arguments) (rpCall env target arguments) := by
    unfold rpCall
    simp only [contextAt, calleeAt]
    returns_result
    all_goals try dsimp only
    all_goals returns_result
  exact result before roots after checked

theorem rpCall_scalarRegister_roots {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {before after : RState} {roots : List RootRef} (arguments : List (List RootRef)) (ty : Ty)
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ integer, ty = .int integer) ∨ ty = .bool)
    (checked : rpCall env target arguments before = .ok (roots, after)) : roots = [] := by
  have result := rpCall_resultRoots arguments contextAt calleeAt checked
  rcases scalar with ⟨integer, rfl⟩ | rfl <;>
    simp [callResultRoots, results, Ty.isRefLike] at result
  all_goals
    cases channels : context.resultRoots with
    | nil => simp [channels, Goose.Core.reject, Functor.map, Except.map, Except.bind] at result
    | cons head tail =>
      cases tail with
      | nil => simpa [channels, List.zip, List.zipWith, List.forIn_cons, List.forIn_nil, pure, Except.pure, bind, Except.bind] using result.symm
      | cons next rest => simp [channels, Goose.Core.reject, Functor.map, Except.map, Except.bind] at result

theorem rpExpr_singleByValue_scalarRegister_roots {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {expression : Expr} {before middle after : RState} {roots : List RootRef}
    {argumentRoots : List (List RootRef)} {origin : Nat} (ty : Ty)
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ integer, ty = .int integer) ∨ ty = .bool)
    (arguments : rpArgs env [.byVal expression] before = .ok (argumentRoots, middle))
    (checked : rpExpr env (.call target [.byVal expression] origin) before = .ok (roots, after)) : roots = [] := by
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
        exact rpCall_scalarRegister_roots argumentRoots ty contextAt calleeAt results scalar call
    · exact rpCall_scalarRegister_roots argumentRoots ty contextAt calleeAt results scalar checked

theorem rpExpr_zeroArgument_scalarRegister_roots {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {before after : RState} {roots : List RootRef} {origin : Nat} (ty : Ty)
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ integer, ty = .int integer) ∨ ty = .bool)
    (checked : rpExpr env (.call target [] origin) before = .ok (roots, after)) : roots = [] := by
  unfold rpExpr at checked
  simp only [rpArgs, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind, contextAt, calleeAt,
    parameters, Array.toList_empty, List.zip, List.zipWith, List.forIn_nil] at checked
  cases content : checkContents env target [] [] with
  | error failure => simp [content, liftV] at checked
  | ok result =>
    cases result
    simp only [content, liftV] at checked
    split at checked
    · simp only [bind, StateT.bind] at checked
      cases updated : noteResultConstruction env before with
      | error failure => simp [updated, Except.bind] at checked
      | ok pair =>
        have call : rpCall env target [] pair.2 = .ok (roots, after) := by
          simpa [updated, Except.bind] using checked
        exact rpCall_scalarRegister_roots [] ty contextAt calleeAt results scalar call
    · exact rpCall_scalarRegister_roots [] ty contextAt calleeAt results scalar checked

#print axioms rpExpr_zeroArgument_scalarRegister_roots
#print axioms rpExpr_singleByValue_scalarRegister_roots
#print axioms rpCall_scalarRegister_roots
#print axioms rpCall_resultRoots
end Goose.Proofs.ConstructionAcceptedExecution
