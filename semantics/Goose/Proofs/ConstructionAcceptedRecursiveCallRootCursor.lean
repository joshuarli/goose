import Goose.Proofs.ConstructionAcceptedCallCheckedEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem rpExpr_zeroArgument_nextVar {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {before after : RState} {roots : List RootRef} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[])
    (checked : rpExpr env (.call target [] origin) before = .ok (roots, after)) :
    after.nextVar = before.nextVar := by
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
        have same : pair.2.nextVar = before.nextVar := by
          simp [noteResultConstruction, modify] at updated
          cases updated
          rfl
        exact (rpCall_nextVar call).trans same
    · exact rpCall_nextVar checked

#print axioms rpExpr_zeroArgument_nextVar
end Goose.Proofs.ConstructionAcceptedExecution
