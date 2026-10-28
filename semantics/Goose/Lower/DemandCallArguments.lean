import Goose.Lower.DemandCalleeEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem mapList_success_length {α β : Type} (operation : α → M β) :
    ∀ (items : List α) {state after : St} {values : List β},
      mapList operation items state = .ok values after → values.length = items.length := by
  intro items
  induction items with
  | nil =>
    intro state after values done
    simp only [mapList, pure_apply, Res.ok.injEq] at done
    obtain ⟨rfl, rfl⟩ := done
    rfl
  | cons item rest ih =>
    intro state after values done
    simp only [mapList, bind_apply] at done
    cases first : operation item state with
    | stop stop final => simp [first] at done
    | ok value middle =>
      simp only [first] at done
      cases tail : mapList operation rest middle with
      | stop stop final => simp [tail] at done
      | ok result final =>
        simp only [tail, pure_apply, Res.ok.injEq] at done
        obtain ⟨rfl, rfl⟩ := done
        simp only [List.length_cons, ih tail]

theorem ExprSource.call_arguments_arity {cfg : Cfg} {env : Env} {state after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) {fuel : Nat} {values : List Val}
    (done : mapList (evalArg fuel cfg env) arguments state = .ok values after) :
    impl.params.size = values.length := by
  have contextAtT : source.typingEnv.mod.contexts[context]? = some ctx := by
    rw [source.frame.mod_t]
    exact contextAt
  have implAtT : source.typingEnv.mod.impls[ctx.impl]? = some impl := by
    rw [source.frame.mod_t]
    exact implAt
  have typing := source.typed
  simp only [tyExpr, contextAtT, implAtT] at typing
  inv at typing
  obtain ⟨_, size, _, _, _, _, _⟩ := typing
  exact size.trans (mapList_success_length (evalArg fuel cfg env) arguments done).symm

theorem accepted_actual_call_arguments_entry {cfg : Cfg} {env : Env} {state after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {sourceFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg sourceFuel cfg env) arguments state = .ok values after)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    {caller : Func} {point : Pt} {callerFrame : GIR.Frame} {result : ValueId} {ids : List ValueId}
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point callerFrame after)
    (instruction : instAt caller point = some (.def result (.call context ids (some origin))))
    (depthEq : callerFrame.depth = env.depth) (depth : callerFrame.depth < maxCallDepth)
    (read : mapList (getVal callerFrame) ids after = .ok values after)
    {map : RetainedSsaMap} {world : World}
    (retained : map.Realizes cfg.mod world env ⟨point, callerFrame, after⟩)
    (count : Nat) (bound : count ≤ values.length) :
    ∃ body : BlockSource cfg ⟨impl.vars, after.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)) impl.body
      { after with nextAct := after.nextAct + 1 },
      Nonempty (ParameterPrefixCursor body count) ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 1 + count)
        { (callFrame impl after.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, after.nextScope)] }
        { after with nextAct := after.nextAct + 1, nextScope := after.nextScope + 1, store := preStore after.nextAct after.nextScope (((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)).take count) after.store } ∧
      map.Realizes cfg.mod world env ⟨point, callerFrame,
        { after with nextAct := after.nextAct + 1, nextScope := after.nextScope + 1, store := preStore after.nextAct after.nextScope (((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)).take count) after.store }⟩ := by
  have arity := source.call_arguments_arity contextAt implAt argumentsDone
  have entry := lowered_function_entry_generated (cfg := cfg) (ctx := ctx) (impl := impl)
    (depth := callerFrame.depth + 1) (values := values) (state := after) arity
  exact accepted_actual_callee_parameter_prefix source argumentsDone contextAt implAt callerPoint instruction
    depthEq depth read entry retained count bound

#print axioms mapList_success_length
#print axioms ExprSource.call_arguments_arity
#print axioms accepted_actual_call_arguments_entry
end Goose.Lower
