import Goose.Lower.DemandCallBodyReturn
import Goose.Lower.DemandCallArguments

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence Goose.Proofs.Lower

structure CallCalleeDemandReady (cfg : Cfg) (env : Env) (middle : St) (values : List Val)
    (context : ContextId) (ctx : Context) (impl : Impl)
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl) where
  source : BlockSource cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
    ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
    { middle with nextAct := middle.nextAct + 1 }
  owned : GeneratedSourceOwner (.context contextAt implAt) source.context
  occurrence : GeneratedDemandOccurrence cfg.mod (lowerContextAt cfg.mod ctx impl)
    (lowerEnv cfg.mod impl.vars impl.results.toList) (.block impl.body) source.path
    (.block none (callPre impl) false impl.body) (callEntry impl)
  rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence ⟨[], []⟩
  input : GeneratedPrefixInput cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
    ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList none
    source.typingEnv source.rootsEnv (callEntry impl) (callFrame impl middle.nextAct (env.depth + 1) values) (0, 0)
  cells : PreRel (callFrame impl middle.nextAct (env.depth + 1) values) (callPre impl)
    ((impl.params.toList.zip values).map fun item => (item.1.var, item.2))

theorem accepted_generated_callee_ready {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {fuel : Nat} {values : List Val} (done : mapList (evalArg fuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) :
    Nonempty (CallCalleeDemandReady cfg env middle values context ctx impl contextAt implAt) := by
  obtain ⟨actualCtx, actualImpl, actualContextAt, actualImplAt, callee, typing, roots, path, sourceOwner⟩ :=
    source.calleeAfterArgs fuel values done
  have ctxEq : actualCtx = ctx := Option.some.inj (actualContextAt.symm.trans contextAt)
  subst actualCtx
  have implEq : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
  subst actualImpl
  let selected : GeneratedDemandRootSelection cfg.mod (lowerContextAt cfg.mod ctx impl)
      (lowerEnv cfg.mod impl.vars impl.results.toList) (.block impl.body) context := .context contextAt implAt
  have owned : GeneratedSourceOwner selected callee.context := by
    refine ⟨sourceOwner, ?_⟩
    rw [path]
    exact .here _
  have occurrence : GeneratedDemandOccurrence cfg.mod (lowerContextAt cfg.mod ctx impl)
      (lowerEnv cfg.mod impl.vars impl.results.toList) (.block impl.body) callee.path
      (.block none (callPre impl) false impl.body) (callEntry impl) := by
    rw [path]
    exact .functionRoot contextAt implAt
  have rows : GeneratedDemandRows cfg.mod callee.rootsEnv.access occurrence ⟨[], []⟩ := by
    simpa only [path] using
      (GeneratedDemandRows.functionRoot (contextAt := contextAt) (implementationAt := implAt) (by rw [roots]))
  have metadata : SourceResults callee.typingEnv callee.rootsEnv impl.results.toList := by
    intro actual equal
    rw [typing] at equal
    simp [implEnv] at equal
    subst actual
    simp [roots]
  have input : GeneratedPrefixInput cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList none
      callee.typingEnv callee.rootsEnv (callEntry impl) (callFrame impl middle.nextAct (env.depth + 1) values) (0, 0) := by
    refine ⟨metadata, ?_, callEntry_pp impl, callFrame_rel _ _ _ _ _ _ _, rfl, ?_, trivial, trivial, trivial,
      callEntry_generated cfg.mod impl, trivial⟩
    · rw [typing]
      simp [LoopSourceMatches, implEnv]
    · rfl
  have arity := source.call_arguments_arity contextAt implAt done
  exact ⟨⟨callee, owned, occurrence, rows, input, callFrame_preRel impl middle.nextAct (env.depth + 1) values arity⟩⟩

theorem accepted_generated_callee_actual_return {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {fuel : Nat} {values : List Val} (done : mapList (evalArg fuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 })
    {taken : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 1 + (callPre impl).length),
        { (callFrame impl middle.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, middle.nextScope)] },
        { middle with nextAct := middle.nextAct + 1, nextScope := middle.nextScope + 1, store := preStore middle.nextAct middle.nextScope ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) middle.store }⟩ terminal)
    (returned : instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term (.ret [] none))) :
    ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal .unit) terminal.state ∧
    (∃ total, DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ total
      ⟨(0, 0), callFrame impl middle.nextAct (env.depth + 1) values, { middle with nextAct := middle.nextAct + 1 }⟩ terminal) ∧
    Post cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (callEntry impl)
      (callFrame impl middle.nextAct (env.depth + 1) values)
      (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
      terminal.frame terminal.point [] := by
  obtain ⟨ready⟩ := accepted_generated_callee_ready source done contextAt implAt
  have coverage : (⟨[], []⟩ : RetainedSsaMap).Covers ⟨[], []⟩ := by simp [RetainedSsaMap.Covers]
  have admitted : (⟨[], []⟩ : RetainedSsaMap).Admitted cfg.mod.profile ready.source.context.retained := by simp [RetainedSsaMap.Admitted]
  have bounded : (⟨[], []⟩ : RetainedSsaMap).Bounded (callEntry impl).vals.size := by simp [RetainedSsaMap.Bounded]
  have realized : (⟨[], []⟩ : RetainedSsaMap).Realizes cfg.mod ready.source.world
      ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ⟨(0, 0), callFrame impl middle.nextAct (env.depth + 1) values, { middle with nextAct := middle.nextAct + 1 }⟩ := by
    simp [RetainedSsaMap.Realizes, RetainedOperandsAt]
  obtain ⟨_, scopes, _⟩ := bindCallParams_frame ⟨middle.nextAct, [], {}, env.depth + 1⟩
    ((List.range impl.params.size).zip (callEntryTypes impl)) (values.map RVal.val)
  have frameScopes : (callFrame impl middle.nextAct (env.depth + 1) values).scopes = [] := by
    simpa only [callFrame] using scopes
  obtain ⟨bodyFuel, bodyDone, bodyResult, fullTrace, post, finalRealized⟩ :=
    accepted_generated_parameterized_callee_return ready.source rfl (by simpa using fragment) noResults noValue
      (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
      (by simpa [frameScopes] using steps) returned
  exact ⟨bodyFuel, bodyDone, fullTrace, post⟩

#print axioms accepted_generated_callee_actual_return
#print axioms accepted_generated_callee_ready
end Goose.Lower
