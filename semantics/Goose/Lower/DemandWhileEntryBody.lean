import Goose.Lower.DemandWhileMixedBranch

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Lower

structure EntryBodyDemandReady (cfg : Cfg) (state : St) (ctx : Context) (impl : Impl)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl) where
  source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body { state with nextAct := state.nextAct + 1 }
  owned : GeneratedSourceOwner (.context contextAt implAt) source.context
  occurrence : GeneratedDemandOccurrence cfg.mod (lowerContextAt cfg.mod ctx impl)
    (lowerEnv cfg.mod impl.vars impl.results.toList) (.block impl.body) source.path
    (.block none [] false impl.body) (callEntry impl)
  rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence ⟨[], []⟩
  input : GeneratedPrefixInput cfg ⟨impl.vars, state.nextAct, [], 1⟩
    ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList none
    source.typingEnv source.rootsEnv (callEntry impl) (callFrame impl state.nextAct 1 []) (0, 0)
  extended : ExtT (lowerBlock none [] false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
    (lowerContextAt cfg.mod ctx impl).blocks
  coverage : (⟨[], []⟩ : RetainedSsaMap).Covers ⟨[], []⟩
  admitted : (⟨[], []⟩ : RetainedSsaMap).Admitted cfg.mod.profile source.context.retained
  bounded : (⟨[], []⟩ : RetainedSsaMap).Bounded (callEntry impl).vals.size
  realized : (⟨[], []⟩ : RetainedSsaMap).Realizes cfg.mod source.world ⟨impl.vars, state.nextAct, [], 1⟩
    ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩

theorem accepted_generated_entry_body_ready {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    (accepted : Core.validate cfg.mod = .ok ()) {fuel : Nat}
    (initialized : initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl) :
    Nonempty (EntryBodyDemandReady cfg state ctx impl contextAt implAt) := by
  obtain ⟨actualCtx, actualImpl, actualContextAt, actualImplAt, noParameters, noResults, source, typing, roots, path, sourceOwner⟩ :=
    acceptedEntryAfterGlobals accepted fuel initialized
  have ctxEq : actualCtx = ctx := Option.some.inj (actualContextAt.symm.trans contextAt)
  subst actualCtx
  have implEq : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
  subst actualImpl
  have emptyPre : (impl.params.toList.zip ([] : List Val) |>.map (fun item => (item.1.var, item.2))) = [] := by
    simp
  generalize preEq : (impl.params.toList.zip ([] : List Val) |>.map (fun item => (item.1.var, item.2))) = pre at source typing roots path sourceOwner
  have preIsEmpty : pre = [] := preEq.symm.trans emptyPre
  clear preEq
  subst pre
  have preEmpty : callPre impl = [] := by simp [callPre, noParameters]
  let selected : GeneratedDemandRootSelection cfg.mod (lowerContextAt cfg.mod ctx impl)
      (lowerEnv cfg.mod impl.vars impl.results.toList) (.block impl.body) cfg.mod.entry := .context contextAt implAt
  have owned : GeneratedSourceOwner selected source.context := by
    refine ⟨sourceOwner, ?_⟩
    rw [path]
    exact .here _
  have occurrence : GeneratedDemandOccurrence cfg.mod (lowerContextAt cfg.mod ctx impl)
      (lowerEnv cfg.mod impl.vars impl.results.toList) (.block impl.body) source.path
      (.block none [] false impl.body) (callEntry impl) := by
    rw [path, ← preEmpty]
    exact .functionRoot contextAt implAt
  have rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence ⟨[], []⟩ := by
    simpa only [path, preEmpty] using
      (GeneratedDemandRows.functionRoot (contextAt := contextAt) (implementationAt := implAt) (by rw [roots]))
  have metadata : SourceResults source.typingEnv source.rootsEnv impl.results.toList := by
    intro actual equal
    rw [typing] at equal
    simp [implEnv] at equal
    subst actual
    simp [roots]
  have input : GeneratedPrefixInput cfg ⟨impl.vars, state.nextAct, [], 1⟩
      ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList none
      source.typingEnv source.rootsEnv (callEntry impl) (callFrame impl state.nextAct 1 []) (0, 0) := by
    refine ⟨metadata, ?_, callEntry_pp impl, callFrame_rel _ _ _ _ _ _ _, rfl, ?_, trivial, trivial, trivial,
      callEntry_generated cfg.mod impl, trivial⟩
    · rw [typing]
      simp [LoopSourceMatches, implEnv]
    · rfl
  have bodyExt : ExtT (lowerBlock none [] false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
      (lowerContextAt cfg.mod ctx impl).blocks := by
    rw [← preEmpty]
    let body := lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)
    have tailExt : ExtT (bodyTail impl (lowerEnv cfg.mod impl.vars impl.results.toList) body.1 body.2)
        (lowerContextAt cfg.mod ctx impl).blocks := by
      rw [lowerContextAt_blocks, lowerImpl_call_blocks]
      exact extT_finish _
    exact tailExt.of_adv (advB_finishFunction impl body.1 _ body.2 _ _ rfl)
  refine ⟨⟨source, owned, occurrence, rows, input, bodyExt, ?_, ?_, ?_, ?_⟩⟩
  · simp [RetainedSsaMap.Covers]
  · simp [RetainedSsaMap.Admitted]
  · simp [RetainedSsaMap.Bounded]
  · simp [RetainedSsaMap.Realizes, RetainedOperandsAt]

theorem accepted_generated_entry_body_prefix {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    (accepted : Core.validate cfg.mod = .ok ()) {fuel : Nat}
    (initialized : initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩ reached) :
    ∃ source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body { state with nextAct := state.nextAct + 1 },
      GeneratedGenericBranchBlockDecomposition (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩)
        (results := impl.results.toList) source (.context contextAt implAt) ⟨[], []⟩ ⟨[], []⟩ (callEntry impl) none
        (callFrame impl state.nextAct 1 []) (0, 0)
        (@WhileMixedStatementCursor cfg
          { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, state.nextScope) :: [], depth := 1 }
          ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList
          (.block impl.body) cfg.mod.entry (.context contextAt implAt)) taken reached := by
  obtain ⟨ready⟩ := accepted_generated_entry_body_ready accepted initialized contextAt implAt
  refine ⟨ready.source, ?_⟩
  exact accepted_generated_while_mixed_branch_block_prefix ready.source (fragment _) (.context contextAt implAt)
    ready.owned ready.occurrence ready.rows ready.coverage ready.admitted ready.bounded ready.realized ready.input ready.extended noValue steps


theorem accepted_generated_entry_body_stopped {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    (accepted : Core.validate cfg.mod = .ok ()) {fuel : Nat}
    (initialized : initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩ reached) {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body { state with nextAct := state.nextAct + 1 },
      StoppedLoopBranchBlockPrefix source ⟨[], []⟩ ⟨[], []⟩
        ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList (callEntry impl) none
        (callFrame impl state.nextAct 1 []) (0, 0) taken reached stop after := by
  obtain ⟨ready⟩ := accepted_generated_entry_body_ready accepted initialized contextAt implAt
  refine ⟨ready.source, ?_⟩
  exact accepted_generated_while_mixed_branch_block_stopped ready.source (.context contextAt implAt)
    ready.owned ready.occurrence ready.rows ready.coverage ready.admitted ready.bounded ready.realized ready.input ready.extended (fragment _) noValue steps stopped nonTimeout

#print axioms accepted_generated_entry_body_ready
#print axioms accepted_generated_entry_body_prefix
#print axioms accepted_generated_entry_body_stopped
end Goose.Lower
