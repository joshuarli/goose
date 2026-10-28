import Goose.Lower.DemandRecursiveNestedCallLoopBlock
import Goose.Lower.DemandWhileCallEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_recursive_nested_call_entry_body {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel : Nat} (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = globalFuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals globalFuel ⟨cfg.profile, lower cfg.mod⟩ (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (positive : 1 < globalFuel)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ middle : St, NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none) :
    ∃ source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body { state with nextAct := state.nextAct + 1 },
      (∀ {taken : Nat} {reached : DemandRuntimePoint},
        DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
          ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩ reached →
        GeneratedGenericBranchBlockDecomposition (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩)
          (results := impl.results.toList) source (.context contextAt implAt) ⟨[], []⟩ ⟨[], []⟩ (callEntry impl) none
          (callFrame impl state.nextAct 1 []) (0, 0)
          (@NestedCallLoopCursor cfg (lowerContextAt cfg.mod ctx impl) impl.results.toList (.block impl.body) cfg.mod.entry
            (Place._sizeOf_11 impl.body.stmts) (⟨impl.vars, state.nextAct, [(impl.body.scope, state.nextScope)], 1⟩ : Env) none (.context contextAt implAt)) taken reached) ∧
      (∀ {taken : Nat} {reached : DemandRuntimePoint},
        DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
          ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩ reached →
        ∀ {targetFuel : Nat} {stop : Stop} {after : St},
          DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ targetFuel reached stop after → stop ≠ .timeout →
          StoppedLoopBranchBlockPrefix source ⟨[], []⟩ ⟨[], []⟩
            ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList (callEntry impl) none
            (callFrame impl state.nextAct 1 []) (0, 0) taken reached stop after) := by
  obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
  obtain ⟨actualCtx, actualImpl, actualContextAt, actualImplAt, noParameters, _, _⟩ :=
    acceptedEntryAfterGlobals accepted sourceFuel sourceInitialized
  have ctxEq : actualCtx = ctx := Option.some.inj (actualContextAt.symm.trans contextAt)
  subst actualCtx
  have implEq : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
  subst actualImpl
  obtain ⟨ready⟩ := accepted_generated_entry_body_ready accepted sourceInitialized contextAt implAt
  have entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl state.nextAct 1 []) { state with nextAct := state.nextAct + 1 } := by
    apply RuntimePoint.entry (fuel := globalFuel) (before := state) positive
    · simpa [lower] using initialized
    · simpa [lower] using lower_func_at contextAt implAt
    · exact lowered_function_entry_generated (cfg := cfg) (ctx := ctx) (impl := impl)
        (depth := 1) (values := []) (state := state) (by simpa using noParameters)
  refine ⟨ready.source, ?_⟩
  exact accepted_generated_recursive_nested_call_loop_body ready.source (fragment state) noValue
    (.context contextAt implAt) ready.owned ready.occurrence ready.rows ready.coverage ready.admitted ready.bounded ready.realized
    ready.input ready.extended entry

#print axioms accepted_generated_recursive_nested_call_entry_body
end Goose.Lower
