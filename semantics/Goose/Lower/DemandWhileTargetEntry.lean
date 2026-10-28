import Goose.Lower.DemandWhileEntryBody
import Goose.Lower.ReflectionGlobals

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_source_globals_of_target {cfg : Cfg} {state : St} {fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range cfg.mod.globals.size) St.initial = .ok () state) :
    ∃ sourceFuel, Core.initGlobals sourceFuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state :=
  typedGlobals_reflection accepted expressions (.ok () state) (NonTimeout.ok () state) initialized

theorem accepted_generated_target_entry_ready {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl} {fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl) :
    Nonempty (EntryBodyDemandReady cfg state ctx impl contextAt implAt) := by
  obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
  exact accepted_generated_entry_body_ready accepted sourceInitialized contextAt implAt


theorem accepted_generated_target_entry_body_prefix {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    (accepted : Core.validate cfg.mod = .ok ()) {fuel : Nat}
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range cfg.mod.globals.size) St.initial = .ok () state)
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
  obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
  exact accepted_generated_entry_body_prefix accepted sourceInitialized contextAt implAt fragment noValue steps

theorem accepted_generated_target_entry_body_stopped {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    (accepted : Core.validate cfg.mod = .ok ()) {fuel : Nat}
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range cfg.mod.globals.size) St.initial = .ok () state)
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
  obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
  exact accepted_generated_entry_body_stopped accepted sourceInitialized contextAt implAt fragment noValue steps stopped nonTimeout


#print axioms accepted_source_globals_of_target
#print axioms accepted_generated_target_entry_ready
#print axioms accepted_generated_target_entry_body_prefix
#print axioms accepted_generated_target_entry_body_stopped
end Goose.Lower
