import Goose.Lower.DemandWhileTargetEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_entry_body_stop_to_module {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel bodyFuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (initialized : Core.initGlobals globalFuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (bodyStop : execBlock bodyFuel cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body
      { state with nextAct := state.nextAct + 1 } = .stop stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ fuel, Core.runModule fuel cfg St.initial = .stop stop after := by
  obtain ⟨actualCtx, actualImpl, actualContextAt, actualImplAt, noParameters, _, _⟩ :=
    acceptedEntryAfterGlobals accepted globalFuel initialized
  have ctxEq : actualCtx = ctx := Option.some.inj (actualContextAt.symm.trans contextAt)
  subst actualCtx
  have implEq : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
  subst actualImpl
  have emptyParameters : impl.params = #[] := Array.size_eq_zero_iff.mp noParameters
  have callStop : Core.enterCall (bodyFuel + 1) cfg 0 cfg.mod.entry [] state = .stop stop after := by
    simp [Core.enterCall, Core.lookupContext, Core.lookupImpl, contextAt, implAt, emptyParameters, Core.maxCallDepth,
      freshAct, bind_apply, pure_apply, bodyStop]
  let fuel := max globalFuel (bodyFuel + 1)
  have globals : Core.initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state :=
    (Goose.Proofs.Fuel.MonoM.initGlobals globalFuel fuel (by dsimp [fuel]; omega) cfg _ St.initial).1 () state initialized
  have called : Core.enterCall fuel cfg 0 cfg.mod.entry [] state = .stop stop after := by
    have agrees := (Goose.Proofs.Fuel.monoAll (bodyFuel + 1) fuel (by dsimp [fuel]; omega)).call cfg 0 cfg.mod.entry [] state
    rcases agrees.2 stop after callStop with timeout | done
    · cases stop <;> simp [Goose.Proofs.Fuel.isTimeout] at timeout
      exact (nonTimeout rfl).elim
    · exact done
  refine ⟨fuel, ?_⟩
  change (Core.initGlobals fuel cfg (List.range cfg.mod.globals.size) >>= fun _ =>
    Core.enterCall fuel cfg 0 cfg.mod.entry [] >>= fun _ => pure ()) St.initial = .stop stop after
  simp only [bind_apply, globals, called]

#print axioms accepted_entry_body_stop_to_module
end Goose.Lower
