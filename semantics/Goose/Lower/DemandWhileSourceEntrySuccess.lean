import Goose.Lower.DemandWhileSourceEntryStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_entry_body_success_to_module {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel bodyFuel : Nat} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (initialized : Core.initGlobals globalFuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (bodyDone : execBlock bodyFuel cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body
      { state with nextAct := state.nextAct + 1 } = .ok (.normal .unit) after) :
    ∃ fuel, Core.runModule fuel cfg St.initial = .ok () after := by
  obtain ⟨actualCtx, actualImpl, actualContextAt, actualImplAt, noParameters, _, _⟩ :=
    acceptedEntryAfterGlobals accepted globalFuel initialized
  have ctxEq : actualCtx = ctx := Option.some.inj (actualContextAt.symm.trans contextAt)
  subst actualCtx
  have implEq : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
  subst actualImpl
  have emptyParameters : impl.params = #[] := Array.size_eq_zero_iff.mp noParameters
  have callDone : Core.enterCall (bodyFuel + 1) cfg 0 cfg.mod.entry [] state = .ok .unit after := by
    simp [Core.enterCall, Core.lookupContext, Core.lookupImpl, contextAt, implAt, emptyParameters, Core.maxCallDepth,
      freshAct, bind_apply, pure_apply, bodyDone, expectReturned]
  let fuel := max globalFuel (bodyFuel + 1)
  have globals : Core.initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state :=
    (Goose.Proofs.Fuel.MonoM.initGlobals globalFuel fuel (by dsimp [fuel]; omega) cfg _ St.initial).1 () state initialized
  have called : Core.enterCall fuel cfg 0 cfg.mod.entry [] state = .ok .unit after :=
    ((Goose.Proofs.Fuel.monoAll (bodyFuel + 1) fuel (by dsimp [fuel]; omega)).call cfg 0 cfg.mod.entry [] state).1 _ _ callDone
  refine ⟨fuel, ?_⟩
  change (Core.initGlobals fuel cfg (List.range cfg.mod.globals.size) >>= fun _ =>
    Core.enterCall fuel cfg 0 cfg.mod.entry [] >>= fun _ => pure ()) St.initial = .ok () after
  simp only [bind_apply, globals, called, pure_apply]

#print axioms accepted_entry_body_success_to_module
end Goose.Lower
