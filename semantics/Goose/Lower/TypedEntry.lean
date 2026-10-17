import Goose.Lower.TypedGlobals
import Goose.Lower.TypedCall

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem typedEntry_simulation {cfg : Cfg} {state : St} (n globalFuel : Nat)
    (accepted : Core.validate cfg.mod = .ok ())
    (initialized : Core.initGlobals globalFuel cfg (List.range cfg.mod.globals.size) St.initial =
      .ok () state)
    (hbody : ∀ (context : Context) (impl : Impl), cfg.mod.contexts[cfg.mod.entry]? = some context →
      cfg.mod.impls[context.impl]? = some impl →
      TypedBlockLoopSimulation n cfg impl.results.toList none (callPre impl) [] false impl.body) :
    EventualM (Core.enterCall (n + 1) cfg 0 cfg.mod.entry [])
      (fun fuel => GIR.callFn fuel ⟨cfg.profile, lower cfg.mod⟩ 0 (lower cfg.mod).entry []) state := by
  obtain ⟨context, impl, contextAt, implAt, noParams, noResults, source, typingEq, rootsEq⟩ :=
    acceptedEntryAfterGlobals accepted globalFuel initialized
  apply typedCall_of_body contextAt implAt cfg.profile n 0 [] state
  intro arity
  apply calleeBodyAt_of_typedBlock arity source
  · rw [typingEq]
    rfl
  · rw [rootsEq]
  · rw [typingEq]
    rfl
  · simpa using hbody context impl contextAt implAt

theorem typedModule_simulation_succ {cfg : Cfg} (n : Nat)
    (accepted : Core.validate cfg.mod = .ok ())
    (hglobals : ∀ (id : GlobalId) (global : Core.Global), cfg.mod.globals[id]? = some global →
      TypedExprClaim (n + 1) cfg [global.ty] global.init)
    (hentry : ∀ (context : Context) (impl : Impl), cfg.mod.contexts[cfg.mod.entry]? = some context →
      cfg.mod.impls[context.impl]? = some impl →
      TypedBlockLoopSimulation n cfg impl.results.toList none (callPre impl) [] false impl.body) :
    EventualM (Core.runModule (n + 1) cfg)
      (fun fuel => GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩) St.initial := by
  unfold Core.runModule GIR.runModule
  have sizes : (lower cfg.mod).globals.size = cfg.mod.globals.size := by simp [lower]
  rw [sizes]
  apply EventualM.bind (typedGlobals_simulation (n + 1) accepted hglobals)
  intro unit state initialized
  have unitEq : unit = () := Subsingleton.elim _ _
  subst unit
  exact EventualM.bind (typedEntry_simulation n (n + 1) accepted initialized hentry)
    (fun value after _ => EventualM.refl (pure () : M Unit) after)

end Goose.Lower
