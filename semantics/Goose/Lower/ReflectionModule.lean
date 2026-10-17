import Goose.Lower.ReflectionGlobals
import Goose.Lower.TypedEntry

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedEntry_reflection {cfg : Cfg} {state : St} {fuel globalFuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (initialized : Core.initGlobals globalFuel cfg (List.range cfg.mod.globals.size) St.initial =
      .ok () state)
    (blocks : ∀ bodyFuel, bodyFuel + 2 = fuel → ∀ (context : Context) (impl : Impl),
      cfg.mod.contexts[cfg.mod.entry]? = some context → cfg.mod.impls[context.impl]? = some impl →
      TypedBlockReflection bodyFuel cfg impl.results.toList none (callPre impl) [] false impl.body) :
    ReflectMFuel fuel (fun n => Core.enterCall n cfg 0 cfg.mod.entry [])
      (fun n => GIR.callFn n ⟨cfg.profile,lower cfg.mod⟩ 0 (lower cfg.mod).entry []) state := by
  obtain ⟨context,impl,contextAt,implAt,noParams,noResults,source,typing,roots⟩ :=
    acceptedEntryAfterGlobals accepted globalFuel initialized
  apply callFn_reflect_of_source contextAt implAt source
  · rw [typing]
    rfl
  · rw [roots]
  · rw [typing]
    rfl
  · intro bodyFuel equal
    simpa using blocks bodyFuel equal context impl contextAt implAt

theorem typedModule_reflection {cfg : Cfg} {fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (blocks : ∀ bodyFuel, bodyFuel + 2 = fuel → ∀ (context : Context) (impl : Impl),
      cfg.mod.contexts[cfg.mod.entry]? = some context → cfg.mod.impls[context.impl]? = some impl →
      TypedBlockReflection bodyFuel cfg impl.results.toList none (callPre impl) [] false impl.body) :
    ReflectMFuel fuel (fun n => Core.runModule n cfg)
      (fun n => GIR.runModule n ⟨cfg.profile,lower cfg.mod⟩) St.initial := by
  unfold Core.runModule GIR.runModule
  have sizes : (lower cfg.mod).globals.size = cfg.mod.globals.size := by simp [lower]
  rw [sizes]
  refine ReflectMFuel.bind_success (typedGlobals_reflection accepted expressions) ?_
    (fun n k bound => MonoM.initGlobals n k bound cfg _) ?_
  · intro n ignored state initialized
    have ignoredEq : ignored = () := Subsingleton.elim _ _
    subst ignored
    refine ReflectMFuel.bind_success (typedEntry_reflection accepted initialized blocks) ?_
      (fun n k bound => (monoAll n k bound).call cfg 0 cfg.mod.entry []) ?_
    · intro k value after evaluated
      exact ReflectMFuel.of_eq (sourceFuel := 0) rfl
    · intro value n k bound
      exact MonoM.refl _
  · intro ignored n k bound
    exact MonoM.bind ((monoAll n k bound).call cfg 0 cfg.mod.entry []) (fun _ => MonoM.refl _)

end Goose.Lower
