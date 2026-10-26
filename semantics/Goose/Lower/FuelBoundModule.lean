import Goose.Lower.FuelBoundGlobals
import Goose.Lower.TypedEntry

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedEntry_fuelBound {cfg : Cfg} {state : St} {sourceFuel fuel globalFuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (initialized : Core.initGlobals globalFuel cfg (List.range cfg.mod.globals.size) St.initial =
      .ok () state)
    (blocks : ∀ bodyFuel, bodyFuel + 2 = fuel → ∀ (context : Context) (impl : Impl),
      cfg.mod.contexts[cfg.mod.entry]? = some context → cfg.mod.impls[context.impl]? = some impl →
      TypedBlockFuelBound sourceFuel bodyFuel cfg impl.results.toList none (callPre impl) [] false impl.body) :
    FuelBoundM (sourceFuel + 1) fuel (fun n => Core.enterCall n cfg 0 cfg.mod.entry [])
      (fun n => GIR.callFn n ⟨cfg.profile,lower cfg.mod⟩ 0 (lower cfg.mod).entry []) state := by
  obtain ⟨context,impl,contextAt,implAt,noParams,noResults,source,typing,roots, _, _⟩ :=
    acceptedEntryAfterGlobals accepted globalFuel initialized
  apply callFn_fuelBound_of_source contextAt implAt source
  · rw [typing]
    rfl
  · rw [roots]
  · rw [typing]
    rfl
  · intro bodyFuel equal
    simpa using blocks bodyFuel equal context impl contextAt implAt

theorem typedModule_fuelBound {cfg : Cfg} {sourceFuel fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global →
      TypedExprFuelBound (sourceFuel + 1) residual cfg [global.ty] global.init)
    (blocks : ∀ bodyFuel, bodyFuel + 2 = fuel → ∀ (context : Context) (impl : Impl),
      cfg.mod.contexts[cfg.mod.entry]? = some context → cfg.mod.impls[context.impl]? = some impl →
      TypedBlockFuelBound sourceFuel bodyFuel cfg impl.results.toList none (callPre impl) [] false impl.body) :
    FuelBoundM (sourceFuel + 1) fuel (fun n => Core.runModule n cfg)
      (fun n => GIR.runModule n ⟨cfg.profile,lower cfg.mod⟩) St.initial := by
  unfold Core.runModule GIR.runModule
  have sizes : (lower cfg.mod).globals.size = cfg.mod.globals.size := by simp [lower]
  rw [sizes]
  refine FuelBoundM.bind_success (typedGlobals_fuelBound accepted expressions) ?_
  intro ignored state initialized
  have ignoredEq : ignored = () := Subsingleton.elim _ _
  subst ignored
  refine FuelBoundM.bind_success (typedEntry_fuelBound accepted initialized blocks) ?_
  intro value after evaluated
  exact FuelBoundM.of_eq rfl

end Goose.Lower
