import Goose.Lower.FuelBoundInduction

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem lowered_done_at_source_fuel_bound {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (profile : NumProfile) (targetFuel : Nat)
    {outcome : Outcome} {trace : String}
    (done : GIR.run targetFuel profile (lower module) = .done outcome trace) :
    Core.eval (loweringSourceFuelBound module targetFuel) profile module = .done outcome trace := by
  have bounded := acceptedModule_fuelBound (cfg := ⟨profile,module⟩) accepted targetFuel
  cases run : GIR.runModule targetFuel ⟨profile,lower module⟩ St.initial with
  | ok value after =>
    have sourceRun := bounded (.ok value after) (NonTimeout.ok _ _) run
    simpa only [Core.eval,sourceRun,GIR.run,run] using done
  | stop stop after =>
    cases stop with
    | abort kind origin =>
      have sourceRun := bounded (.stop (.abort kind origin) after) (by intro next equal; cases equal) run
      simpa only [Core.eval,sourceRun,GIR.run,run] using done
    | exit code =>
      have sourceRun := bounded (.stop (.exit code) after) (by intro next equal; cases equal) run
      simpa only [Core.eval,sourceRun,GIR.run,run] using done
    | fault kind => simp [GIR.run,run] at done
    | timeout => simp [GIR.run,run] at done

theorem lowered_timeout_of_source_fuel_bound {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (profile : NumProfile) (targetFuel : Nat)
    {trace : String}
    (sourceTimeout : Core.eval (loweringSourceFuelBound module targetFuel) profile module = .timeout trace) :
    ∃ targetTrace, GIR.run targetFuel profile (lower module) = .timeout targetTrace := by
  have bounded := acceptedModule_fuelBound (cfg := ⟨profile,module⟩) accepted targetFuel
  cases sourceRun : Core.runModule (loweringSourceFuelBound module targetFuel) ⟨profile,module⟩ St.initial with
  | ok value after => simp [Core.eval,sourceRun] at sourceTimeout
  | stop stop after =>
    cases stop with
    | abort kind origin => simp [Core.eval,sourceRun] at sourceTimeout
    | exit code => simp [Core.eval,sourceRun] at sourceTimeout
    | fault kind => simp [Core.eval,sourceRun] at sourceTimeout
    | timeout =>
      obtain ⟨stopped,targetRun⟩ := bounded.timeout_of_source sourceRun
      exact ⟨stopped.trace,by simp [GIR.run,targetRun]⟩

theorem lowering_diverges_with_fuel_bound {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (profile : NumProfile)
    (diverges : ∀ sourceFuel, ∃ trace, Core.eval sourceFuel profile module = .timeout trace) :
    ∀ targetFuel, ∃ trace, GIR.run targetFuel profile (lower module) = .timeout trace := by
  intro targetFuel
  obtain ⟨trace,sourceTimeout⟩ := diverges (loweringSourceFuelBound module targetFuel)
  exact lowered_timeout_of_source_fuel_bound accepted profile targetFuel sourceTimeout

end Goose.Lower
