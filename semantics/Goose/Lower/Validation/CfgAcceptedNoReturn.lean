import Goose.Lower.Validation.CfgNoReturnModule
import Goose.Lower.Validation.CfgReturnFreeTyping
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem accepted_sourceStoppingReturnFree {module : Core.Module}
    (accepted : Core.validate module = .ok ()) : SourceStoppingReturnFree module := by
  intro callee context impl contextRow implRow stopped
  have checked := (Core.Sound.validate_modOk module accepted).impl context.impl impl implRow
  obtain ⟨bodyTy, finish, typed, _⟩ := checked.body
  have bodyStops : impl.body.stops module.noReturn = true := by
    obtain ⟨actualContext, actualImpl, actualContextRow, actualImplRow, actualStops⟩ :=
      core_noReturn_body_stops module callee stopped
    have sameContext : actualContext = context := Option.some.inj (actualContextRow.symm.trans contextRow)
    subst actualContext
    have sameImpl : actualImpl = impl := Option.some.inj (actualImplRow.symm.trans implRow)
    simpa only [sameImpl] using actualStops
  exact tyBlock_returnFreeStopping module.noReturn impl.body [] typed bodyStops

theorem lower_noReturn_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    ∀ callee, module.noReturn callee = true → (lower module).functionsMayReturn[callee]?.getD true = false :=
  lower_noReturn_of_source module (accepted_sourceStoppingReturnFree accepted)

theorem lower_checkUnreachable_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    checkUnreachable (lower module) = .ok () :=
  lower_checkUnreachable_of_source module (accepted_sourceStoppingReturnFree accepted)

end Goose.Lower.Validation
