import Goose.Lower.Validation.SourceOrigins
import Goose.Lower.Validation.ShrinkOrigins

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_checkOrigins {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    (checkAll (lower module).infos fun info =>
      checkOrigins (lower module).profile info.label info.f) = .ok () := by
  cases profile : module.profile with
  | pilot =>
    change (checkAll (lower module).infos fun info =>
      checkOrigins module.profile info.label info.f) = .ok ()
    rw [profile]
    exact Origins.lower_checkOrigins_pilot module
  | shrink =>
    change (checkAll (lower module).infos fun info =>
      checkOrigins module.profile info.label info.f) = .ok ()
    rw [profile]
    exact ShrinkOrigins.lower_checkOrigins_shrink module
      (SourceOrigins.implementations_present accepted profile)
      (SourceOrigins.initializers_present accepted profile)

end Goose.Lower.Validation
