import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.GIR

theorem unit_bind_ok {error : Type} (first second : Except error Unit) :
    (first >>= fun _ => second) = .ok () ↔ first = .ok () ∧ second = .ok () := by
  cases first with
  | error rejection => simp [bind, Except.bind]
  | ok value => cases value; simp [bind, Except.bind]

theorem gir_validate_stages (module : Module) :
    let walks := module.infos.map fun info => walkScopes info.label info.f
    validate module = .ok () ↔
      checkEntryAndGlobals module = .ok () ∧
      (checkAll module.labelled fun (label, func) => checkSymbols module label func) = .ok () ∧
      checkStructTypes module = .ok () ∧
      (checkAll module.infos fun info => checkTypes module info.label info.f info.vt) = .ok () ∧
      (checkAll module.infos fun info => checkCfg info.label info.f info.vt) = .ok () ∧
      checkUnreachable module = .ok () ∧
      (checkAll (module.infos.zip walks) fun (info, walk) => do
        if let some message := walk.storage then violation .v030 message
        checkStorage module info.label info.f info.vt
        checkPermissions module info.label info.f info.vt) = .ok () ∧
      (checkAll walks fun walk => do
        if let some message := walk.scopes then violation .v040 message) = .ok () ∧
      asCheck .v050 "declared regions"
        (module.checkAdmittedRegions module.implTypes (resultRoots module module.implTypes) module.rootCount) = .ok () ∧
      (checkAll (List.range module.funcs.size)
        (checkSummaryOf module module.implTypes (resultRoots module module.implTypes) module.rootCount)) = .ok () ∧
      (checkAll module.infos fun info =>
        checkShrinkReplace module info.label info.f info.vt) = .ok () ∧
      (checkAll module.infos fun info =>
        asCheck .v080 info.label (checkEvidence module info.f info.vt)) = .ok () ∧
      (checkAll module.infos fun info => checkOrigins module.profile info.label info.f) = .ok () := by
  simp only [validate, checkShrinkReplace_canonical, unit_bind_ok]
  rfl

end Goose.Lower.Validation
