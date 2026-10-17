import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem checkAll_success {items : List α} {action : α → Except ε Unit}
    (checked : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
    simp only [checkAll, checked item (by simp), bind, Except.bind]
    exact inductionHypothesis (fun next member => checked next (by simp [member]))

private theorem bind_success {action : Except ε α} {next : α → Except ε β} {value : α} {result : β}
    (first : action = .ok value) (remaining : next value = .ok result) :
    (action >>= next) = .ok result := by
  rw [first]
  exact remaining

private theorem validate_of_stages (module : GIR.Module)
    (entry : checkEntryAndGlobals module = .ok ())
    (symbols : checkAll module.labelled (fun (label, func) => checkSymbols module label func) = .ok ())
    (structs : checkStructTypes module = .ok ())
    (types : checkAll module.infos (fun info => checkTypes module info.label info.f info.vt) = .ok ())
    (cfg : checkAll module.infos (fun info => checkCfg info.label info.f info.vt) = .ok ())
    (unreachable : checkUnreachable module = .ok ())
    (storageWalks : checkAll (module.infos.map fun info => walkScopes info.label info.f) (fun walk => do
      if let some message := walk.storage then violation .v030 message) = .ok ())
    (storage : checkAll module.infos (fun info => checkStorage module info.label info.f info.vt) = .ok ())
    (permissions : checkAll module.infos (fun info => checkPermissions module info.label info.f info.vt) = .ok ())
    (scopes : checkAll (module.infos.map fun info => walkScopes info.label info.f) (fun walk => do
      if let some message := walk.scopes then violation .v040 message) = .ok ())
    (summaries : checkAll (List.range module.funcs.size)
      (checkSummaryOf module module.implTypes (resultRoots module module.implTypes) module.rootCount) = .ok ())
    (replacement : checkAll module.infos (fun info =>
      let provenance := info.f.provenance (resultRoots module module.implTypes) info.vt module.rootCount
      checkShrinkReplace module info.label info.f info.vt provenance) = .ok ())
    (evidence : checkAll module.infos (fun info => asCheck .v080 info.label (checkEvidence module info.f info.vt)) = .ok ())
    (origins : checkAll module.infos (fun info => checkOrigins module.profile info.label info.f) = .ok ()) :
    GIR.validate module = .ok () := by
  unfold GIR.validate
  rw [entry, symbols, structs, types, cfg, unreachable]
  simp only [bind, Except.bind]
  apply bind_success (value := ())
  · apply checkAll_success
    intro pair member
    rcases pair with ⟨info, walk⟩
    have infoMember := (List.of_mem_zip member).1
    have walkMember := (List.of_mem_zip member).2
    have walkChecked := checkAll_ok storageWalks walk walkMember
    have storageChecked := checkAll_ok storage info infoMember
    have permissionsChecked := checkAll_ok permissions info infoMember
    cases found : walk.storage with
    | none => simp [storageChecked, permissionsChecked]
    | some message => simp [found, violation] at walkChecked
  · apply bind_success (value := ())
    · apply checkAll_success
      intro walk member
      have checked := checkAll_ok scopes walk member
      cases found : walk.scopes with
      | none => simp [pure, Except.pure]
      | some message => simp [found, violation] at checked
    · rw [summaries, replacement, evidence, origins]

end Goose.Lower.Validation
