import Goose.Lower.Validation.CfgReconstructedEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

structure LowerCfgSourceCertificates (module : Core.Module) : Prop where
  functions : ∀ (index : Nat) (context : Context) (impl : Core.Impl), module.contexts[index]? = some context →
    module.impls[context.impl]? = some impl →
    EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl) ∧
    MutableSnapshotGraphs (lower module) (lowerContextAt module context impl) (cfg_implState module impl)
  globals : ∀ (index : Nat) (global : Core.Global), module.globals[index]? = some global →
    EmittedBuilder (lowerEnv module #[] [global.ty]) initState (cfg_globalState module global) ∧
    MutableSnapshotGraphs (lower module) (lowerGlobal module global).init (cfg_globalState module global)

theorem lower_cfgFacts_of_accepted_source_certificates {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (certificates : LowerCfgSourceCertificates module)
    (func : Func) (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    CfgFacts func (func.valueTypes (lower module)) := by
  have moduleOk := validate_modOk module accepted
  rcases List.mem_append.mp member with implementation | initializer
  · change func ∈ (module.contexts.map fun context =>
        match (module.impls.map fun impl =>
          (impl, lowerImplFromState module impl (lowerImplState module impl), lowerImplState module impl))[context.impl]? with
        | some (impl, body, state) => { body with roots := { lowerContextRootInfo context impl with
            values := lowerContextValueRoots module context impl state } }
        | none => invalidContextFunction context).toList at implementation
    simp only [Array.toList_map, List.mem_map] at implementation
    obtain ⟨context, contextMember, equality⟩ := implementation
    obtain ⟨index, contextRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp contextMember)
    obtain ⟨impl, implRow, _⟩ := moduleOk.ctx index context contextRow
    rw [Array.getElem?_map, implRow] at equality
    simp only [Option.map_some] at equality
    subst func
    obtain ⟨builder, graphs⟩ := certificates.functions index context impl contextRow implRow
    obtain ⟨type, finish, typed, _⟩ := (moduleOk.impl context.impl impl implRow).body
    exact lowerContextAt_cfgFacts_of_source_certificates typed builder graphs
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, sourceMember, rfl⟩ := globalMember
    obtain ⟨index, sourceRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp sourceMember)
    obtain ⟨builder, graphs⟩ := certificates.globals index source sourceRow
    obtain ⟨finish, typed⟩ := (moduleOk.glob index source sourceRow).init
    exact lowerGlobal_cfgFacts_of_source_certificates typed builder graphs

private theorem checkAll_success {items : List α} {action : α → Except ε Unit}
    (checked : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [checkAll, checked item (by simp), bind, Except.bind]
    exact ih fun next member => checked next (by simp [member])

theorem lower_checkCfg_of_accepted_source_certificates {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (certificates : LowerCfgSourceCertificates module) :
    checkAll (lower module).infos (fun info => checkCfg info.label info.f info.vt) = .ok () := by
  apply checkAll_success
  intro info member
  unfold GIR.Module.infos at member
  obtain ⟨⟨label, func⟩, labelledMember, rfl⟩ := List.mem_map.mp member
  apply cfgFacts_checked (lower_cfgFacts_of_accepted_source_certificates accepted certificates func ?_) label
  unfold GIR.Module.labelled at labelledMember
  rcases List.mem_append.mp labelledMember with implementation | initializer
  · obtain ⟨body, present, same⟩ := List.mem_map.mp implementation
    have sameBody : body = func := congrArg Prod.snd same
    exact List.mem_append_left _ (sameBody ▸ present)
  · obtain ⟨global, present, same⟩ := List.mem_map.mp initializer
    have initMember : global.init ∈ (lower module).globals.toList.map (·.init) :=
      List.mem_map.mpr ⟨global, present, rfl⟩
    have sameInit : global.init = func := congrArg Prod.snd same
    exact List.mem_append_right _ (sameInit ▸ initMember)

end Goose.Lower.Validation
