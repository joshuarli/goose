import Goose.Lower.Validation.JoinTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_signatureTables (module : Core.Module) :
    (lower module).funcs.map (fun func => (func.params, func.results)) =
      (lowerEnv module #[] []).sigs := by
  apply Array.ext
  · simp [lower, lowerEnv]
  · intro index leftBound rightBound
    have bound : index < module.contexts.size := by simpa [lowerEnv] using rightBound
    simp only [lower, lowerEnv, Array.getElem_map, Array.getElem?_map]
    cases row : module.impls[(module.contexts[index]'bound).impl]? <;> simp [invalidContextFunction, lowerImpl]

theorem lower_globalTypeTables (module : Core.Module) :
    (lower module).globals.map (fun global => (global.ty, global.kind)) =
      (lowerEnv module #[] []).globals := by
  simp [lower, lowerEnv, lowerGlobal, Array.map_map]

theorem lowerImpl_typingTables (module : Core.Module) (impl : Core.Impl) (state : LS) :
    ((lower module).tyEnv (lowerImpl module impl)).slots =
        (tyEnv (lowerEnv module impl.vars impl.results.toList) state).slots ∧
      ((lower module).tyEnv (lowerImpl module impl)).globals =
        (tyEnv (lowerEnv module impl.vars impl.results.toList) state).globals ∧
      ((lower module).tyEnv (lowerImpl module impl)).sigs =
        (tyEnv (lowerEnv module impl.vars impl.results.toList) state).sigs ∧
      ((lower module).tyEnv (lowerImpl module impl)).structs =
        (tyEnv (lowerEnv module impl.vars impl.results.toList) state).structs ∧
      ((lower module).tyEnv (lowerImpl module impl)).profile =
        (tyEnv (lowerEnv module impl.vars impl.results.toList) state).profile := by
  refine ⟨rfl, ?_, ?_, rfl, rfl⟩
  · exact lower_globalTypeTables module
  · exact lower_signatureTables module

theorem lowerGlobal_typingTables (module : Core.Module) (global : Core.Global) (state : LS) :
    ((lower module).tyEnv (lowerGlobal module global).init).slots =
        (tyEnv (lowerEnv module #[] [global.ty]) state).slots ∧
      ((lower module).tyEnv (lowerGlobal module global).init).globals =
        (tyEnv (lowerEnv module #[] [global.ty]) state).globals ∧
      ((lower module).tyEnv (lowerGlobal module global).init).sigs =
        (tyEnv (lowerEnv module #[] [global.ty]) state).sigs ∧
      ((lower module).tyEnv (lowerGlobal module global).init).structs =
        (tyEnv (lowerEnv module #[] [global.ty]) state).structs ∧
      ((lower module).tyEnv (lowerGlobal module global).init).profile =
        (tyEnv (lowerEnv module #[] [global.ty]) state).profile := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · rfl
  · exact lower_globalTypeTables module
  · exact lower_signatureTables module

end Goose.Lower.Validation
