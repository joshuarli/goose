import Goose.Lower.Validation.SnapshotContentsFinish
import Goose.Lower.Validation.SnapshotContentsFinal
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Lower.GeneratedTargetFramesSource
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerImpl_snapshotSourceTrace {module : Core.Module} {impl : Core.Impl} {type : Ty} {finish : Nat}
    (typed : Core.tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish))
    (body : SnapshotSourceBlock (implEnv module impl) impl.results.toList impl.body) :
    SnapshotSourceTrace (lowerEnv module impl.vars impl.results.toList) 0
      (cfg_implState module impl) (cfg_implState module impl) := by
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let allocated := newBlock types le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let pre : List (SlotId × ValueId × OriginId) := (impl.params.toList.zip allocated.1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
  let output := lowerBlock none pre false impl.body le selected.2
  have allocatedTrace := (SnapshotSourceTrace.empty le initState GeneratedBuilderState.initState.dense).newBlock types
    GeneratedBuilderState.initState (show newBlock types le initState = allocated from rfl)
  have allocatedGenerated : GeneratedBuilderState allocated.2 := GeneratedBuilderState.initState.newBlock (env := le) types rfl
  have selectedTrace := allocatedTrace.setCur_full (current := some allocated.1.1) rfl
  have selectedGenerated : GeneratedBuilderState selected.2 := allocatedGenerated.setCur (env := le) _ (by
    intro block same
    cases Option.some.inj same
    simp [allocated, newBlock_run_general]) rfl
  have source : SnapshotTraceRun le none (lowerBlock none pre false impl.body) := body typed none pre false
  have outputTrace := source.continue (dense_lowerBlock none pre false impl.body)
    (advB_lowerBlock none pre false impl.body) (types_lowerBlock none pre false impl.body)
    (generatedTargetFrame_lowerBlock none pre false impl.body) selectedTrace selectedGenerated trivial
    (Nat.zero_le _) (show lowerBlock none pre false impl.body le selected.2 = output from rfl)
  have outputGenerated : GeneratedBuilderState output.2 := selectedGenerated.lowerBlock none pre false impl.body trivial rfl
  have finished := outputTrace.finishFunction outputGenerated impl output.1
  change SnapshotSourceTrace le 0 (Goose.Lower.finishFunction impl output.1 le output.2).2
    (Goose.Lower.finishFunction impl output.1 le output.2).2
  exact finished

theorem lowerGlobal_snapshotSourceTrace {module : Core.Module} {global : Core.Global} {index finish : Nat}
    (typed : Core.tyExpr (initEnv module index) global.init 0 = .ok (global.ty, finish))
    (source : SnapshotSourceExpression (initEnv module index) [global.ty] global.init) :
    SnapshotSourceTrace (lowerEnv module #[] [global.ty]) 0
      (cfg_globalState module global) (cfg_globalState module global) := by
  let le := lowerEnv module #[] [global.ty]
  let allocated := newBlock [] le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let output := lowerExpr global.init le selected.2
  have allocatedTrace := (SnapshotSourceTrace.empty le initState GeneratedBuilderState.initState.dense).newBlock []
    GeneratedBuilderState.initState (show newBlock [] le initState = allocated from rfl)
  have allocatedGenerated : GeneratedBuilderState allocated.2 := GeneratedBuilderState.initState.newBlock (env := le) [] rfl
  have selectedTrace := allocatedTrace.setCur_full (current := some allocated.1.1) rfl
  have selectedGenerated : GeneratedBuilderState selected.2 := allocatedGenerated.setCur (env := le) _ (by
    intro block same
    cases Option.some.inj same
    simp [allocated, newBlock0_run]) rfl
  have expression : SnapshotTraceRun le none (lowerExpr global.init) := source typed
  have outputTrace := expression.continue (dense_lowerExpr global.init)
    (advB_lowerExpr global.init) (types_lowerExpr global.init)
    (generatedTargetFrame_lowerExpr none global.init) selectedTrace selectedGenerated trivial
    (Nat.zero_le _) (show lowerExpr global.init le selected.2 = output from rfl)
  have outputGenerated : GeneratedBuilderState output.2 := selectedGenerated.lowerExpr global.init rfl
  have finished := outputTrace.emitTerm_before_full outputGenerated
    (term := .ret [output.1] (some global.org)) rfl (by
      intro edge member
      simp [Term.permissionEdges] at member)
  change SnapshotSourceTrace le 0 (Goose.Lower.emitTerm (.ret [output.1] (some global.org)) le output.2).2
    (Goose.Lower.emitTerm (.ret [output.1] (some global.org)) le output.2).2
  exact finished

theorem lowerImpl_mutableSnapshotGraphs {module : Core.Module} {impl : Core.Impl}
    (trace : SnapshotSourceTrace (lowerEnv module impl.vars impl.results.toList) 0
      (cfg_implState module impl) (cfg_implState module impl)) :
    MutableSnapshotGraphs (lower module) (lowerImpl module impl) (cfg_implState module impl) := by
  apply trace.mutableSnapshotGraphs rfl (cfg_impl_blocks module impl) ?_ rfl
  simp [lower, lowerEnv, lowerGlobal, Array.map_map]

theorem lowerContext_mutableSnapshotGraphs {module : Core.Module} {context : Context} {impl : Core.Impl}
    (trace : SnapshotSourceTrace (lowerEnv module impl.vars impl.results.toList) 0
      (cfg_implState module impl) (cfg_implState module impl)) :
    MutableSnapshotGraphs (lower module) (lowerContextAt module context impl) (cfg_implState module impl) := by
  apply trace.mutableSnapshotGraphs rfl (cfg_context_blocks module context impl) ?_ rfl
  simp [lower, lowerEnv, lowerGlobal, Array.map_map]

theorem lowerGlobal_mutableSnapshotGraphs {module : Core.Module} {global : Core.Global}
    (trace : SnapshotSourceTrace (lowerEnv module #[] [global.ty]) 0
      (cfg_globalState module global) (cfg_globalState module global)) :
    MutableSnapshotGraphs (lower module) (lowerGlobal module global).init (cfg_globalState module global) := by
  apply trace.mutableSnapshotGraphs rfl (cfg_global_blocks module global) ?_ rfl
  simp [lower, lowerEnv, lowerGlobal, Array.map_map]

end Goose.Lower.Validation
