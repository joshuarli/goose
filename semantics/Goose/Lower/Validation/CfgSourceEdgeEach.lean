import Goose.Lower.Validation.CfgSourceEdgeContracts
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_each {env : Core.TEnv} {results : List Ty} (x : VarId) (index : Option VarId)
    (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (viewChild : CfgSourceEachSource env results view)
    (bodyChild : CfgSourceBlock { env with loops := env.loops + 1, visible := x :: index.toList ++ env.visible } results body) :
    CfgSourceStatement env results (.forEach x index view byRef body origin) := by
  cases index with
  | none =>
    intro output scope start finish source context
    obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyTy, _, _, viewSource, _, bodySource, _⟩ :=
      tyStmt_forEach_children source
    intro before result after run generated loop checked
    simp only [lowerStmt, bind_eq] at run
    obtain ⟨⟨owner, value⟩, viewed, viewRun, regrow, regrown, regrowRun, sampled, sampledEnd, sampleRun,
      initial, initialized, initializeRun, tail⟩ := run
    obtain ⟨viewGenerated, viewExtension, viewChecked⟩ :=
      (viewChild viewSource).withLoop context before _ viewed viewRun generated loop checked
    obtain ⟨regrowGenerated, regrowExtension, regrowChecked⟩ :=
      generated_edge_regrowOf _ context owner viewed regrow regrown regrowRun viewGenerated (loop.extend viewExtension) viewChecked
    have throughRegrow := viewExtension.trans regrowExtension
    obtain ⟨sampleGenerated, sampleExtension, sampleChecked⟩ :=
      generated_edge_eachSampled _ context regrow value regrown sampled sampledEnd sampleRun regrowGenerated
        (loop.extend throughRegrow) regrowChecked
    have throughSample := throughRegrow.trans sampleExtension
    obtain ⟨initializedGenerated, initializeExtension, initializedChecked⟩ :=
      generated_edge_emitDef _ context (.constInt .i64 0) sampledEnd initial initialized initializeRun sampleGenerated
        (loop.extend throughSample) sampleChecked
    have throughInitialization := throughSample.trans initializeExtension
    cases current : initialized.cur with
    | none =>
      rw [whenLive_none _ _ _ current] at tail
      obtain ⟨_, rfl⟩ := Prod.mk.inj tail
      exact ⟨initializedGenerated, throughInitialization, initializedChecked⟩
    | some block =>
      have initialTyped : initialized.vals[initial]? = some (some (.data (.int .i64))) := by
        cases previous : sampledEnd.cur with
        | none =>
          rw [emitDef_none _ _ previous] at initializeRun
          obtain ⟨_, rfl⟩ := Prod.mk.inj initializeRun
          simp [previous] at current
        | some previousBlock =>
          exact edge_emitDef_recorded previous (by rfl) initializeRun
      rw [whenLive_some _ _ _ current] at tail
      let eachBody (header : BlockId) (counter : ValueId) (depth : Nat) (exit : BlockId) : B ValueId := do
        let elem ← emitDef (.refElem value counter)
        let localValue ← eachElemValue x byRef elem
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, localValue, origin) :: []) false body
      have eachBodyEdges : ∀ header counter depth exit,
          GeneratedEdgeRun (lowerEnv env.mod env.vars results) (some ⟨depth, exit, .next header .i64 counter⟩)
            (eachBody header counter depth exit) := by
        intro header counter depth exit
        exact (generated_edge_emitDef _ _ (.refElem value counter)).bind fun elem =>
          (generated_edge_eachElemValue _ _ x byRef elem).bind fun localValue =>
            bodyChild bodySource (some ⟨depth, exit, .next header .i64 counter⟩)
              ((x, localValue, origin) :: []) false
      obtain ⟨afterGenerated, finalExtension, afterChecked⟩ := generated_edge_counterHeader_at _ context .i64 initial
        (body := fun header counter => lowerEach regrow owner sampled header counter (eachBody header counter))
        (fun header counter before result after lowered generated loop checked current frame typed =>
          generated_edge_lowerEach_at _ context regrow owner sampled header counter
            (body := eachBody header counter) (eachBodyEdges header counter)
            before after result lowered generated loop checked current frame typed)
        initialized after result tail initializedGenerated (loop.extend throughInitialization) initializedChecked initialTyped
      exact ⟨afterGenerated, throughInitialization.trans finalExtension, afterChecked⟩
  | some index =>
    intro output scope start finish source context
    obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyTy, _, _, viewSource, _, bodySource, _⟩ :=
      tyStmt_forEach_children source
    intro before result after run generated loop checked
    simp only [lowerStmt, bind_eq] at run
    obtain ⟨⟨owner, value⟩, viewed, viewRun, regrow, regrown, regrowRun, sampled, sampledEnd, sampleRun,
      initial, initialized, initializeRun, tail⟩ := run
    obtain ⟨viewGenerated, viewExtension, viewChecked⟩ :=
      (viewChild viewSource).withLoop context before _ viewed viewRun generated loop checked
    obtain ⟨regrowGenerated, regrowExtension, regrowChecked⟩ :=
      generated_edge_regrowOf _ context owner viewed regrow regrown regrowRun viewGenerated (loop.extend viewExtension) viewChecked
    have throughRegrow := viewExtension.trans regrowExtension
    obtain ⟨sampleGenerated, sampleExtension, sampleChecked⟩ :=
      generated_edge_eachSampled _ context regrow value regrown sampled sampledEnd sampleRun regrowGenerated
        (loop.extend throughRegrow) regrowChecked
    have throughSample := throughRegrow.trans sampleExtension
    obtain ⟨initializedGenerated, initializeExtension, initializedChecked⟩ :=
      generated_edge_emitDef _ context (.constInt .i64 0) sampledEnd initial initialized initializeRun sampleGenerated
        (loop.extend throughSample) sampleChecked
    have throughInitialization := throughSample.trans initializeExtension
    cases current : initialized.cur with
    | none =>
      rw [whenLive_none _ _ _ current] at tail
      obtain ⟨_, rfl⟩ := Prod.mk.inj tail
      exact ⟨initializedGenerated, throughInitialization, initializedChecked⟩
    | some block =>
      have initialTyped : initialized.vals[initial]? = some (some (.data (.int .i64))) := by
        cases previous : sampledEnd.cur with
        | none =>
          rw [emitDef_none _ _ previous] at initializeRun
          obtain ⟨_, rfl⟩ := Prod.mk.inj initializeRun
          simp [previous] at current
        | some previousBlock =>
          exact edge_emitDef_recorded previous (by rfl) initializeRun
      rw [whenLive_some _ _ _ current] at tail
      let eachBody (header : BlockId) (counter : ValueId) (depth : Nat) (exit : BlockId) : B ValueId := do
        let elem ← emitDef (.refElem value counter)
        let localValue ← eachElemValue x byRef elem
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, localValue, origin) :: [(index, counter, origin)]) false body
      have eachBodyEdges : ∀ header counter depth exit,
          GeneratedEdgeRun (lowerEnv env.mod env.vars results) (some ⟨depth, exit, .next header .i64 counter⟩)
            (eachBody header counter depth exit) := by
        intro header counter depth exit
        exact (generated_edge_emitDef _ _ (.refElem value counter)).bind fun elem =>
          (generated_edge_eachElemValue _ _ x byRef elem).bind fun localValue =>
            bodyChild bodySource (some ⟨depth, exit, .next header .i64 counter⟩)
              ((x, localValue, origin) :: [(index, counter, origin)]) false
      obtain ⟨afterGenerated, finalExtension, afterChecked⟩ := generated_edge_counterHeader_at _ context .i64 initial
        (body := fun header counter => lowerEach regrow owner sampled header counter (eachBody header counter))
        (fun header counter before result after lowered generated loop checked current frame typed =>
          generated_edge_lowerEach_at _ context regrow owner sampled header counter
            (body := eachBody header counter) (eachBodyEdges header counter)
            before after result lowered generated loop checked current frame typed)
        initialized after result tail initializedGenerated (loop.extend throughInitialization) initializedChecked initialTyped
      exact ⟨afterGenerated, throughInitialization.trans finalExtension, afterChecked⟩

end Goose.Lower.Validation
