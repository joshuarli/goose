import Goose.Lower.Validation.SnapshotContentsSourceControlHeaders
import Goose.Lower.Validation.SnapshotContentsSourceLeavesAccess
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem snapshot_source_forEach {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : VarId) (index : Option VarId) (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (viewChild : SnapshotSourceView env results view) (bodyChild : ∀ env, SnapshotSourceBlock env results body) :
    SnapshotSourceStatement env results scope (.forEach slot index view byRef body origin) := by
  intro output start finish source loop before result after generated frames run
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declared, indexChecked, viewSource, binderChecked, bodySource, _⟩ := tyStmt_forEach_children source
  let le := lowerEnv env.mod env.vars results
  let bodyAction := fun ownerView header counter depth target => (do
    let elem ← emitDef (.refElem ownerView counter)
    let value ← eachElemValue slot byRef elem
    let pre := (slot, value, origin) :: (match index with
      | some idx => [(idx, counter, origin)]
      | none => [])
    lowerBlock (some ⟨depth, target, .next header .i64 counter⟩) pre false body : B ValueId)
  have bodyChecked : ∀ ownerView header counter depth target,
      SnapshotSourceAction le (some ⟨depth, target, .next header .i64 counter⟩)
        (bodyAction ownerView header counter depth target) := by
    intro ownerView header counter depth target
    exact (SnapshotSourceAction.emitDef le _ (.refElem ownerView counter) (by intros; intro h; cases h)).bind fun elem =>
      (SnapshotSourceAction.eachElemValue le _ slot byRef elem).bind fun value =>
        SnapshotSourceAction.lowerBlock _ _ false body
          (bodyChild { env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible }
            bodySource _ _ false)
  change (do
    let (owner, vw) ← lowerEachSource view
    let regrow ← regrowOf owner
    let sampled ← eachSampled regrow vw
    let initial ← emitDef (.constInt .i64 0)
    whenLive () fun _ => do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      lowerEach regrow owner sampled header counter (bodyAction vw header counter)) le before = (result, after) at run
  obtain ⟨⟨owner, vw⟩, inputState, inputRun, regrow, regrowState, regrowRun,
    sampled, sampledState, sampledRun, initial, initialState, initialRun, rest⟩ := by
      simpa only [bind_eq] using run
  have inputTrace := snapshot_source_eachSource view viewChild viewSource before (owner, vw) inputState generated trivial inputRun
  have inputGenerated := generated.lowerEachSource view inputRun
  have inputFresh := (advB_lowerEachSource view le before _ inputState inputRun).vals
  let regrowAction := SnapshotSourceAction.regrowOf le none owner
  have regrowTrace := regrowAction.snapshots.continue regrowAction.dense regrowAction.advance regrowAction.types
    regrowAction.frames inputTrace inputGenerated trivial inputFresh regrowRun
  have regrowGenerated := inputGenerated.regrowOf owner regrowRun
  have regrowFresh := Nat.le_trans inputFresh (regrowAction.advance le inputState regrow regrowState regrowRun).vals
  let sampledAction := SnapshotSourceAction.eachSampled le none regrow vw
  have sampledTrace := sampledAction.snapshots.continue sampledAction.dense sampledAction.advance sampledAction.types
    sampledAction.frames regrowTrace regrowGenerated trivial regrowFresh sampledRun
  have sampledGenerated := regrowGenerated.eachSampled regrow vw sampledRun
  have sampledFresh := Nat.le_trans regrowFresh (sampledAction.advance le regrowState sampled sampledState sampledRun).vals
  have initialTrace := sampledTrace.emitDef sampledGenerated initialRun (by intros; intro h; cases h)
  have initialGenerated := sampledGenerated.emitDef (.constInt .i64 0) initialRun
  have initialFresh := Nat.le_trans sampledFresh (advB_emitDef (.constInt .i64 0) le sampledState initial initialState initialRun).vals
  cases live : initialState.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at rest
    obtain ⟨_, rfl⟩ := Prod.mk.inj rest
    exact initialTrace
  | some current =>
    rw [whenLive_some _ _ _ live] at rest
    have checked := snapshot_control_header1 initialTrace initialGenerated initialFresh .i64 initial
      (fun header counter => lowerEach regrow owner sampled header counter (bodyAction vw header counter))
      (fun header counter state trace generated fresh headerAt =>
        (snapshot_lowerEach trace generated fresh regrow owner sampled header counter headerAt
          (bodyAction vw header counter) (bodyChecked vw header counter)).1)
    simpa only [rest] using checked

end Goose.Lower.Validation
