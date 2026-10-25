import Goose.Lower.Validation.StorageSourceEachFrame
import Goose.Lower.Validation.StorageSourceEachValue
import Goose.Lower.Validation.OperandEach
import Goose.Lower.Validation.SourceStatementTypingControl
import Goose.Lower.Validation.SourceReadable

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

attribute [local irreducible] StorageAt

theorem storage_forEach_source {env output : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) (sourceTypes : SourceReadableEnvironment env)
    {slot : VarId} {index : Option VarId} {view : View} {byReference : Bool}
    {body : Core.Block} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.forEach slot index view byReference body origin) start = .ok (output, finish))
    (viewChild : StorageViewChild env results view)
    (bodyChild : ∀ {type : Ty} {first last : Nat},
      Core.tyBlock { env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible }
        [] body first = .ok (type, last) →
      ∀ (loop : Option LoopCtx) (pre : List (VarId × ValueId × OriginId)) {state : LS},
        GeneratedBuilderState state → LoopBuilderTargets loop state →
        StorageAt (lowerEnv env.mod env.vars results) state (lowerBlock loop pre false body))
    {before : LS} (generated : GeneratedBuilderState before) (loop : Option LoopCtx) :
    StorageAt (lowerEnv env.mod env.vars results) before
      (lowerStmt loop (.forEach slot index view byReference body origin)) := by
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    _, _, viewSource, _, bodySource, _⟩ := tyStmt_forEach_children source
  have flat := source_view_element_flat view sourceTypes viewSource
  let le := lowerEnv env.mod env.vars results
  let sourced := lowerEachSource view le before
  let regrown := regrowOf sourced.1.1 le sourced.2
  let sampled := eachSampled regrown.1 sourced.1.2 le regrown.2
  let started := emitDef (.constInt .i64 0) le sampled.2
  have sourcedStorage : StorageAt le before (lowerEachSource view) := by
    unfold StorageAt
    intro checked
    have viewed := viewChild viewSource generated
    unfold StorageAt at viewed
    have viewed := viewed checked
    cases view <;> exact viewed
  have sourcedGenerated : GeneratedBuilderState sourced.2 := generated.lowerEachSource view
    (show lowerEachSource view le before = sourced from rfl)
  have regrownGenerated : GeneratedBuilderState regrown.2 := sourcedGenerated.regrowOf sourced.1.1
    (show regrowOf sourced.1.1 le sourced.2 = regrown from rfl)
  have sampledGenerated : GeneratedBuilderState sampled.2 := regrownGenerated.eachSampled regrown.1 sourced.1.2
    (show eachSampled regrown.1 sourced.1.2 le regrown.2 = sampled from rfl)
  have startedGenerated : GeneratedBuilderState started.2 := sampledGenerated.emitDef (.constInt .i64 0)
    (show emitDef _ le sampled.2 = started from rfl)
  apply sourcedStorage.bind
  apply (StorageAt.regrowOf _ _ _).bind
  apply (StorageAt.eachSampled _ _ _ _).bind
  apply (StorageAt.emitDef _ (by intros; trivial)).bind
  apply StorageAt.whenLive
  intro block live
  have startedLive : started.2.cur.isSome = true := congrArg Option.isSome live
  have sampledLive : sampled.2.cur.isSome = true :=
    (dead_emitDef (.constInt .i64 0)).live_before (le := le) (before := sampled.2) rfl startedLive
  have regrownLive : regrown.2.cur.isSome = true := (dead_eachSampled regrown.1 sourced.1.2).live_before rfl sampledLive
  have sourcedLive : sourced.2.cur.isSome = true := (dead_regrowOf sourced.1.1).live_before rfl regrownLive
  have viewRow : ∃ mu, sourced.2.vals[sourced.1.2]? = some (some (.view mu element)) := by
    have typed := outputs.view view viewSource generated rfl
    cases view <;> exact typed sourcedLive
  obtain ⟨mu, sourceRow⟩ := viewRow
  have startTypes : TypePrefix sourced.2 started.2 :=
    (types_regrowOf sourced.1.1 le sourced.2 regrown.1 regrown.2 rfl).trans
      ((types_eachSampled regrown.1 sourced.1.2 le regrown.2 sampled.1 sampled.2 rfl).trans
        (types_emitDef (.constInt .i64 0) le sampled.2 started.1 started.2 rfl))
  have startedRow := startTypes _ _ sourceRow
  refine StorageAt.header1_withTypes (α := Unit) (le := le) (before := started.2)
    (tail := fun header counter => lowerEach regrown.1 sourced.1.1 sampled.1 header counter (fun depth exit => do
      let reference ← emitDef (.refElem sourced.1.2 counter)
      let value ← eachElemValue slot byReference reference
      let pre := (slot, value, origin) :: (match (generalizing := false) index with
        | some slot => [(slot, counter, origin)] | none => [])
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body))
    (.data (.int .i64)) [started.1] startedGenerated ?_
  intro header counter state current headerBound headerTypes counterRow
  have currentRow := headerTypes _ _ startedRow
  refine StorageAt.lowerEach_withTypes regrown.1 sourced.1.1 sampled.1 header counter current ?_
  intro depth exit bodyState bodyGenerated exitBound grows bodyTypes
  let reference := emitDef (.refElem sourced.1.2 counter) le bodyState
  let value := eachElemValue slot byReference reference.1 le reference.2
  have bodyViewRow := bodyTypes _ _ currentRow
  have bodyCounterRow := bodyTypes _ _ counterRow
  have referenceOperation : (Op.refElem sourced.1.2 counter).resultTy (tyEnv le bodyState) =
      .ok (.data (.ref mu element)) := by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      bodyViewRow, bodyCounterRow, pure, Except.pure, bind, Except.bind]
  have referenceGenerated := bodyGenerated.emitDef (.refElem sourced.1.2 counter)
    (show emitDef _ le bodyState = reference from rfl)
  have valueGenerated := referenceGenerated.eachElemValue slot byReference reference.1
    (show eachElemValue slot byReference reference.1 le reference.2 = value from rfl)
  let measured := eachLen regrown.1 sourced.1.1 sampled.1 le state
  let compared := emitDef (.cmp .lt .i64 counter measured.1) le measured.2
  have measuredDense := dense_eachLen regrown.1 sourced.1.1 sampled.1 le state measured.1 measured.2 rfl current.dense current.live
  have comparedDense := dense_emitDef (.cmp .lt .i64 counter measured.1) le measured.2 compared.1 compared.2 rfl measuredDense.1 measuredDense.2.1
  have headerAtBody := Nat.lt_of_lt_of_le headerBound (Nat.le_trans measuredDense.2.2 (Nat.le_trans comparedDense.2.2 grows))
  have referenceDense := dense_emitDef (.refElem sourced.1.2 counter) le bodyState reference.1 reference.2 rfl bodyGenerated.dense bodyGenerated.live
  have valueDense := dense_eachElemValue slot byReference reference.1 le reference.2 value.1 value.2 rfl referenceDense.1 referenceDense.2.1
  have valueBounds : LoopBuilderTargets (some ⟨depth, exit, .next header .i64 counter⟩) value.2 :=
    (show LoopBuilderTargets (some ⟨depth, exit, .next header .i64 counter⟩) bodyState from ⟨exitBound, headerAtBody⟩).mono
      (Nat.le_trans referenceDense.2.2 valueDense.2.2)
  apply (StorageAt.emitDef _ (by intros; trivial)).bind
  apply StorageAt.bind
  · apply StorageAt.eachElemValue
    intro active result
    have earlierLive : bodyState.cur.isSome = true := (dead_emitDef (.refElem sourced.1.2 counter)).live_before rfl active
    cases atBody : bodyState.cur with
    | none => simp [atBody] at earlierLive
    | some currentBlock =>
      have recorded := emitDef_recorded atBody referenceOperation
      exact ⟨mu, element, recorded.2.2.1, Or.inl (by simpa only [Ty.readable] using flat_or_slice_readable (Or.inl flat))⟩
  · exact bodyChild bodySource (some ⟨depth, exit, .next header .i64 counter⟩)
      ((slot, value.1, origin) :: (match (generalizing := false) index with | some slot => [(slot, counter, origin)] | none => []))
      valueGenerated valueBounds

end Goose.Lower.Validation
