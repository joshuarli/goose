import Goose.Lower.Validation.EmittedMetadataControlEachPrepared
import Goose.Lower.Validation.EmittedMetadataControlIterationBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_source_forEach {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : VarId) (index : Option VarId) (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (viewChild : EmittedMetadataSourceView env results view)
    (bodyChild : ∀ env, EmittedMetadataSourceBlock env results body) :
    EmittedMetadataSourceStatement env results scope (.forEach slot index view byRef body origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run metadata
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declared, indexChecked, viewSource, binderChecked, bodySource, _⟩ := tyStmt_forEach_children source
  have variableRow := (declare_ok _ _ _ _ _ declared).2.1
  have indexRows : ∀ i, index = some i → ∃ indexVar, env.vars[i]? = some indexVar ∧ indexVar.ty = .int .i64 := by
    intro i atIndex
    obtain ⟨_, indexVar, row, _, type⟩ := (declareIndex_ok _ _ _ _ _ indexChecked).2 i atIndex
    exact ⟨indexVar, row, type⟩
  let le := lowerEnv env.mod env.vars results
  let input := lowerEachSource view le before
  let flag := (regrowOf input.1.1 le input.2).1
  let sampled := eachSampled flag input.1.2 le input.2
  let started := emitDef (.constInt .i64 0) le sampled.2
  let bodyAction := fun header counter depth target => (do
    let elem ← emitDef (.refElem input.1.2 counter)
    let value ← eachElemValue slot byRef elem
    let pre := (slot, value, origin) :: (match (generalizing := false) index with
      | some i => [(i, counter, origin)] | none => [])
    lowerBlock (some ⟨depth, target, .next header .i64 counter⟩) pre false body : B ValueId)
  have viewRun := emitted_eachSource_view view le before
  have inputMetadata : EmittedMetadata le input.2 := by
    rw [viewRun.1]
    exact viewChild agreement viewSource before _ _ generated trivial trivial rfl metadata
  have inputGenerated : GeneratedBuilderState input.2 := generated.lowerEachSource view (env := le) rfl
  have regrowRun : regrowOf input.1.1 le input.2 = (flag, input.2) :=
    Prod.ext rfl (emitted_regrowOf_state _ _ _)
  have final : EmittedMetadata le (lowerStmt loop (.forEach slot index view byRef body origin) le before).2 := by
    change EmittedMetadata le ((do
      let regrow ← regrowOf input.1.1
      let count ← eachSampled regrow input.1.2
      let begin ← emitDef (.constInt .i64 0)
      whenLive () fun _ => do
        let (header, params) ← newBlock [.data (.int .i64)]
        let counter := params.headD 0
        emitTerm (.br header [begin])
        setCur (some header)
        lowerEach regrow input.1.1 count header counter (bodyAction header counter)) le input.2).2
    simp only [bind_run, regrowRun]
    change EmittedMetadata le ((whenLive () fun _ => do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [started.1])
      setCur (some header)
      lowerEach flag input.1.1 sampled.1 header counter (bodyAction header counter)) le started.2).2
    cases inputLive : input.2.cur with
    | none =>
      have sampledMetadata := (EmittedMetadataAction.eachSampled le none flag input.1.2).metadata
        input.2 _ _ inputGenerated trivial trivial rfl inputMetadata
      have startedMetadata := sampledMetadata.emitDef (.constInt .i64 0)
      have sampledDead : sampled.2.cur = none := dead_eachSampled flag input.1.2 le input.2 _ _ rfl inputLive
      have startedDead : started.2.cur = none := dead_emitDef (.constInt .i64 0) le sampled.2 _ _ rfl sampledDead
      rw [whenLive_none _ _ _ startedDead]
      exact startedMetadata
    | some current =>
      have viewTyped : ∃ mu, input.2.vals[input.1.2]? = some (some (.view mu element)) ∧
          (writable = true → mu = .mutable) := by
        rw [viewRun.1, viewRun.2]
        exact metadata_each_view_typed view viewSource generated rfl (by rw [← viewRun.1, inputLive]; rfl)
      obtain ⟨mu, viewTyped, viewMutable⟩ := viewTyped
      have prepared := metadata_each_prepared inputMetadata inputGenerated input.1.1 input.1.2 inputLive viewTyped
      have retainedView := (types_emitDef (.constInt .i64 0) le sampled.2 _ _ rfl) _ _
        ((types_eachSampled flag input.1.2 le input.2 _ _ rfl) _ _ viewTyped)
      have checked := metadata_control_eachHeader prepared.1 prepared.2.1 flag input.1.1 sampled.1 started.1
        prepared.2.2.2.1 prepared.2.2.2.2 bodyAction
        (fun header counter depth target state metadata generated counterTyped prefixProof headerBound targetBound active => by
          cases current : state.cur with
          | none => simp [current] at active
          | some block =>
            let op := Op.refElem input.1.2 counter
            let addressed := emitDef op le state
            let evaluated := eachElemValue slot byRef addressed.1 le addressed.2
            let pre := (slot, evaluated.1, origin) :: (match (generalizing := false) index with
              | some i => [(i, counter, origin)] | none => [])
            have viewRow := prefixProof _ _ retainedView
            have operationSuccess : op.resultTy (tyEnv le state) = .ok (.data (.ref mu element)) := by
              simp [op, Op.resultTy, TyEnv.viewTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, viewRow, counterTyped,
                pure, Except.pure, bind, Except.bind]
            have addressedMetadata := metadata.emitDef op
            have addressedGenerated : GeneratedBuilderState addressed.2 := generated.emitDef op (env := le) rfl
            have addressedRecorded := emitDef_recorded current operationSuccess
            have addressedLive : addressed.2.cur = some block := addressedRecorded.2.1.trans current
            have evaluatedMetadata := (EmittedMetadataAction.eachElemValue le none slot byRef addressed.1).metadata
              addressed.2 _ _ addressedGenerated trivial trivial rfl addressedMetadata
            have evaluatedGenerated : GeneratedBuilderState evaluated.2 := addressedGenerated.eachElemValue
              slot byRef addressed.1 (env := le) rfl
            have evaluatedTyped := metadata_each_value_typed binderChecked
              (show le.vars[slot]? = some localVar from variableRow) viewMutable addressedRecorded.2.2.1 addressedLive
            have retainedCounter := (types_eachElemValue slot byRef addressed.1 le addressed.2 _ _ rfl) _ _
              ((types_emitDef op le state _ _ rfl) _ _ counterTyped)
            have grows := Nat.le_trans (advB_emitDef op le state _ _ rfl).ext.1
              (advB_eachElemValue slot byRef addressed.1 le addressed.2 _ _ rfl).ext.1
            have targets : LoopBuilderTargets (some ⟨depth, target, .next header .i64 counter⟩) evaluated.2 :=
              ⟨Nat.lt_of_lt_of_le targetBound grows, Nat.lt_of_lt_of_le headerBound grows⟩
            have preTyped : EmittedPreTyped le evaluated.2 pre :=
              metadata_each_pre_typed variableRow indexRows evaluatedTyped.2 retainedCounter
            have bodyMetadata := bodyChild { env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible }
              agreement bodySource (some ⟨depth, target, .next header .i64 counter⟩) pre false evaluated.2 _ _
              evaluatedGenerated targets retainedCounter preTyped rfl evaluatedMetadata
            have sameState : (bodyAction header counter depth target le state).2 =
                (lowerBlock (some ⟨depth, target, .next header .i64 counter⟩) pre false body le evaluated.2).2 := rfl
            rw [sameState]
            exact ⟨bodyMetadata, evaluatedGenerated.lowerBlock _ pre false body targets (env := le) rfl⟩)
        (fun header counter depth target => AdvB.bind (advB_emitDef _) fun elem =>
          AdvB.bind (advB_eachElemValue slot byRef elem) fun value => advB_lowerBlock _ _ false body)
        (fun header counter depth target => TypeRun.bind (types_emitDef _) fun elem =>
          TypeRun.bind (types_eachElemValue slot byRef elem) fun value => types_lowerBlock _ _ false body)
      rw [whenLive_some _ _ _ prepared.2.2.1]
      exact checked.1
  simpa only [le, run] using final

#print axioms metadata_source_forEach

end Goose.Lower.Validation
