import Goose.Lower.Validation.EmittedTypingBlockSource
import Goose.Lower.Validation.EmittedTypingGeneratedEach
import Goose.Lower.Validation.EmittedTypingSourceOutputs
import Goose.Lower.Validation.OperandEach
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_eachSource_view (view : View) (le : LEnv) (before : LS) :
    (lowerEachSource view le before).2 = (lowerView view le before).2 ∧
    (lowerEachSource view le before).1.2 = (lowerView view le before).1 := by
  cases view <;> exact ⟨rfl, rfl⟩

theorem emitted_regrowOf_state (owner : Option ValueId) (le : LEnv) (before : LS) :
    (regrowOf owner le before).2 = before := by
  cases owner with
  | none => rfl
  | some value =>
    simp only [regrowOf, growOwner, bind_run, valTy_run]
    cases (valTy value le before).1 with
    | view _ _ => rfl
    | data type => cases type <;> rfl

theorem emitted_regrowOf_owner {owner : Option ValueId} {le : LEnv} {before : LS}
    (regrow : (regrowOf owner le before).1 = true) :
    ∃ mu ownerType element, before.vals[owner.getD 0]? = some (some (.data (.ref mu ownerType))) ∧
      GIR.arrayElem? ownerType = some element := by
  cases owner with
  | none => cases regrow
  | some value =>
    simp only [regrowOf, growOwner, bind_run, valTy_run] at regrow
    generalize observed : (valTy value le before).1 = recorded at regrow
    cases recorded with
    | view _ _ => cases regrow
    | data type =>
      cases type with
      | ref mu ownerType =>
        cases ownerType <;> simp only [pure_run, Prod.fst] at regrow
        all_goals first
          | exact ⟨mu, _, _, emitted_valTy_nonunit (by intro equality; cases equality) observed, rfl⟩
          | cases regrow
      | _ => cases regrow

theorem EmittedBuilder.eachElemValue {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (slot : VarId) (byRef : Bool) (element : ValueId)
    (typed : before.cur.isSome = true → ∃ mu type, before.vals[element]? = some (some (.data (.ref mu type)))) :
    EmittedBuilder le initial (Goose.Lower.eachElemValue slot byRef element le before).2 := by
  cases byRef
  · apply builder.emitDef (.load element)
    · intro active
      obtain ⟨mu, type, row⟩ := typed active
      exact ⟨.data type, by
        simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row,
          pure, Except.pure, bind, Except.bind]⟩
    · intro active operand member
      have same : operand = element := by simpa [Op.uses] using member
      subst operand
      obtain ⟨mu, type, row⟩ := typed active
      exact (Array.getElem?_eq_some_iff.mp row).1
  · simp only [Goose.Lower.eachElemValue, reduceIte, bind_run, read_apply]
    cases localRow : le.vars[slot]? with
    | none => exact builder
    | some localVar =>
      cases typeRow : localVar.ty <;> simp only [typeRow]
      all_goals first
        | exact builder
        | exact builder.borrowTo _ element

theorem EmittedBuilder.eachSampled {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (regrow : Bool) (view : ValueId)
    (typed : before.cur.isSome = true → ∃ mu element, before.vals[view]? = some (some (.view mu element))) :
    EmittedBuilder le initial (Goose.Lower.eachSampled regrow view le before).2 := by
  cases regrow
  · apply builder.emitDef (.viewLen view)
    · intro active
      obtain ⟨mu, element, row⟩ := typed active
      exact ⟨.data (.int .i64), by
        simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, tyEnv, row, pure, Except.pure, bind, Except.bind]⟩
    · intro active operand member
      have same : operand = view := by simpa [Op.uses] using member
      subst operand
      obtain ⟨mu, element, row⟩ := typed active
      exact (Array.getElem?_eq_some_iff.mp row).1
  · exact builder

theorem emitted_checked_eachPrepared {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (owner : Option ValueId) (view : ValueId) {mu : Mutability} {element : Ty} {current : BlockId}
    (live : before.cur = some current) (viewTyped : before.vals[view]? = some (some (.view mu element))) :
    let regrow := (regrowOf owner le before).1
    let sampled := eachSampled regrow view le before
    let started := emitDef (.constInt .i64 0) le sampled.2
    EmittedBuilder le initial started.2 ∧ GeneratedBuilderState started.2 ∧ started.2.cur = some current ∧
      started.2.vals[started.1]? = some (some (.data (.int .i64))) ∧
      EmittedEachLengthTypes started.2 regrow owner sampled.1 := by
  have zeroSuccess : (Op.constInt .i64 0).resultTy (tyEnv le before) = .ok (.data (.int .i64)) := by simp [Op.resultTy, show IntTy.i64.inRange 0 = true from by decide, pure, Except.pure]
  cases regrowCase : (regrowOf owner le before).1
  · let sampled := emitDef (.viewLen view) le before
    have sampleSuccess : (Op.viewLen view).resultTy (tyEnv le before) = .ok (.data (.int .i64)) := by
      simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, tyEnv, viewTyped, pure, Except.pure, bind, Except.bind]
    have sampledBuilder := builder.emitDef (.viewLen view) (fun _ => ⟨_, sampleSuccess⟩) (by
      intro active operand member
      have same : operand = view := by simpa [Op.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp viewTyped).1)
    have sampledGenerated : GeneratedBuilderState sampled.2 := generated.emitDef (.viewLen view) rfl
    have sampledRecorded := emitDef_recorded live sampleSuccess
    have sampleLive : sampled.2.cur = some current := sampledRecorded.2.1.trans live
    have startedBuilder := sampledBuilder.emitDef (.constInt .i64 0) (fun _ => ⟨.data (.int .i64), by simp [Op.resultTy, show IntTy.i64.inRange 0 = true from by decide, pure, Except.pure]⟩)
      (by intro active operand member; simp [Op.uses] at member)
    have startedGenerated : GeneratedBuilderState (emitDef (.constInt .i64 0) le sampled.2).2 :=
      sampledGenerated.emitDef (.constInt .i64 0) rfl
    have startedRecorded := emitDef_recorded sampleLive (show (Op.constInt .i64 0).resultTy (tyEnv le sampled.2) = .ok (.data (.int .i64)) from by simp [Op.resultTy, show IntTy.i64.inRange 0 = true from by decide, pure, Except.pure])
    exact ⟨startedBuilder, startedGenerated, startedRecorded.2.1.trans sampleLive, startedRecorded.2.2.1,
      (types_emitDef (.constInt .i64 0) le sampled.2 _ _ rfl) _ _ sampledRecorded.2.2.1⟩
  · have startedBuilder := builder.emitDef (.constInt .i64 0) (fun _ => ⟨_, zeroSuccess⟩)
      (by intro active operand member; simp [Op.uses] at member)
    have startedGenerated : GeneratedBuilderState (emitDef (.constInt .i64 0) le before).2 :=
      generated.emitDef (.constInt .i64 0) rfl
    have startedRecorded := emitDef_recorded live zeroSuccess
    have ownerTyped : EmittedEachLengthTypes before true owner 0 := emitted_regrowOf_owner regrowCase
    exact ⟨startedBuilder, startedGenerated, startedRecorded.2.1.trans live, startedRecorded.2.2.1,
      ownerTyped.retained (types_emitDef (.constInt .i64 0) le before _ _ rfl)⟩

theorem emitted_source_forEach {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : VarId) (index : Option VarId) (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (viewChild : EmittedSourceView env results view) (bodyChild : ∀ env, EmittedSourceBlock env results body) :
    EmittedSourceStatement env results scope (.forEach slot index view byRef body origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declared, indexChecked, viewSource, binderChecked, bodySource, _⟩ := tyStmt_forEach_children source
  let le := lowerEnv env.mod env.vars results
  let input := lowerEachSource view le before
  let flag := (regrowOf input.1.1 le input.2).1
  let sampled := eachSampled flag input.1.2 le input.2
  let started := emitDef (.constInt .i64 0) le sampled.2
  let bodyAction := fun header counter depth target => (do
    let elem ← emitDef (.refElem input.1.2 counter)
    let value ← eachElemValue slot byRef elem
    let pre := (slot, value, origin) :: (match index with | some i => [(i, counter, origin)] | none => [])
    lowerBlock (some ⟨depth, target, .next header .i64 counter⟩) pre false body : B ValueId)
  have viewRun := emitted_eachSource_view view le before
  have inputBuilder : EmittedBuilder le initial input.2 := by
    rw [viewRun.1]
    exact viewChild viewSource generated builder
  have inputGenerated : GeneratedBuilderState input.2 := generated.lowerEachSource view rfl
  have regrowRun : regrowOf input.1.1 le input.2 = (flag, input.2) :=
    Prod.ext rfl (emitted_regrowOf_state _ _ _)
  change EmittedBuilder le initial ((do
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
  change EmittedBuilder le initial ((whenLive () fun _ => do
    let (header, params) ← newBlock [.data (.int .i64)]
    let counter := params.headD 0
    emitTerm (.br header [started.1])
    setCur (some header)
    lowerEach flag input.1.1 sampled.1 header counter (bodyAction header counter)) le started.2).2
  cases inputLive : input.2.cur with
  | none =>
    have sampledBuilder := inputBuilder.eachSampled flag input.1.2 (by intro live; simp [inputLive] at live)
    have startedBuilder := sampledBuilder.emitDef (.constInt .i64 0)
      (fun _ => ⟨.data (.int .i64), by simp [Op.resultTy, show IntTy.i64.inRange 0 = true from by decide, pure, Except.pure]⟩)
      (by intro live operand member; simp [Op.uses] at member)
    have sampledDead : sampled.2.cur = none := dead_eachSampled flag input.1.2 le input.2 _ _ rfl inputLive
    have startedDead : started.2.cur = none := dead_emitDef (.constInt .i64 0) le sampled.2 _ _ rfl sampledDead
    rw [whenLive_none _ _ _ startedDead]
    exact startedBuilder
  | some current =>
    have viewTyped : ∃ mu, input.2.vals[input.1.2]? = some (some (.view mu element)) := by
      rw [viewRun.1, viewRun.2]
      exact lowerView_generated_typed view viewSource rfl (by rw [← viewRun.1, inputLive]; rfl) generated
    obtain ⟨mu, viewTyped⟩ := viewTyped
    have prepared := emitted_checked_eachPrepared inputBuilder inputGenerated input.1.1 input.1.2 inputLive viewTyped
    have retainedView := (types_emitDef (.constInt .i64 0) le sampled.2 _ _ rfl) _ _
      ((types_eachSampled flag input.1.2 le input.2 _ _ rfl) _ _ viewTyped)
    have checked := emitted_checked_generated_eachHeader prepared.1 prepared.2.1 flag input.1.1 sampled.1 started.1
      prepared.2.2.2.1 prepared.2.2.2.2 bodyAction
      (fun header counter depth target initial state builder generated counterTyped prefixProof headerBound targetBound => by
        let op := Op.refElem input.1.2 counter
        let addressed := emitDef op le state
        let evaluated := eachElemValue slot byRef addressed.1 le addressed.2
        let pre := (slot, evaluated.1, origin) :: (match index with | some i => [(i, counter, origin)] | none => [])
        have viewRow := prefixProof _ _ retainedView
        have operationSuccess : op.resultTy (tyEnv le state) = .ok (.data (.ref mu element)) := by
          simp [op, Op.resultTy, TyEnv.viewTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, viewRow, counterTyped,
            pure, Except.pure, bind, Except.bind]
        have addressedBuilder := builder.emitDef op (fun _ => ⟨_, operationSuccess⟩) (by
          intro live operand member
          have either : operand = input.1.2 ∨ operand = counter := by simpa [op, Op.uses] using member
          rcases either with rfl | rfl
          · exact (Array.getElem?_eq_some_iff.mp viewRow).1
          · exact (Array.getElem?_eq_some_iff.mp counterTyped).1)
        have evaluatedBuilder := addressedBuilder.eachElemValue slot byRef addressed.1 (by
          intro live
          have initialLive := (dead_emitDef op).live_before rfl live
          cases current : state.cur with
          | none => simp [current] at initialLive
          | some block => exact ⟨mu, element, (emitDef_recorded current operationSuccess).2.2.1⟩)
        have addressedGenerated : GeneratedBuilderState addressed.2 := generated.emitDef op rfl
        have evaluatedGenerated : GeneratedBuilderState evaluated.2 := addressedGenerated.eachElemValue slot byRef addressed.1 rfl
        have nonempty : 0 < state.vals.size := Nat.lt_of_le_of_lt (Nat.zero_le counter) (Array.getElem?_eq_some_iff.mp counterTyped).1
        have elementBound : addressed.1 < addressed.2.vals.size := value_emitDef_of_nonempty rfl nonempty
        have valueBound : evaluated.1 < evaluated.2.vals.size := value_eachElemValue_of_bounded rfl elementBound
        have retainedCounter := (types_eachElemValue slot byRef addressed.1 le addressed.2 _ _ rfl) _ _
          ((types_emitDef op le state _ _ rfl) _ _ counterTyped)
        have grows := Nat.le_trans (advB_emitDef op le state _ _ rfl).ext.1
          (advB_eachElemValue slot byRef addressed.1 le addressed.2 _ _ rfl).ext.1
        have targets : LoopBuilderTargets (some ⟨depth, target, .next header .i64 counter⟩) evaluated.2 :=
          ⟨Nat.lt_of_lt_of_le targetBound grows, Nat.lt_of_lt_of_le headerBound grows⟩
        have preBounds : ∀ x value org, (x, value, org) ∈ pre → value < evaluated.2.vals.size := by
          intro x value org member
          have either : value = evaluated.1 ∨ value = counter := by
            cases index with
            | none =>
              simp only [pre, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
              exact Or.inl member.2.1
            | some idx =>
              simp only [pre, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
              exact member.elim (fun h => Or.inl h.2.1) (fun h => Or.inr h.2.1)
          rcases either with rfl | rfl
          · exact valueBound
          · exact (Array.getElem?_eq_some_iff.mp retainedCounter).1
        have bodyBuilder := bodyChild { env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible }
          bodySource (some ⟨depth, target, .next header .i64 counter⟩) pre false evaluatedGenerated evaluatedBuilder
          retainedCounter targets preBounds
        have sameState : (bodyAction header counter depth target le state).2 =
            (lowerBlock (some ⟨depth, target, .next header .i64 counter⟩) pre false body le evaluated.2).2 := by
          cases index <;> rfl
        rw [sameState]
        exact ⟨bodyBuilder, evaluatedGenerated.lowerBlock _ pre false body targets rfl⟩)
      (fun header counter depth target => AdvB.bind (advB_emitDef _) fun elem =>
        AdvB.bind (advB_eachElemValue slot byRef elem) fun value => advB_lowerBlock _ _ false body)
      (fun header counter depth target => TypeRun.bind (types_emitDef _) fun elem =>
        TypeRun.bind (types_eachElemValue slot byRef elem) fun value => types_lowerBlock _ _ false body)
    rw [whenLive_some _ _ _ prepared.2.2.1]
    exact checked.1

end Goose.Lower.Validation
