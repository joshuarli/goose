import Goose.Lower.Validation.PermissionInstructionControlEach
import Goose.Lower.Validation.PermissionInstructionControlRangeHeader

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private def eachStatementBody (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (view header counter : ValueId) (depth exit : Nat) : B ValueId := do
  let element ← emitDef (.refElem view counter)
  let value ← eachElemValue slot byRef element
  lowerBlock (some ⟨depth,exit,.next header .i64 counter⟩)
    ((slot,value,origin) :: (match index with | some id => [(id,counter,origin)] | none => [])) false body

private theorem eachStatementBody_dense (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (view header counter : ValueId) (depth exit : Nat) :
    DenseRun (eachStatementBody slot index byRef origin body view header counter depth exit) := by
  unfold eachStatementBody
  exact DenseRun.bind (dense_emitDef _) fun element => DenseRun.bind (dense_eachElemValue slot byRef element)
    fun value => dense_lowerBlock _ _ false body

private theorem eachStatementBody_advance (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (view header counter : ValueId) (depth exit : Nat) :
    AdvB (eachStatementBody slot index byRef origin body view header counter depth exit) := by
  unfold eachStatementBody
  exact AdvB.bind (advB_emitDef _) fun element => AdvB.bind (advB_eachElemValue slot byRef element)
    fun value => advB_lowerBlock _ _ false body

private theorem eachStatementBody_types (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (view header counter : ValueId) (depth exit : Nat) :
    TypeRun (eachStatementBody slot index byRef origin body view header counter depth exit) := by
  unfold eachStatementBody
  exact TypeRun.bind (types_emitDef _) fun element => TypeRun.bind (types_eachElemValue slot byRef element)
    fun value => types_lowerBlock _ _ false body

private theorem eachStatementBody_frames (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (view header counter : ValueId) (depth exit : Nat) :
    GeneratedTargetFrameRun (some ⟨depth,exit,.next header .i64 counter⟩)
      (eachStatementBody slot index byRef origin body view header counter depth exit) := by
  unfold eachStatementBody
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef _ _) fun element =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_eachElemValue _ slot byRef element)
      fun value => generatedTargetFrame_lowerBlock _ _ false body

private def eachStatementTail (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (owner : Option ValueId)
    (view : ValueId) (regrow : Bool) (sampled start : ValueId) : B Unit :=
  whenLive () fun _ => do
    let (header,ids) ← newBlock [.data (.int .i64)]
    let counter := ids.headD 0
    emitTerm (.br header [start])
    setCur (some header)
    lowerEach regrow owner sampled header counter (eachStatementBody slot index byRef origin body view header counter)

private theorem eachStatementTail_dense (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (owner : Option ValueId)
    (view : ValueId) (regrow : Bool) (sampled start : ValueId) :
    DenseRun (eachStatementTail slot index byRef origin body owner view regrow sampled start) := by
  unfold eachStatementTail
  refine dense_whenLive _ fun _ => ?_
  exact dense_header1 (.data (.int .i64)) start
    (tail := fun header counter => lowerEach regrow owner sampled header counter
      (eachStatementBody slot index byRef origin body view header counter))
    (fun header counter => dense_lowerEach _ _ _ _ _ (eachStatementBody_dense slot index byRef origin body view header counter))

private theorem eachStatementTail_advance (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (owner : Option ValueId)
    (view : ValueId) (regrow : Bool) (sampled start : ValueId) :
    AdvB (eachStatementTail slot index byRef origin body owner view regrow sampled start) := by
  unfold eachStatementTail
  refine advB_whenLive _ fun _ => ?_
  exact advB_header1 (.data (.int .i64)) start
    (tail := fun header counter => lowerEach regrow owner sampled header counter
      (eachStatementBody slot index byRef origin body view header counter))
    (fun header counter => advB_lowerEach _ _ _ _ _ (eachStatementBody_advance slot index byRef origin body view header counter))

private theorem eachStatementTail_types (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (owner : Option ValueId)
    (view : ValueId) (regrow : Bool) (sampled start : ValueId) :
    TypeRun (eachStatementTail slot index byRef origin body owner view regrow sampled start) := by
  unfold eachStatementTail
  refine types_whenLive _ fun _ => ?_
  exact types_header1 (.data (.int .i64)) start
    (tail := fun header counter => lowerEach regrow owner sampled header counter
      (eachStatementBody slot index byRef origin body view header counter))
    (fun header counter => types_lowerEach _ _ _ _ _ (eachStatementBody_types slot index byRef origin body view header counter))

private theorem eachStatementTail_frames (slot : VarId) (index : Option VarId) (byRef : Bool)
    (origin : OriginId) (body : Core.Block) (owner : Option ValueId)
    (view : ValueId) (regrow : Bool) (sampled start : ValueId) :
    GeneratedTargetFrameRun none (eachStatementTail slot index byRef origin body owner view regrow sampled start) := by
  unfold eachStatementTail
  refine generatedTargetFrame_whenLive none _ fun _ => ?_
  exact generatedTargetFrame_header1 none .i64 start
    (tail := fun header counter => lowerEach regrow owner sampled header counter
      (eachStatementBody slot index byRef origin body view header counter)) (by
        intro header counter base env current after result baseCurrent frames terms fresh headerAt run
        exact generatedTargetFrame_lowerEachFresh none regrow owner sampled header counter
          (eachStatementBody_frames slot index byRef origin body view header counter)
          baseCurrent frames terms fresh headerAt run)

private theorem regrowOf_state {le : LEnv} {owner : Option ValueId} {before after : LS} {result : Bool}
    (run : regrowOf owner le before = (result,after)) : after = before := by
  have stable : (regrowOf owner le before).2 = before := by
    cases owner with
    | none => rfl
    | some value =>
      simp only [regrowOf,growOwner,bind_run,valTy_run]
      cases (valTy value le before).1 with
      | data type => cases type <;> rfl
      | view => rfl
  rw [run] at stable
  exact stable

private theorem emitDef_current {le : LEnv} {op : Op} {before after : LS} {value : ValueId}
    (run : emitDef op le before = (value,after)) : after.cur = before.cur := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ le current] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact current
  | some block =>
    rw [emitDef_run _ le current] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact current

private theorem eachSampled_current {le : LEnv} {regrow : Bool} {view : ValueId}
    {before after : LS} {value : ValueId} (run : eachSampled regrow view le before = (value,after)) :
    after.cur = before.cur := by
  cases regrow with
  | true =>
    simp only [eachSampled,ite_true,pure_run] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    rfl
  | false =>
    simp only [eachSampled,Bool.false_eq_true,ite_false] at run
    exact emitDef_current run

theorem forEach_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat} {before after : LS} {result : Unit}
    {loop : Option LoopCtx} {slot : VarId} {index : Option VarId} {source : View}
    {byRef : Bool} {body : Core.Block} {origin : OriginId}
    (generated : GeneratedBuilderState before) (lower : first ≤ before.vals.size)
    (sourceNew : ∀ owner view sourceState, lowerEachSource source le before = ((owner,view),sourceState) →
      NewPermissionInstructions module func le first before sourceState)
    (bodyNew : ∀ (owner : Option ValueId) (view : ValueId) (sourceState : LS), lowerEachSource source le before = ((owner,view),sourceState) →
      sourceState.cur ≠ none → ∀ (header counter : ValueId) (depth exit : Nat) (input : LS) (value : ValueId) (output : LS),
      GeneratedBuilderState input → input.cur.isSome = true →
      LoopBuilderFrames (some ⟨depth,exit,.next header .i64 counter⟩) input →
      first ≤ input.vals.size → sourceState.Ext input → sourceState.vals.size ≤ input.vals.size →
      TypePrefix sourceState input → TermEdgesFramed none sourceState input →
      (do
        let element ← emitDef (.refElem view counter)
        let value ← eachElemValue slot byRef element
        lowerBlock (some ⟨depth,exit,.next header .i64 counter⟩)
          ((slot,value,origin) :: (match index with | some id => [(id,counter,origin)] | none => [])) false body)
          le input = (value,output) → NewPermissionInstructions module func le first input output)
    (run : lowerStmt loop (.forEach slot index source byRef body origin) le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerStmt,bind_eq] at run
  obtain ⟨⟨owner,view⟩,sourceState,sourceRun,regrow,prepared,regrowRun,sampled,sampledState,sampleRun,
    start,started,startRun,tailRun⟩ := run
  have preparedSame := regrowOf_state regrowRun
  subst prepared
  have sourceGenerated := generated.lowerEachSource source sourceRun
  have sampledGenerated := sourceGenerated.eachSampled regrow view sampleRun
  have startedGenerated := sampledGenerated.emitDef _ startRun
  have sourceLower := Nat.le_trans lower (advB_lowerEachSource source le before (owner,view) sourceState sourceRun).vals
  have sampleAdvance := advB_eachSampled regrow view le sourceState sampled sampledState sampleRun
  have startAdvance := advB_emitDef (.constInt .i64 0) le sampledState start started startRun
  have startedGrowth := Nat.le_trans sampleAdvance.vals startAdvance.vals
  have startedLower := Nat.le_trans sourceLower startedGrowth
  have prefixExt := sampleAdvance.ext.trans startAdvance.ext
  have prefixTypes := (types_eachSampled regrow view le sourceState sampled sampledState sampleRun).trans
    (types_emitDef _ le sampledState start started startRun)
  have sampleFrames := generatedTargetFrame_eachSampled none regrow view sourceState le sourceState sampled sampledState
    (.refl _) trivial (.refl _ _) sampleRun
  have prefixFrames := generatedTargetFrame_emitDef none (.constInt .i64 0)
    sourceState le sampledState start started sampleAdvance.ext trivial sampleFrames.1 startRun
  have sampledNew := (sourceNew owner view sourceState sourceRun).compose_framed
    (NewPermissionInstructions.eachSampled sampleRun) sampleRun (dense_eachSampled regrow view)
    (advB_eachSampled regrow view) (types_eachSampled regrow view)
    (generatedTargetFrame_eachSampled none regrow view) sourceGenerated trivial
  have startedNew := sampledNew.compose_framed (NewPermissionInstructions.counting startRun trivial)
    startRun (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    sampledGenerated trivial
  have tailRules : NewPermissionInstructions module func le first started after := by
    cases current : started.cur with
    | none =>
      rw [whenLive_none _ _ le current] at tailRun
      obtain ⟨_,rfl⟩ := Prod.mk.inj tailRun
      exact .of_blocks_eq rfl
    | some currentBlock =>
      have sourceLive : sourceState.cur ≠ none := by
        intro dead
        have same := (emitDef_current startRun).trans (eachSampled_current sampleRun)
        rw [dead,current] at same
        cases same
      rw [whenLive_some _ _ le current] at tailRun
      have actualHeader : (do
          let (header,ids) ← newBlock [.data (.int .i64)]
          let counter := ids.headD 0
          emitTerm (.br header [start])
          setCur (some header)
          lowerEach regrow owner sampled header counter (eachStatementBody slot index byRef origin body view header counter))
          le started = (result,after) := by
        have pairAction (action : B (BlockId × List ValueId)) (tail : BlockId → List ValueId → B Unit) :
            (do let (header,ids) ← action; tail header ids) = action >>= fun pair => tail pair.1 pair.2 := by
          congr 1
        exact (congrArg (fun action : B Unit => action le started)
          (pairAction (newBlock [.data (.int .i64)]) (fun header ids => do
            let counter := ids.headD 0
            emitTerm (.br header [start])
            setCur (some header)
            lowerEach regrow owner sampled header counter (eachStatementBody slot index byRef origin body view header counter)))).trans tailRun
      apply header1_newPermissionInstructions (hint := .i64) (initial := start)
        (tail := fun header counter => lowerEach regrow owner sampled header counter
          (eachStatementBody slot index byRef origin body view header counter))
        startedGenerated startedLower ?_ actualHeader
      intro header counter input output inputGenerated inputLower headerAt headerExt headerGrowth headerTypes headerFrames eachRun
      apply (lowerEach_counted_newPermissionInstructions inputGenerated inputLower headerAt
        (eachStatementBody_dense slot index byRef origin body view header counter)
        (eachStatementBody_advance slot index byRef origin body view header counter)
        (eachStatementBody_types slot index byRef origin body view header counter)
        (eachStatementBody_frames slot index byRef origin body view header counter) ?_ eachRun).1
      intro depth exit bodyInput value bodyOutput bodyGenerated bodyLive bodyFrames bodyLower bodyExt bodyGrowth bodyTypes bodyTerms bodyRun
      exact bodyNew owner view sourceState sourceRun sourceLive header counter depth exit bodyInput value bodyOutput
        bodyGenerated bodyLive bodyFrames bodyLower ((prefixExt.trans headerExt).trans bodyExt)
        (Nat.le_trans (Nat.le_trans startedGrowth headerGrowth) bodyGrowth)
        ((prefixTypes.trans headerTypes).trans bodyTypes)
        ((prefixFrames.1.compose headerFrames prefixExt).compose bodyTerms (prefixExt.trans headerExt)) bodyRun
  exact startedNew.compose_framed tailRules
    (show eachStatementTail slot index byRef origin body owner view regrow sampled start le started = (result,after) from tailRun)
    (eachStatementTail_dense _ _ _ _ _ _ _ _ _ _) (eachStatementTail_advance _ _ _ _ _ _ _ _ _ _)
    (eachStatementTail_types _ _ _ _ _ _ _ _ _ _) (eachStatementTail_frames _ _ _ _ _ _ _ _ _ _) startedGenerated trivial

#print axioms forEach_newPermissionInstructions

end Goose.Lower.Validation
