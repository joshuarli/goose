import Goose.Lower.Validation.SourceReplacementWriterLedgerChildSpansStatementsBranches

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem loopBody_child_span (condition : ValueId) (body : Nat → BlockId → B ValueId) (back : B Unit)
    (backAdvance : AdvB back) (env : LEnv) (before : LS) :
    let split := fork condition env before
    let entry := (setCur (some split.1.1) env split.2).2
    before.Ext entry ∧ ((body before.stack.length split.1.2) env entry).2.Ext (loopBody condition body back env before).2 := by
  dsimp only
  let split := fork condition env before
  let entry := (setCur (some split.1.1) env split.2).2
  let result := body before.stack.length split.1.2 env entry
  have whole : (loopBody condition body back env before).2 =
      (setCur (some split.1.2) env (back env result.2).2).2 := by
    simp only [loopBody, bind_run, get_apply]
    rfl
  refine ⟨(advB_fork condition env before _ _ rfl).ext.trans (setCur_extension _ _ _), ?_⟩
  rw [whole]
  exact (backAdvance env result.2 _ _ rfl).ext.trans (setCur_extension _ _ _)

theorem Fragment.while_child_span {loop : Option LoopCtx} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {child : Fragment} {env : LEnv} {before start : LS} {index : Nat}
    (row : (Fragment.statement loop (.while condition body origin)).child? env before index = some (child, start)) :
    before.Ext start ∧ (child.finish env start).Ext ((Fragment.statement loop (.while condition body origin)).finish env before) := by
  have member := Fragment.child_member row
  let header := newBlock [] env before
  let jumped := (emitTerm (.br header.1.1 []) env header.2).2
  let conditionBefore := (setCur (some header.1.1) env jumped).2
  let tested := lowerExpr condition env conditionBefore
  have entrySpan : before.Ext conditionBefore := (advB_newBlock0 env before _ _ rfl).ext.trans
    ((advB_emitTerm _ env header.2 _ _ rfl).ext.trans (setCur_extension _ _ _))
  have whole : ((Fragment.statement loop (.while condition body origin)).finish env before) =
      (lowerWhile header.1.1 (lowerExpr condition)
        (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header.1.1⟩) [] false body) env conditionBefore).2 := rfl
  change some (child, start) ∈ whileChildren env before condition body at member
  unfold whileChildren at member
  change some (child, start) ∈ [some (.expression condition, conditionBefore),
    if tested.2.cur.isSome then
      let split := fork tested.1 env tested.2
      let bodyBefore := (setCur (some split.1.1) env split.2).2
      some (.block (some ⟨tested.2.stack.length, split.1.2, .jump header.1.1⟩) [] false body, bodyBefore)
    else none] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rw [whole]
  rcases member with same | same
  · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
    subst start
    exact ⟨entrySpan, bind_suffix_ext (lowerExpr condition) _
      (fun value => advB_whenLive () fun _ => advB_loopBody value
        (fun depth exit => advB_lowerBlock (some ⟨depth, exit, .jump header.1.1⟩) [] false body)
        (advB_emitTerm _)) env conditionBefore⟩
  · split at same
    · rename_i live
      let split := fork tested.1 env tested.2
      let bodyBefore := (setCur (some split.1.1) env split.2).2
      have pairEq : (child, start) =
          (.block (some ⟨tested.2.stack.length, split.1.2, .jump header.1.1⟩) [] false body, bodyBefore) := Option.some.inj same
      obtain ⟨rfl, same⟩ := Prod.mk.inj pairEq
      subst start
      have span := loopBody_child_span tested.1
        (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header.1.1⟩) [] false body)
        (emitTerm (.br header.1.1 [])) (advB_emitTerm _) env tested.2
      refine ⟨entrySpan.trans ((advB_lowerExpr condition env conditionBefore _ _ rfl).ext.trans span.1), ?_⟩
      obtain ⟨current, currentAt⟩ := Option.isSome_iff_exists.mp live
      dsimp only [tested] at span currentAt
      simpa only [Fragment.finish, tested, split, bodyBefore, lowerWhile, bind_run, whenLive_some _ _ _ currentAt] using span.2
    · simp at same

theorem Fragment.forRange_child_span {loop : Option LoopCtx} {varId : VarId} {low high : Expr} {body : Core.Block}
    {origin : OriginId} {child : Fragment} {env : LEnv} {before start : LS} {index : Nat}
    (row : (Fragment.statement loop (.forRange varId low high body origin)).child? env before index = some (child, start)) :
    before.Ext start ∧ (child.finish env start).Ext ((Fragment.statement loop (.forRange varId low high body origin)).finish env before) := by
  have member := Fragment.child_member row
  let first := lowerExpr low env before
  let second := lowerExpr high env first.2
  have tailAdvance (a b : ValueId) :
      AdvB (whenLive () fun _ => do
        let type ← intTyOf a
        let (header, parameters) ← newBlock [.data (.int type)]
        let counter := parameters.headD 0
        emitTerm (.br header [a])
        setCur (some header)
        lowerRange type counter b header (fun depth exit =>
          lowerBlock (some ⟨depth, exit, .next header type counter⟩) [(varId, counter, origin)] false body)) := by
    exact advB_whenLive () fun _ => AdvB.bind (advB_intTyOf a) fun type =>
      advB_header1 (.data (.int type)) a
        (fun header counter => advB_lowerRange type counter b header
          (fun depth exit => advB_lowerBlock (some ⟨depth, exit, .next header type counter⟩) [(varId, counter, origin)] false body))
  change some (child, start) ∈ [some (.expression low, before), some (.expression high, first.2),
    rangeChild env second.2 varId first.1 second.1 body origin] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    exact ⟨.refl _, bind_suffix_ext (lowerExpr low) _
      (fun a => AdvB.bind (advB_lowerExpr high) fun b => tailAdvance a b) env _⟩
  · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
    subst start
    exact ⟨(advB_lowerExpr low env before _ _ rfl).ext,
      bind_suffix_ext (lowerExpr high) _ (fun b => tailAdvance first.1 b) env first.2⟩
  · unfold rangeChild at same
    split at same
    · rename_i live
      let type := (intTyOf first.1 env second.2).1
      let header := newBlock [.data (.int type)] env second.2
      let counter := header.1.2.headD 0
      let jumped := (emitTerm (.br header.1.1 [first.1]) env header.2).2
      let headerBefore := (setCur (some header.1.1) env jumped).2
      let tested := emitDef (.cmp .lt type counter second.1) env headerBefore
      let split := fork tested.1 env tested.2
      let bodyBefore := (setCur (some split.1.1) env split.2).2
      have pairEq : (child, start) =
          (.block (some ⟨tested.2.stack.length, split.1.2, .next header.1.1 type counter⟩)
            [(varId, counter, origin)] false body, bodyBefore) := Option.some.inj same
      obtain ⟨rfl, same⟩ := Prod.mk.inj pairEq
      subst start
      have initialSpan : before.Ext second.2 := (advB_lowerExpr low env before _ _ rfl).ext.trans
        (advB_lowerExpr high env first.2 _ _ rfl).ext
      have headerSpan : second.2.Ext tested.2 := (advB_newBlock1 _ env second.2 _ _ rfl).ext.trans
        ((advB_emitTerm _ env header.2 _ _ rfl).ext.trans
          ((setCur_extension _ _ _).trans (advB_emitDef _ env headerBefore _ _ rfl).ext))
      have span := loopBody_child_span tested.1
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header.1.1 type counter⟩)
          [(varId, counter, origin)] false body)
        (rangeBack type counter header.1.1) (advB_rangeBack _ _ _) env tested.2
      refine ⟨initialSpan.trans (headerSpan.trans span.1), ?_⟩
      obtain ⟨current, currentAt⟩ := Option.isSome_iff_exists.mp live
      have queryState : (intTyOf first.1 env second.2).2 = second.2 := intTyOf_eq rfl
      have whole : ((Fragment.statement loop (.forRange varId low high body origin)).finish env before) =
          (loopBody tested.1
            (fun depth exit => lowerBlock (some ⟨depth, exit, .next header.1.1 type counter⟩)
              [(varId, counter, origin)] false body)
            (rangeBack type counter header.1.1) env tested.2).2 := by
        change (lowerStmt loop (.forRange varId low high body origin) env before).2 = _
        simp only [lowerStmt, bind_run]
        change (whenLive () _ env second.2).2 = _
        rw [whenLive_some _ _ _ currentAt]
        dsimp only [first] at queryState
        simp only [bind_run, queryState]
        rfl
      rw [whole]
      exact span.2
    · simp at same

theorem lowerEachSource_view_state (view : View) (env : LEnv) (before : LS) :
    (lowerEachSource view env before).2 = (lowerView view env before).2 := by
  cases view <;> rfl

private def forEachTail (varId : VarId) (iterationIndex : Option VarId) (byRef : Bool)
    (body : Core.Block) (origin : OriginId) (ownerView : Option ValueId × ValueId) : B Unit := do
  let regrow ← regrowOf ownerView.1
  let sampled ← eachSampled regrow ownerView.2
  let startAt ← emitDef (.constInt .i64 0)
  whenLive () fun _ => do
    let (header, parameters) ← newBlock [.data (.int .i64)]
    let counter := parameters.headD 0
    emitTerm (.br header [startAt])
    setCur (some header)
    lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
      let element ← emitDef (.refElem ownerView.2 counter)
      let value ← eachElemValue varId byRef element
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
        ((varId, value, origin) :: (match iterationIndex with | none => [] | some i => [(i, counter, origin)])) false body)

private theorem forEachTail_advance (varId : VarId) (iterationIndex : Option VarId) (byRef : Bool)
    (body : Core.Block) (origin : OriginId) (ownerView : Option ValueId × ValueId) :
    AdvB (forEachTail varId iterationIndex byRef body origin ownerView) := by
  unfold forEachTail
  refine AdvB.bind (advB_regrowOf _) fun regrow => AdvB.bind (advB_eachSampled _ _) fun sampled =>
    AdvB.bind (advB_emitDef _) fun startAt => advB_whenLive () fun _ => ?_
  exact advB_header1 (.data (.int .i64)) startAt
    (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
      let element ← emitDef (.refElem ownerView.2 counter)
      let value ← eachElemValue varId byRef element
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
        ((varId, value, origin) :: (match iterationIndex with | none => [] | some i => [(i, counter, origin)])) false body))
    (fun header counter => advB_lowerEach regrow ownerView.1 sampled header counter
      (fun depth exit => AdvB.bind (advB_emitDef _) fun element =>
        AdvB.bind (advB_eachElemValue varId byRef element) fun value => advB_lowerBlock
          (some ⟨depth, exit, .next header .i64 counter⟩)
          ((varId, value, origin) :: (match iterationIndex with | none => [] | some i => [(i, counter, origin)])) false body))

theorem Fragment.forEach_child_span {loop : Option LoopCtx} {varId : VarId} {iterationIndex : Option VarId}
    {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId} {child : Fragment}
    {env : LEnv} {before start : LS} {index : Nat}
    (row : (Fragment.statement loop (.forEach varId iterationIndex view byRef body origin)).child? env before index = some (child, start)) :
    before.Ext start ∧ (child.finish env start).Ext
      ((Fragment.statement loop (.forEach varId iterationIndex view byRef body origin)).finish env before) := by
  have member := Fragment.child_member row
  let source := lowerEachSource view env before
  let regrow := regrowOf source.1.1 env source.2
  let sampled := eachSampled regrow.1 source.1.2 env regrow.2
  let startAt := emitDef (.constInt .i64 0) env sampled.2
  change some (child, start) ∈ [some (.view view, before),
    eachChild env before varId iterationIndex view byRef body origin] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    refine ⟨.refl _, ?_⟩
    change (lowerView view env start).2.Ext _
    rw [← lowerEachSource_view_state]
    generalize sourceRun : lowerEachSource view env start = sourcePair
    obtain ⟨ownerView, sourceState⟩ := sourcePair
    obtain ⟨owner, viewValue⟩ := ownerView
    have finishEq : ((Fragment.statement loop (.forEach varId iterationIndex view byRef body origin)).finish env start) =
        (forEachTail varId iterationIndex byRef body origin (owner, viewValue) env sourceState).2 := by
      simp only [Fragment.finish, lowerStmt, bind_run, sourceRun]
      cases iterationIndex <;> rfl
    rw [finishEq]
    exact (forEachTail_advance varId iterationIndex byRef body origin (owner, viewValue)
      env sourceState _ _ rfl).ext
  · unfold eachChild at same
    change some (child, start) = (if startAt.2.cur.isSome then
      let header := newBlock [.data (.int .i64)] env startAt.2
      let counter := header.1.2.headD 0
      let jumped := (emitTerm (.br header.1.1 [startAt.1]) env header.2).2
      let headerBefore := (setCur (some header.1.1) env jumped).2
      let length := eachLen regrow.1 source.1.1 sampled.1 env headerBefore
      let tested := emitDef (.cmp .lt .i64 counter length.1) env length.2
      let split := fork tested.1 env tested.2
      let elementBefore := (setCur (some split.1.1) env split.2).2
      let element := emitDef (.refElem source.1.2 counter) env elementBefore
      let value := eachElemValue varId byRef element.1 env element.2
      let bindings := (varId, value.1, origin) :: (iterationIndex.toList.map fun i => (i, counter, origin))
      some (.block (some ⟨tested.2.stack.length, split.1.2, .next header.1.1 .i64 counter⟩) bindings false body, value.2)
      else none) at same
    split at same
    · rename_i live
      let header := newBlock [.data (.int .i64)] env startAt.2
      let counter := header.1.2.headD 0
      let jumped := (emitTerm (.br header.1.1 [startAt.1]) env header.2).2
      let headerBefore := (setCur (some header.1.1) env jumped).2
      let length := eachLen regrow.1 source.1.1 sampled.1 env headerBefore
      let tested := emitDef (.cmp .lt .i64 counter length.1) env length.2
      let split := fork tested.1 env tested.2
      let elementBefore := (setCur (some split.1.1) env split.2).2
      let element := emitDef (.refElem source.1.2 counter) env elementBefore
      let value := eachElemValue varId byRef element.1 env element.2
      let bindings := (varId, value.1, origin) :: (iterationIndex.toList.map fun i => (i, counter, origin))
      have pairEq : (child, start) =
          (.block (some ⟨tested.2.stack.length, split.1.2, .next header.1.1 .i64 counter⟩) bindings false body, value.2) := Option.some.inj same
      obtain ⟨rfl, same⟩ := Prod.mk.inj pairEq
      subst start
      have initialSpan : before.Ext startAt.2 := (advB_lowerEachSource view env before _ _ rfl).ext.trans
        ((advB_regrowOf source.1.1 env source.2 _ _ rfl).ext.trans
          ((advB_eachSampled regrow.1 source.1.2 env regrow.2 _ _ rfl).ext.trans
            (advB_emitDef _ env sampled.2 _ _ rfl).ext))
      have headerSpan : startAt.2.Ext tested.2 := (advB_newBlock1 _ env startAt.2 _ _ rfl).ext.trans
        ((advB_emitTerm _ env header.2 _ _ rfl).ext.trans
          ((setCur_extension _ _ _).trans
            ((advB_eachLen regrow.1 source.1.1 sampled.1 env headerBefore _ _ rfl).ext.trans
              (advB_emitDef _ env length.2 _ _ rfl).ext)))
      let bodyAction := fun depth exit => do
        let element ← emitDef (.refElem source.1.2 counter)
        let value ← eachElemValue varId byRef element
        lowerBlock (some ⟨depth, exit, .next header.1.1 .i64 counter⟩)
          ((varId, value, origin) :: (iterationIndex.toList.map fun i => (i, counter, origin))) false body
      have span := loopBody_child_span tested.1 bodyAction (rangeBack .i64 counter header.1.1)
        (advB_rangeBack _ _ _) env tested.2
      have bodyPrefix : elementBefore.Ext value.2 := (advB_emitDef _ env elementBefore _ _ rfl).ext.trans
        (advB_eachElemValue varId byRef element.1 env element.2 _ _ rfl).ext
      refine ⟨initialSpan.trans (headerSpan.trans (span.1.trans bodyPrefix)), ?_⟩
      obtain ⟨current, currentAt⟩ := Option.isSome_iff_exists.mp live
      have whole : ((Fragment.statement loop (.forEach varId iterationIndex view byRef body origin)).finish env before) =
          (loopBody tested.1 bodyAction (rangeBack .i64 counter header.1.1) env tested.2).2 := by
        change (lowerStmt loop (.forEach varId iterationIndex view byRef body origin) env before).2 = _
        simp only [lowerStmt, bind_run]
        change (whenLive () _ env startAt.2).2 = _
        rw [whenLive_some _ _ _ currentAt]
        cases iterationIndex <;> rfl
      rw [whole]
      exact span.2
    · simp at same

#print axioms loopBody_child_span
#print axioms Fragment.while_child_span
#print axioms Fragment.forRange_child_span
#print axioms Fragment.forEach_child_span

end Goose.Lower.Validation.SourceReplacementWriterLedger
