import Goose.Lower.Validation.SourceReplacementWriterLedgerChildGenerated

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem newHeader_entry_generated (types : List VTy) (arguments : List ValueId) (env : LEnv) (before : LS)
    (checked : GeneratedBuilderState before) :
    let header := newBlock types env before
    let jumped := (emitTerm (.br header.1.1 arguments) env header.2).2
    let entry := (setCur (some header.1.1) env jumped).2
    GeneratedBuilderState entry ∧ header.1.1 < entry.blocks.size := by
  dsimp only
  let header := newBlock types env before
  have headerBound : header.1.1 < header.2.blocks.size := by
    change before.blocks.size < (before.blocks.push _).size
    simp
  have jumped := (checked.newBlock types (env := env) rfl).emitTerm (.br header.1.1 arguments)
    (by intro target member; simp only [Term.successors, List.mem_singleton] at member; exact member ▸ headerBound)
    (env := env) rfl
  have bound : header.1.1 < (emitTerm (.br header.1.1 arguments) env header.2).2.blocks.size :=
    Nat.lt_of_lt_of_le headerBound (advB_emitTerm _ env header.2 _ _ rfl).ext.1
  exact ⟨jumped.setCur _ (env := env) (by intro target same; cases Option.some.inj same; exact bound) rfl,
    by simpa only [setCur_run] using bound⟩

theorem fork_header_bounds (condition : ValueId) (header : BlockId) (env : LEnv) (before : LS)
    (bounded : header < before.blocks.size) :
    let split := fork condition env before
    let entry := (setCur (some split.1.1) env split.2).2
    split.1.2 < entry.blocks.size ∧ header < entry.blocks.size := by
  dsimp only
  have growth : before.Ext (fork condition env before).2 := (advB_fork condition env before _ _ rfl).ext
  exact ⟨by simpa only [setCur_run] using (fork_entry_liveBound condition env before).2,
    by
      change header < (fork condition env before).2.blocks.size
      exact Nat.lt_of_lt_of_le bounded growth.1⟩

theorem whileChildren_generated (env : LEnv) (before : LS) (condition : Expr) (body : Core.Block)
    (checked : GeneratedBuilderState before) : ChildrenGenerated (whileChildren env before condition body) := by
  let header := newBlock [] env before
  let jumped := (emitTerm (.br header.1.1 []) env header.2).2
  let conditionBefore := (setCur (some header.1.1) env jumped).2
  let tested := lowerExpr condition env conditionBefore
  have entry := newHeader_entry_generated [] [] env before checked
  change (GeneratedBuilderState conditionBefore ∧ True) ∧ ChildrenGenerated [if tested.2.cur.isSome then
    let split := fork tested.1 env tested.2
    let bodyBefore := (setCur (some split.1.1) env split.2).2
    some (.block (some ⟨tested.2.stack.length, split.1.2, .jump header.1.1⟩) [] false body, bodyBefore)
    else none]
  refine ⟨⟨entry.1, trivial⟩, ?_⟩
  split
  · have headerBound := Nat.lt_of_lt_of_le entry.2 (advB_lowerExpr condition env conditionBefore _ _ rfl).ext.1
    exact ⟨⟨fork_entry_generated tested.1 env tested.2 (entry.1.lowerExpr condition rfl),
      fork_header_bounds tested.1 header.1.1 env tested.2 headerBound⟩, trivial⟩
  · trivial

theorem rangeChild_generated (env : LEnv) (before : LS) (varId : VarId) (low high : ValueId)
    (body : Core.Block) (origin : OriginId) (checked : GeneratedBuilderState before) :
    ChildrenGenerated [rangeChild env before varId low high body origin] := by
  unfold rangeChild
  split
  · let type := (intTyOf low env before).1
    let header := newBlock [.data (.int type)] env before
    let counter := header.1.2.headD 0
    let headerBefore := (setCur (some header.1.1) env (emitTerm (.br header.1.1 [low]) env header.2).2).2
    let tested := emitDef (.cmp .lt type counter high) env headerBefore
    have entry := newHeader_entry_generated [.data (.int type)] [low] env before checked
    have headerBound := Nat.lt_of_lt_of_le entry.2 (advB_emitDef (.cmp .lt type counter high) env headerBefore _ _ rfl).ext.1
    exact ⟨⟨fork_entry_generated tested.1 env tested.2 (entry.1.emitDef _ rfl),
      fork_header_bounds tested.1 header.1.1 env tested.2 headerBound⟩, trivial⟩
  · trivial

theorem eachChild_generated (env : LEnv) (before : LS) (varId : VarId) (index : Option VarId)
    (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (checked : GeneratedBuilderState before) : ChildrenGenerated [eachChild env before varId index view byRef body origin] := by
  let source := lowerEachSource view env before
  let regrow := regrowOf source.1.1 env source.2
  let sampled := eachSampled regrow.1 source.1.2 env regrow.2
  let startAt := emitDef (.constInt .i64 0) env sampled.2
  have sourceGenerated := checked.lowerEachSource view (env := env) rfl
  have regrowGenerated := sourceGenerated.regrowOf source.1.1 (env := env) rfl
  have sampledGenerated := regrowGenerated.eachSampled regrow.1 source.1.2 (env := env) rfl
  have startGenerated := sampledGenerated.emitDef (.constInt .i64 0) (env := env) rfl
  unfold eachChild
  dsimp only
  split
  · let header := newBlock [.data (.int .i64)] env startAt.2
    let counter := header.1.2.headD 0
    let headerBefore := (setCur (some header.1.1) env (emitTerm (.br header.1.1 [startAt.1]) env header.2).2).2
    let length := eachLen regrow.1 source.1.1 sampled.1 env headerBefore
    let tested := emitDef (.cmp .lt .i64 counter length.1) env length.2
    let split := fork tested.1 env tested.2
    let elementBefore := (setCur (some split.1.1) env split.2).2
    let element := emitDef (.refElem source.1.2 counter) env elementBefore
    let value := eachElemValue varId byRef element.1 env element.2
    have entry := newHeader_entry_generated [.data (.int .i64)] [startAt.1] env startAt.2 startGenerated
    have lengthGenerated := entry.1.eachLen regrow.1 source.1.1 sampled.1 (env := env) rfl
    have testGenerated := lengthGenerated.emitDef (.cmp .lt .i64 counter length.1) (env := env) rfl
    have headerBound := Nat.lt_of_lt_of_le entry.2
      ((advB_eachLen regrow.1 source.1.1 sampled.1 env headerBefore _ _ rfl).ext.trans
        (advB_emitDef (.cmp .lt .i64 counter length.1) env length.2 _ _ rfl).ext).1
    have bounds := fork_header_bounds tested.1 header.1.1 env tested.2 headerBound
    have elementGenerated := (fork_entry_generated tested.1 env tested.2 testGenerated).emitDef
      (.refElem source.1.2 counter) (env := env) rfl
    have valueGenerated := elementGenerated.eachElemValue varId byRef element.1 (env := env) rfl
    have growth := (advB_emitDef (.refElem source.1.2 counter) env elementBefore _ _ rfl).ext.trans
      (advB_eachElemValue varId byRef element.1 env element.2 _ _ rfl).ext
    exact ⟨⟨valueGenerated, ⟨Nat.lt_of_lt_of_le bounds.1 growth.1,
      Nat.lt_of_lt_of_le bounds.2 growth.1⟩⟩, trivial⟩
  · trivial

#print axioms whileChildren_generated
#print axioms rangeChild_generated
#print axioms eachChild_generated

end Goose.Lower.Validation.SourceReplacementWriterLedger
