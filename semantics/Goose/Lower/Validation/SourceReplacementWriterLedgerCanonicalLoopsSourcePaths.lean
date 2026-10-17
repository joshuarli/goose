import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsWhile
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsRange
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsEachPrelude

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation SummaryPreservation.ReplayBuilder

theorem canonical_while_condition_child (le : LEnv) (initial : LS)
    (loop : Option LoopCtx) (condition : Expr) (body : Core.Block) (origin : OriginId) :
    (Fragment.statement loop (.while condition body origin)).child? le initial 0 =
      some (.expression condition, nativeWhileHeader le initial) := rfl

theorem canonical_while_body_child (le : LEnv) (initial : LS)
    (loop : Option LoopCtx) (condition : Expr) (body : Core.Block) (origin : OriginId)
    (live : (lowerExpr condition le (nativeWhileHeader le initial)).2.cur.isSome = true) :
    (Fragment.statement loop (.while condition body origin)).child? le initial 1 =
      some (.block (some (nativeWhileContext condition le initial)) [] false body,
        nativeWhileBody condition le initial) := by
  have conditionLive : (lowerExpr condition le
      ((setCur (some (newBlock [] le initial).1.1) le
        (emitTerm (.br (newBlock [] le initial).1.1 []) le (newBlock [] le initial).2).2).2)).2.cur.isSome = true := live
  simp only [Fragment.child?, Fragment.children, whileChildren, conditionLive, ↓reduceIte]
  simp [nativeWhileContext, nativeWhileBody, nativeWhileHeader, loopBodyEntry, newBlock0_run]

theorem canonical_range_body_child (le : LEnv) (initial : LS)
    (loop : Option LoopCtx) (variableId : VarId) (low high : Expr) (body : Core.Block) (origin : OriginId)
    (live : (lowerExpr high le (lowerExpr low le initial).2).2.cur.isSome = true) :
    let first := lowerExpr low le initial
    let last := lowerExpr high le first.2
    let type := (intTyOf first.1 le last.2).1
    let allocated := newBlock [.data (.int type)] le last.2
    let counter := allocated.1.2.headD 0
    let started := nativeRangeStart low high le initial
    let compared := emitDef (.cmp .lt type counter last.1) le started
    let split := fork compared.1 le compared.2
    (Fragment.statement loop (.forRange variableId low high body origin)).child? le initial 2 =
      some (.block (some ⟨compared.2.stack.length, split.1.2,
        .next allocated.1.1 type counter⟩) [(variableId, counter, origin)] false body,
        nativeRangeBody type counter last.1 le started) := by
  dsimp only
  simp only [Fragment.child?, Fragment.children, rangeChild, live, ↓reduceIte]
  rfl

private theorem canonical_regrow_source_state (owner : Option ValueId) (le : LEnv) (state : LS) :
    (regrowOf owner le state).2 = state := by
  cases owner with
  | none => rfl
  | some value =>
    simp only [regrowOf, growOwner, bind_run, valTy_run]
    cases (valTy value le state).1 with
    | view _ _ => rfl
    | data type => cases type <;> rfl

theorem canonical_each_body_child (le : LEnv) (initial : LS)
    (loop : Option LoopCtx) (variableId : VarId) (indexVar : Option VarId)
    (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (live : (lowerEachSource view le initial).2.cur.isSome = true) :
    let source := lowerEachSource view le initial
    let regrow := (regrowOf source.1.1 le source.2).1
    let prelude := nativeEachPrefix regrow source.1.2 le source.2
    let length := eachLen regrow source.1.1 prelude.sampled le prelude.state
    let compared := emitDef (.cmp .lt .i64 prelude.counter length.1) le length.2
    let split := fork compared.1 le compared.2
    let entry := eachLoopBodyEntry regrow source.1.1 prelude.sampled prelude.counter le prelude.state
    let address := emitDef (.refElem source.1.2 prelude.counter) le entry
    let produced := eachElemValue variableId byRef address.1 le address.2
    (Fragment.statement loop (.forEach variableId indexVar view byRef body origin)).child? le initial 1 =
      some (.block (some ⟨compared.2.stack.length, split.1.2,
        .next prelude.header .i64 prelude.counter⟩)
        ((variableId, produced.1, origin) :: indexVar.toList.map (fun j => (j, prelude.counter, origin)))
        false body, produced.2) := by
  dsimp only
  let source := lowerEachSource view le initial
  let growing := (regrowOf source.1.1 le source.2).1
  have sampleCur : (eachSampled growing source.1.2 le source.2).2.cur = source.2.cur := by
    cases growing <;> cases current : source.2.cur <;>
      simp [eachSampled, emitDef_run, emitDef_none, pure_run, current]
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  have startLive : (emitDef (.constInt .i64 0) le (eachSampled growing source.1.2 le source.2).2).2.cur.isSome = true := by
    have sampleCurrent : (eachSampled growing source.1.2 le source.2).2.cur = some block := sampleCur.trans current
    simp [emitDef_run _ _ sampleCurrent, sampleCurrent]
  simp only [Fragment.child?, Fragment.children, eachChild, canonical_regrow_source_state]
  change (if (emitDef (.constInt .i64 0) le (eachSampled growing source.1.2 le source.2).2).2.cur.isSome then _ else none) = _
  simp only [startLive, ↓reduceIte]
  rfl

#print axioms canonical_while_condition_child
#print axioms canonical_while_body_child
#print axioms canonical_range_body_child
#print axioms canonical_each_body_child

end Goose.Lower.Validation.SourceReplacementWriterLedger
