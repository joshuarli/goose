import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlOptional
import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlLoops

namespace Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl

open Goose.Core Goose.GIR

def whileSetup (condition : Expr) : B (Option (BlockId × Nat × BlockId)) := do
  let (header, _) ← newBlock []
  emitTerm (.br header [])
  setCur (some header)
  let value ← lowerExpr condition
  whenLive none fun _ => do
    let pair ← loopPrefix value
    pure (some (header, pair.1, pair.2))

def rangeSetup (lo hi : Expr) : B (Option (IntTy × ValueId × ValueId × BlockId × Nat × BlockId)) := do
  let lower ← lowerExpr lo
  let upper ← lowerExpr hi
  whenLive none fun _ => do
    let type ← intTyOf lower
    let (header, parameters) ← newBlock [.data (.int type)]
    let counter := parameters.headD 0
    emitTerm (.br header [lower])
    setCur (some header)
    let condition ← emitDef (.cmp .lt type counter upper)
    let pair ← loopPrefix condition
    pure (some (type, counter, upper, header, pair.1, pair.2))

def eachSetup (view : View) : B (Option (ValueId × ValueId × BlockId × Nat × BlockId)) := do
  let (owner, value) ← lowerEachSource view
  let regrow ← regrowOf owner
  let sampled ← eachSampled regrow value
  let start ← emitDef (.constInt .i64 0)
  whenLive none fun _ => do
    let (header, parameters) ← newBlock [.data (.int .i64)]
    let counter := parameters.headD 0
    emitTerm (.br header [start])
    setCur (some header)
    let length ← eachLen regrow owner sampled
    let condition ← emitDef (.cmp .lt .i64 counter length)
    let pair ← loopPrefix condition
    pure (some (value, counter, header, pair.1, pair.2))

def eachBody (x : VarId) (index : Option VarId) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (arguments : ValueId × ValueId × BlockId × Nat × BlockId) : B ValueId := do
  let (view, counter, header, depth, exit) := arguments
  let element ← emitDef (.refElem view counter)
  let value ← eachElemValue x byRef element
  let bindings := (x, value, origin) :: (match index with
    | some slot => [(slot, counter, origin)]
    | none => [])
  lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body

theorem while_factor (loop : Option LoopCtx) (condition : Expr) (body : Core.Block) (origin : OriginId) :
    lowerStmt loop (.while condition body origin) = (do
      let selected ← whileSetup condition
      match selected with
      | none => pure ()
      | some (header, depth, exit) =>
        let _ ← lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body
        emitTerm (.br header [])
        setCur (some exit)) := by
  funext env state
  simp only [lowerStmt, whileSetup, lowerWhile, loopBody, loopPrefix, bind_run, pure_run]
  cases current : (lowerExpr condition env
      (setCur (some (newBlock [] env state).1.1) env
        (emitTerm (.br (newBlock [] env state).1.1 []) env (newBlock [] env state).2).2).2).2.cur <;>
    first
    | simp only [whenLive_none _ _ _ current, bind_run, pure_run]
    | simp only [whenLive_some _ _ _ current, bind_run, pure_run]

theorem range_factor (loop : Option LoopCtx) (x : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId) :
    lowerStmt loop (.forRange x lo hi body origin) = (do
      let selected ← rangeSetup lo hi
      match selected with
      | none => pure ()
      | some (type, counter, _, header, depth, exit) =>
        let _ ← lowerBlock (some ⟨depth, exit, .next header type counter⟩) [(x, counter, origin)] false body
        rangeBack type counter header
        setCur (some exit)) := by
  funext env state
  simp only [lowerStmt, rangeSetup, lowerRange, loopBody, loopPrefix, bind_run, pure_run]
  cases current : (lowerExpr hi env (lowerExpr lo env state).2).2.cur <;>
    first
    | simp only [whenLive_none _ _ _ current, bind_run, pure_run]
    | simp only [whenLive_some _ _ _ current, bind_run, pure_run]

theorem each_factor (loop : Option LoopCtx) (x : VarId) (index : Option VarId) (view : View)
    (byRef : Bool) (body : Core.Block) (origin : OriginId) :
    lowerStmt loop (.forEach x index view byRef body origin) = (do
      let selected ← eachSetup view
      match selected with
      | none => pure ()
      | some arguments =>
        let _ ← eachBody x index byRef body origin arguments
        rangeBack .i64 arguments.2.1 arguments.2.2.1
        setCur (some arguments.2.2.2.2)) := by
  funext env state
  simp only [lowerStmt, eachSetup, eachBody, lowerEach, loopBody, loopPrefix, bind_run, pure_run]
  generalize head : lowerEachSource view env state = ownerPair
  obtain ⟨⟨owner, value⟩, sourceState⟩ := ownerPair
  generalize regrowRun : regrowOf owner env sourceState = regrowPair
  obtain ⟨regrow, regrowState⟩ := regrowPair
  generalize sampleRun : eachSampled regrow value env regrowState = sampledPair
  obtain ⟨sampled, sampledState⟩ := sampledPair
  generalize startRun : emitDef (.constInt .i64 0) env sampledState = startPair
  obtain ⟨start, startState⟩ := startPair
  cases current : startState.cur <;>
    first
    | simp only [whenLive_none _ _ _ current, bind_run, pure_run]
    | simp only [whenLive_some _ _ _ current, bind_run, pure_run]

  all_goals rfl

end Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl
