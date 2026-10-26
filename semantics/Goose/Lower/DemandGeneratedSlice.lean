import Goose.Lower.DemandGeneratedSliceBounds
import Goose.Lower.DemandGeneratedTransfer
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

def sliceLowerBefore (view : View) (le : LEnv) (before : LS) : LS := (lowerView view le before).2

def sliceUpperBefore (view : View) (lower : Bound) (le : LEnv) (before : LS) : LS :=
  (lowerBound lower le (sliceLowerBefore view le before)).2

def sliceEmissionBefore (view : View) (lower upper : Bound) (le : LEnv) (before : LS) : LS :=
  (lowerBound upper le (sliceUpperBefore view lower le before)).2

def sliceOperation (mutability : Mutability) (view : View) (lower upper : Bound) (origin : OriginId)
    (le : LEnv) (before : LS) : Op :=
  .viewSlice mutability (lowerView view le before).1
    (lowerBound lower le (sliceLowerBefore view le before)).1
    (lowerBound upper le (sliceUpperBefore view lower le before)).1 (some origin)

theorem lowerExpr_slice_run (mutability : Mutability) (view : View) (lower upper : Bound) (origin : OriginId)
    (le : LEnv) (before : LS) :
    lowerExpr (.slice mutability view lower upper origin) le before =
      emitDef (sliceOperation mutability view lower upper origin le before) le
        (sliceEmissionBefore view lower upper le before) := by
  simp only [lowerExpr, bind_run, sliceOperation, sliceLowerBefore, sliceUpperBefore, sliceEmissionBefore]

theorem generated_slice_upper_extended {mutability : Mutability} {view : View} {lower upper : Bound}
    {origin : OriginId} {le : LEnv} {before : LS} {blocks : Array GIR.Block}
    (extended : ExtT (lowerExpr (.slice mutability view lower upper origin) le before).2 blocks) :
    ExtT (sliceEmissionBefore view lower upper le before) blocks := by
  rw [lowerExpr_slice_run] at extended
  exact extended.of_adv (adv_emitDef rfl)

theorem generated_slice_lower_extended {mutability : Mutability} {view : View} {lower upper : Bound}
    {origin : OriginId} {le : LEnv} {before : LS} {blocks : Array GIR.Block}
    (extended : ExtT (lowerExpr (.slice mutability view lower upper origin) le before).2 blocks) :
    ExtT (sliceUpperBefore view lower le before) blocks :=
  (generated_slice_upper_extended extended).of_adv (advB_lowerBound upper le (sliceUpperBefore view lower le before) _ _ rfl)

theorem generated_slice_view_extended {mutability : Mutability} {view : View} {lower upper : Bound}
    {origin : OriginId} {le : LEnv} {before : LS} {blocks : Array GIR.Block}
    (extended : ExtT (lowerExpr (.slice mutability view lower upper origin) le before).2 blocks) :
    ExtT (sliceLowerBefore view le before) blocks :=
  (generated_slice_lower_extended extended).of_adv (advB_lowerBound lower le (sliceLowerBefore view le before) _ _ rfl)

inductive GeneratedSliceInstruction (m : Core.Module) (access : AccessEnv) :
    Func → RetainedSsaMap → DemandSourceLabel → Pt → Inst → Prop where
  | checked {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {mutability : Mutability} {view : View} {lower upper : Bound} {origin : OriginId}
      {required : RetainedSsaMap} {point : Pt}
      (occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (.slice mutability view lower upper origin)) before)
      (rows : GeneratedDemandRows m access (.sliceUpper occurrence) required)
      (atPoint : (sliceEmissionBefore view lower upper le before).pp = some point)
      (extended : ExtT (lowerExpr (.slice mutability view lower upper origin) le before).2 function.blocks) :
      GeneratedSliceInstruction m access function required ⟨path ++ [2], .bound, .exit⟩ point
        (.def (lowerExpr (.slice mutability view lower upper origin) le before).1
          (sliceOperation mutability view lower upper origin le before))

theorem GeneratedSliceInstruction.instruction {m : Core.Module} {access : AccessEnv} {function : Func}
    {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedSliceInstruction m access function required label point instruction) :
    instAt function point = some instruction := by
  cases site with
  | @checked le root path before mutability view lower upper origin required point occurrence rows atPoint extended =>
    have emitted : emitDef (sliceOperation mutability view lower upper origin le before) le
        (sliceEmissionBefore view lower upper le before) =
        ((lowerExpr (.slice mutability view lower upper origin) le before).1,
          (lowerExpr (.slice mutability view lower upper origin) le before).2) := by rw [lowerExpr_slice_run]
    exact (emitDef_facts emitted atPoint extended).2.2.2.2

theorem GeneratedSliceInstruction.requiredRows {m : Core.Module} {access : AccessEnv} {function : Func}
    {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedSliceInstruction m access function required label point instruction) :
    ∃ (le : LEnv) (root : DemandNode) (bound : Bound) (before : LS)
      (occurrence : GeneratedDemandOccurrence m function le root label.path (.bound bound) before),
      GeneratedDemandRows m access occurrence required ∧ label.phase = .bound ∧ label.boundary = .exit := by
  cases site with
  | checked occurrence rows atPoint extended => exact ⟨_, _, _, _, .sliceUpper occurrence, rows, rfl, rfl⟩

structure SliceOperands (lower upper : Bound) where
  sample : ViewVal
  lowerOperand : SliceBoundOperand lower
  upperOperand : SliceBoundOperand upper

def SliceOperands.cells {lower upper : Bound} (operands : SliceOperands lower upper)
    (view : View) (le : LEnv) (before : LS) : List (ValueId × RVal) :=
  ((lowerView view le before).1, .view operands.sample) ::
    (operands.lowerOperand.cells le (sliceLowerBefore view le before) ++
      operands.upperOperand.cells le (sliceUpperBefore view lower le before))

def SliceOperands.PrefixEvaluated {lower upper : Bound} (operands : SliceOperands lower upper)
    (view : View) (fuel : Nat) (cfg : Cfg) (env : Env) (state after : St) : Prop :=
  ∃ afterView afterLower,
    evalView (fuel + 1) cfg env view state = .ok operands.sample afterView ∧
    operands.lowerOperand.PrefixEvaluated fuel cfg env afterView afterLower ∧
    operands.upperOperand.PrefixEvaluated fuel cfg env afterLower after

def SliceOperands.compute {lower upper : Bound} (operands : SliceOperands lower upper) (origin : OriginId) : Except Stop Val :=
  let low := operands.lowerOperand.value operands.sample.len 0
  let high := operands.upperOperand.value operands.sample.len operands.sample.len
  if 0 ≤ low ∧ low ≤ high ∧ high ≤ (operands.sample.len : Int) then
    .ok (.slice operands.sample.loc (operands.sample.start + low.toNat) (high - low).toNat)
  else .error (.abort .sliceOob origin)

theorem SliceOperands.source_decompose {lower upper : Bound} (operands : SliceOperands lower upper)
    (mutability : Mutability) (view : View) (origin : OriginId) {fuel : Nat} {cfg : Cfg} {env : Env}
    {state after : St} (evaluated : operands.PrefixEvaluated view fuel cfg env state after) :
    evalExpr (fuel + 2) cfg env (.slice mutability view lower upper origin) state =
      match operands.compute origin with
      | .ok value => .ok value after
      | .error stop => .stop stop after := by
  obtain ⟨afterView, afterLower, viewed, low, high⟩ := evaluated
  have lowerDone := operands.lowerOperand.source_evaluated low (length := operands.sample.len) (default := 0)
  have upperDone := operands.upperOperand.source_evaluated high (length := operands.sample.len) (default := operands.sample.len)
  simp only [evalExpr, bind_apply, viewed, lowerDone, upperDone, compute]
  split <;> simp only [pure_apply, abortAt, M.stop]

theorem SliceOperands.instruction_decompose {lower upper : Bound} (operands : SliceOperands lower upper)
    (mutability : Mutability) (view : View) (origin : OriginId) {le : LEnv} {before : LS} {frame : GIR.Frame} {cx : FnCtx}
    (has : ∀ cell ∈ operands.cells view le before, frame.vals[cell.1]? = some cell.2) (fuel : Nat) (state : St) :
    execOp fuel cx frame (sliceOperation mutability view lower upper origin le before) state =
      match operands.compute origin with
      | .ok value => .ok (.val value) state
      | .error stop => .stop stop state := by
  have sampleCell := has ((lowerView view le before).1, .view operands.sample) (by simp [cells])
  have lowerCells : ∀ cell ∈ operands.lowerOperand.cells le (sliceLowerBefore view le before),
      frame.vals[cell.1]? = some cell.2 := by
    intro cell member
    exact has cell (List.mem_cons_of_mem _ (List.mem_append_left _ member))
  have upperCells : ∀ cell ∈ operands.upperOperand.cells le (sliceUpperBefore view lower le before),
      frame.vals[cell.1]? = some cell.2 := by
    intro cell member
    exact has cell (List.mem_cons_of_mem _ (List.mem_append_right _ member))
  have lowerDone := operands.lowerOperand.target_evaluated lowerCells operands.sample.len 0 state
  have upperDone := operands.upperOperand.target_evaluated upperCells operands.sample.len operands.sample.len state
  simp only [sliceOperation, execOp, execPure, getView_of sampleCell, bind_apply, pure_apply,
    lowerDone, upperDone, compute]
  split <;> simp_all only [pure_apply, abortAtOrg, abortAt, M.stop]

end Goose.Lower
