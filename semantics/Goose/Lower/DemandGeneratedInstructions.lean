import Goose.Lower.DemandGeneratedRows
import Goose.Lower.DemandTrace

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower

def demandBlockValueBefore (le : LEnv) (before : LS) (loop : Option LoopCtx)
    (parameters : List (SlotId × ValueId × OriginId)) (block : Core.Block) : LS :=
  (lowerStmts loop block.stmts le (demandBlockStatementsBefore le before parameters block)).2

inductive GeneratedDemandInstruction (m : Core.Module) (access : AccessEnv) :
    Func → RetainedSsaMap → DemandSourceLabel → Pt → Inst → Prop
  | literal {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {type : IntTy} {number : Int} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.expression (.lit type number)) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : before.pp = some point)
      (instruction : instAt function point = some (.def (lowerExpr (.lit type number) le before).1 (.constInt type number))) :
      GeneratedDemandInstruction m access function required ⟨path, .expression, .entry⟩ point
        (.def (lowerExpr (.lit type number) le before).1 (.constInt type number))
  | boolean {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {value : Bool} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.expression (.bool value)) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : before.pp = some point)
      (instruction : instAt function point = some (.def (lowerExpr (.bool value) le before).1 (.constBool value))) :
      GeneratedDemandInstruction m access function required ⟨path, .expression, .entry⟩ point
        (.def (lowerExpr (.bool value) le before).1 (.constBool value))
  | globalAddress {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {global : GlobalId} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.place (.global global)) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : before.pp = some point)
      (instruction : instAt function point = some (.def (lowerPlace (.global global) le before).1 (.globalAddr global))) :
      GeneratedDemandInstruction m access function required ⟨path, .place, .entry⟩ point
        (.def (lowerPlace (.global global) le before).1 (.globalAddr global))
  | slotAddress {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {variableId : VarId} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.place (.var variableId)) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : before.pp = some point)
      (instruction : instAt function point = some (.def (lowerPlace (.var variableId) le before).1 (.slotAddr variableId))) :
      GeneratedDemandInstruction m access function required ⟨path, .place, .entry⟩ point
        (.def (lowerPlace (.var variableId) le before).1 (.slotAddr variableId))
  | snapshot {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {place : Place} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.view (.of place)) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : (lowerPlace place le before).2.pp = some point)
      (instruction : instAt function point = some
        (.def (lowerView (.of place) le before).1
          (.snapshot (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed) (lowerPlace place le before).1))) :
      GeneratedDemandInstruction m access function required ⟨path, .view, .exit⟩ point
        (.def (lowerView (.of place) le before).1
          (.snapshot (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed) (lowerPlace place le before).1))
  | indexChecked {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {view : View} {index : Expr} {origin : OriginId} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.place (.elem view index origin)) before)
      (requirements : GeneratedDemandRows m access (.index occurrence) required)
      (atPoint : (lowerExpr index le (lowerView view le before).2).2.pp = some point)
      (instruction : instAt function point = some
        (.def (lowerPlace (.elem view index origin) le before).1
          (.indexChecked (lowerView view le before).1 (lowerExpr index le (lowerView view le before).2).1 (some origin)))) :
      GeneratedDemandInstruction m access function required ⟨path ++ [1], .expression, .exit⟩ point
        (.def (lowerPlace (.elem view index origin) le before).1
          (.indexChecked (lowerView view le before).1 (lowerExpr index le (lowerView view le before).2).1 (some origin)))
  | load {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {place : Place} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.expression (.read place)) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : (lowerPlace place le before).2.pp = some point)
      (instruction : instAt function point = some
        (.def (lowerExpr (.read place) le before).1 (.load (lowerPlace place le before).1))) :
      GeneratedDemandInstruction m access function required ⟨path ++ [0], .place, .exit⟩ point
        (.def (lowerExpr (.read place) le before).1 (.load (lowerPlace place le before).1))
  | blockEnter {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {parameters : List (SlotId × ValueId × OriginId)} {want : Bool}
      {block : Core.Block} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.block loop parameters want block) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : before.pp = some point)
      (instruction : instAt function point = some (.eff (.enter block.scope))) :
      GeneratedDemandInstruction m access function required ⟨path, .block, .entry⟩ point (.eff (.enter block.scope))
  | blockLeave {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {parameters : List (SlotId × ValueId × OriginId)} {want : Bool}
      {block : Core.Block} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.block loop parameters want block) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : (lowerBlockValue want block.value le (demandBlockValueBefore le before loop parameters block)).2.pp = some point)
      (instruction : instAt function point = some (.eff (.leave block.scope))) :
      GeneratedDemandInstruction m access function required (match (generalizing := false) block.value with
          | some _ => ⟨path ++ [block.stmts.length], .expression, .exit⟩
          | none => ⟨path, .block, .exit⟩) point (.eff (.leave block.scope))
  | clear {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {place : Place} {origin : OriginId} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.clear place origin)) before)
      (requirements : GeneratedDemandRows m access occurrence required)
      (atPoint : (lowerPlace place le before).2.pp = some point)
      (instruction : instAt function point = some (.eff (.clear (lowerPlace place le before).1 (some origin)))) :
      GeneratedDemandInstruction m access function required ⟨path ++ [0], .place, .exit⟩ point (.eff (.clear (lowerPlace place le before).1 (some origin)))
  | globalReturn {globalId : GlobalId} {global : Core.Global} {point : Pt} {required : RetainedSsaMap}
      (globalAt : m.globals[globalId]? = some global)
      (requirements : GeneratedDemandRows m access (.globalRoot globalAt) required)
      (atPoint : (lowerExpr global.init (lowerEnv m #[] [global.ty]) startLS).2.pp = some point)
      (instruction : instAt (lowerGlobal m global).init point = some
        (.term (.ret [(lowerExpr global.init (lowerEnv m #[] [global.ty]) startLS).1] (some global.org)))) :
      GeneratedDemandInstruction m access (lowerGlobal m global).init required ⟨[], .expression, .exit⟩ point
        (.term (.ret [(lowerExpr global.init (lowerEnv m #[] [global.ty]) startLS).1] (some global.org)))

theorem GeneratedDemandInstruction.instruction {m : Core.Module} {access : AccessEnv} {required : RetainedSsaMap}
    {function : Func} {label : DemandSourceLabel}
    {point : Pt} {inst : Inst} (site : GeneratedDemandInstruction m access function required label point inst) :
    instAt function point = some inst := by
  cases site <;> assumption

theorem GeneratedDemandInstruction.source {m : Core.Module} {access : AccessEnv} {required : RetainedSsaMap}
    {function : Func} {label : DemandSourceLabel} {point : Pt} {inst : Inst}
    (site : GeneratedDemandInstruction m access function required label point inst) :
    ∃ (le : LEnv) (root : DemandNode) (action : DemandLoweringAction) (before : LS),
      GeneratedDemandOccurrence m function le root label.path action before ∧
        label.phase = action.node.primaryPhase := by
  cases site with
  | literal occurrence requirements atPoint instruction => exact ⟨_, _, _, _, occurrence, rfl⟩
  | boolean occurrence requirements atPoint instruction => exact ⟨_, _, _, _, occurrence, rfl⟩
  | globalAddress occurrence requirements atPoint instruction => exact ⟨_, _, _, _, occurrence, rfl⟩
  | slotAddress occurrence requirements atPoint instruction => exact ⟨_, _, _, _, occurrence, rfl⟩
  | snapshot occurrence requirements atPoint instruction => exact ⟨_, _, _, _, occurrence, rfl⟩
  | indexChecked occurrence requirements atPoint instruction => exact ⟨_, _, _, _, .index occurrence, rfl⟩
  | load occurrence requirements atPoint instruction =>
    exact ⟨_, _, _, _, .first occurrence (.expressionPlace rfl), rfl⟩
  | blockEnter occurrence requirements atPoint instruction => exact ⟨_, _, _, _, occurrence, rfl⟩
  | @blockLeave function le root path before loop parameters want block point required occurrence requirements atPoint instruction =>
    cases valueAt : block.value with
    | none => exact ⟨_, _, _, _, occurrence, by rfl⟩
    | some expression =>
      exact ⟨_, _, _, _, .blockValue occurrence valueAt, by rfl⟩
  | clear occurrence requirements atPoint instruction => exact ⟨_, _, _, _, .clearPlace occurrence, rfl⟩
  | globalReturn globalAt requirements atPoint instruction => exact ⟨_, _, _, _, .globalRoot globalAt, rfl⟩

end Goose.Lower
