import Goose.Lower.DemandGeneratedOccurrence
import Goose.Lower.DemandRetainedRows

namespace Goose.Lower

open Goose.Core Goose.GIR

def RetainedSsaMap.addValues (map : RetainedSsaMap) (id : ValueId) (aliases : List RetainedAlias) : RetainedSsaMap :=
  ⟨aliases.map (fun alias => (id, alias)) ++ map.values, map.runs⟩

def RetainedSsaMap.addRuns (map : RetainedSsaMap) (id : ValueId) (aliases : List RetainedAlias) : RetainedSsaMap :=
  ⟨map.values, aliases.map (fun alias => (id, alias)) ++ map.runs⟩

inductive GeneratedDemandRows (m : Core.Module) (access : AccessEnv) :
    {function : Func} → {le : LEnv} → {root : DemandNode} → {path : List Nat} → {action : DemandLoweringAction} →
    {before : LS} → GeneratedDemandOccurrence m function le root path action before → RetainedSsaMap → Prop
  | functionRoot {contextId : ContextId} {context : Context} {implementation : Impl}
      {contextAt : m.contexts[contextId]? = some context} {implementationAt : m.impls[context.impl]? = some implementation}
      (accessEq : access = (⟨m, implementation, context, []⟩ : PEnv).access) :
      GeneratedDemandRows m access (.functionRoot contextAt implementationAt) ⟨[], []⟩
  | globalRoot {globalId : GlobalId} {global : Core.Global} {globalAt : m.globals[globalId]? = some global}
      (accessEq : access = (⟨m, initImpl, initContext, []⟩ : PEnv).access) :
      GeneratedDemandRows m access (.globalRoot globalAt) ⟨[], []⟩
  | first {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {parent child : DemandLoweringAction}
      {before : LS} {occurrence : GeneratedDemandOccurrence m function le root path parent before}
      {first : parent.FirstChild child} {required : RetainedSsaMap}
      (rows : GeneratedDemandRows m access occurrence required) :
      GeneratedDemandRows m access (.first occurrence first) required
  | binaryRight {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {operation : BinOp} {left right : Expr} {origin : OriginId}
      {occurrence : GeneratedDemandOccurrence m function le root path (.expression (.bin operation left right origin)) before}
      {required : RetainedSsaMap} {aliases : List RetainedAlias}
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasExpr (path ++ [0]) left = .ok aliases) :
      GeneratedDemandRows m access (.binaryRight occurrence)
        (required.addValues (lowerExpr left le before).1 aliases)
  | comparisonRight {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {operation : CmpOp} {left right : Expr}
      {occurrence : GeneratedDemandOccurrence m function le root path (.expression (.cmp operation left right)) before}
      {required : RetainedSsaMap} {aliases : List RetainedAlias}
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasExpr (path ++ [0]) left = .ok aliases) :
      GeneratedDemandRows m access (.comparisonRight occurrence)
        (required.addValues (lowerExpr left le before).1 aliases)
  | shortCircuitRight {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {isAnd : Bool} {left right : Expr}
      {occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (if isAnd then .and left right else .or left right)) before}
      {live : (lowerExpr left le before).2.cur.isSome = true} {required : RetainedSsaMap} {aliases : List RetainedAlias}
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasExpr (path ++ [0]) left = .ok aliases) :
      GeneratedDemandRows m access (.shortCircuitRight occurrence live)
        (required.addValues (lowerExpr left le before).1 aliases)
  | index {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {view : View} {index : Expr} {origin : OriginId}
      {occurrence : GeneratedDemandOccurrence m function le root path (.place (.elem view index origin)) before}
      {required : RetainedSsaMap} {aliases : List RetainedAlias}
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasView (path ++ [0]) view = .ok aliases) :
      GeneratedDemandRows m access (.index occurrence)
        (required.addRuns (lowerView view le before).1 aliases)
  | sliceLower {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {mutability : Mutability} {view : View} {low high : Bound} {origin : OriginId}
      {occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (.slice mutability view low high origin)) before}
      {required : RetainedSsaMap} {aliases : List RetainedAlias}
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasView (path ++ [0]) view = .ok aliases) :
      GeneratedDemandRows m access (.sliceLower occurrence)
        (required.addRuns (lowerView view le before).1 aliases)
  | sliceUpper {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {mutability : Mutability} {view : View} {low high : Bound} {origin : OriginId}
      {occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (.slice mutability view low high origin)) before}
      {required : RetainedSsaMap} {aliases : List RetainedAlias}
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasView (path ++ [0]) view = .ok aliases) :
      GeneratedDemandRows m access (.sliceUpper occurrence)
        (required.addRuns (lowerView view le before).1 aliases)
  | pushValue {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {owner : Place} {value : Expr} {origin : Option OriginId}
      {occurrence : GeneratedDemandOccurrence m function le root path (.expression (.push owner value origin)) before}
      {required : RetainedSsaMap} {aliases : List RetainedAlias}
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasPlace (path ++ [0]) owner = .ok aliases) :
      GeneratedDemandRows m access (.pushValue occurrence)
        (required.addValues (lowerPlace owner le before).1 aliases)
  | argumentValue {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {expression : Expr}
      {occurrence : GeneratedDemandOccurrence m function le root path (.argument (.byVal expression)) before}
      {required : RetainedSsaMap} (rows : GeneratedDemandRows m access occurrence required) :
      GeneratedDemandRows m access (.argumentValue occurrence) required
  | argumentPlace {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {mutability : Mutability} {place : Place}
      {occurrence : GeneratedDemandOccurrence m function le root path (.argument (.byRef mutability place)) before}
      {required : RetainedSsaMap} (rows : GeneratedDemandRows m access occurrence required) :
      GeneratedDemandRows m access (.argumentPlace occurrence) required
  | eachView {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {view : View}
      {occurrence : GeneratedDemandOccurrence m function le root path (.eachSource view) before}
      {required : RetainedSsaMap} (rows : GeneratedDemandRows m access occurrence required) :
      GeneratedDemandRows m access (.eachView occurrence) required
  | blockStatement {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
      {index : Nat} {statement : Stmt}
      {occurrence : GeneratedDemandOccurrence m function le root path (.block loop parameters want block) before}
      {statementAt : block.stmts[index]? = some statement} {required : RetainedSsaMap}
      (rows : GeneratedDemandRows m access occurrence required) :
      GeneratedDemandRows m access (.blockStatement occurrence statementAt) required
  | blockValue {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
      {expression : Expr} {valueAt : block.value = some expression}
      {occurrence : GeneratedDemandOccurrence m function le root path (.block loop parameters want block) before}
      {required : RetainedSsaMap} (rows : GeneratedDemandRows m access occurrence required) :
      GeneratedDemandRows m access (.blockValue occurrence valueAt) required
  | assignmentPlace {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {place : Place} {value : Expr} {origin : OriginId}
      {occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.assign place value origin)) before}
      {required : RetainedSsaMap} (rows : GeneratedDemandRows m access occurrence required) :
      GeneratedDemandRows m access (.assignmentPlace occurrence) required
  | assignmentValue {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {place : Place} {value : Expr} {origin : OriginId}
      {occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.assign place value origin)) before}
      {required : RetainedSsaMap} {aliases : List RetainedAlias}
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasPlace (path ++ [0]) place = .ok aliases) :
      GeneratedDemandRows m access (.assignmentValue occurrence)
        (required.addValues (lowerPlace place le before).1 aliases)
  | clearPlace {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {place : Place} {origin : OriginId}
      {occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.clear place origin)) before}
      {required : RetainedSsaMap} (rows : GeneratedDemandRows m access occurrence required) :
      GeneratedDemandRows m access (.clearPlace occurrence) required

end Goose.Lower
