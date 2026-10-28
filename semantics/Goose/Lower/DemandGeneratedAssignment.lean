import Goose.Lower.DemandGeneratedConstruction

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_assignment_value_extended {le : LEnv} {before : LS} {place : Place} {value : Expr}
    {origin : OriginId} {loop : Option LoopCtx} {blocks : Array GIR.Block}
    (extended : ExtT (lowerStmt loop (.assign place value origin) le before).2 blocks) :
    ExtT (lowerExpr value le (lowerPlace place le before).2).2 blocks := by
  have emitted : ExtT (emitEffect (.store (lowerPlace place le before).1
      (lowerExpr value le (lowerPlace place le before).2).1 (some origin)) le
      (lowerExpr value le (lowerPlace place le before).2).2).2 blocks := by
    simpa only [lowerStmt, bind_run] using extended
  exact emitted.of_adv (adv_emitEffect rfl)

theorem generated_assignment_place_extended {le : LEnv} {before : LS} {place : Place} {value : Expr}
    {origin : OriginId} {loop : Option LoopCtx} {blocks : Array GIR.Block}
    (extended : ExtT (lowerStmt loop (.assign place value origin) le before).2 blocks) :
    ExtT (lowerPlace place le before).2 blocks :=
  (generated_assignment_value_extended extended).of_adv (advB_lowerExpr value le _ _ _ rfl)

structure GeneratedAssignmentStoreSite (m : Core.Module) (access : AccessEnv) (function : Func)
    (le : LEnv) (root : DemandNode) (path : List Nat) (before : LS) (loop : Option LoopCtx)
    (place : Place) (value : Expr) (origin : OriginId) (required : RetainedSsaMap) (point : Pt) : Prop where
  occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.assign place value origin)) before
  rows : GeneratedDemandRows m access occurrence required
  query : ∃ aliases, access.aliasPlace (path ++ [0]) place = .ok aliases
  atPoint : (lowerExpr value le (lowerPlace place le before).2).2.pp = some point
  extended : ExtT (lowerStmt loop (.assign place value origin) le before).2 function.blocks

theorem GeneratedAssignmentStoreSite.instruction {m : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {loop : Option LoopCtx}
    {place : Place} {value : Expr} {origin : OriginId} {required : RetainedSsaMap} {point : Pt}
    (site : GeneratedAssignmentStoreSite m access function le root path before loop place value origin required point) :
    instAt function point = some (.eff (.store (lowerPlace place le before).1
      (lowerExpr value le (lowerPlace place le before).2).1 (some origin))) := by
  have emitted : emitEffect (.store (lowerPlace place le before).1
      (lowerExpr value le (lowerPlace place le before).2).1 (some origin)) le
      (lowerExpr value le (lowerPlace place le before).2).2 =
      ((), (lowerStmt loop (.assign place value origin) le before).2) := by
    simp only [lowerStmt, bind_run]
  simpa only [instAt_eq] using (emitEffect_facts emitted site.atPoint site.extended).2.2.2

theorem GeneratedAssignmentStoreSite.valueRows {m : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {loop : Option LoopCtx}
    {place : Place} {value : Expr} {origin : OriginId} {required : RetainedSsaMap} {point : Pt}
    (site : GeneratedAssignmentStoreSite m access function le root path before loop place value origin required point) :
    ∃ aliases, access.aliasPlace (path ++ [0]) place = .ok aliases ∧
      GeneratedDemandRows m access (.assignmentValue site.occurrence)
        (required.addValues (lowerPlace place le before).1 aliases) := by
  obtain ⟨aliases, query⟩ := site.query
  exact ⟨aliases, query, .assignmentValue site.rows query⟩

#print axioms GeneratedAssignmentStoreSite.valueRows
#print axioms generated_assignment_place_extended
#print axioms GeneratedAssignmentStoreSite.instruction

end Goose.Lower
