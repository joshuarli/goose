import Goose.Lower.DemandGeneratedStatementPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedAbortSite {cfg : Cfg} {cx : FnCtx} {le : LEnv} {root : DemandNode} {path : List Nat}
    {before : LS} {loop : Option LoopCtx} {message : String} {origin : OriginId}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root path (.statement loop (.abort message origin)) before)
    (access : AccessEnv) (required : RetainedSsaMap) (point : Pt) : Prop where
  rows : GeneratedDemandRows cfg.mod access occurrence required
  atPoint : before.pp = some point
  extended : ExtT (lowerStmt loop (.abort message origin) le before).2 cx.fn.blocks

theorem GeneratedAbortSite.instruction {cfg : Cfg} {cx : FnCtx} {le : LEnv} {root : DemandNode} {path : List Nat}
    {before : LS} {loop : Option LoopCtx} {message : String} {origin : OriginId}
    {occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root path (.statement loop (.abort message origin)) before}
    {access : AccessEnv} {required : RetainedSsaMap} {point : Pt}
    (site : GeneratedAbortSite occurrence access required point) :
    instAt cx.fn point = some (.term (.abort .userAbort (some origin))) := by
  have emitted : emitTerm (.abort .userAbort (some origin)) le before =
      ((lowerStmt loop (.abort message origin) le before).1, (lowerStmt loop (.abort message origin) le before).2) := rfl
  simpa only [instAt_eq] using (emitTerm_facts emitted site.atPoint site.extended).2.2.2

theorem GeneratedAbortSite.excludes_runtimeStep {cfg : Cfg} {cx : FnCtx} {le : LEnv} {root : DemandNode} {path : List Nat}
    {before : LS} {loop : Option LoopCtx} {message : String} {origin : OriginId}
    {occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root path (.statement loop (.abort message origin)) before}
    {access : AccessEnv} {required : RetainedSsaMap} {point next : Pt} {frame final : GIR.Frame} {state after : St}
    (site : GeneratedAbortSite occurrence access required point)
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame state next final after) : False := by
  cases step with
  | define instruction execution => cases site.instruction.symm.trans instruction
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

theorem GeneratedAbortSite.prefix_zero {cfg : Cfg} {cx : FnCtx} {le : LEnv} {root : DemandNode} {path : List Nat}
    {before : LS} {loop : Option LoopCtx} {message : String} {origin : OriginId}
    {occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root path (.statement loop (.abort message origin)) before}
    {access : AccessEnv} {required : RetainedSsaMap} {point : Pt} {frame : GIR.Frame} {state : St}
    {taken : Nat} {reached : DemandRuntimePoint}
    (site : GeneratedAbortSite occurrence access required point)
    (steps : DemandRuntimePrefix cx taken ⟨point, frame, state⟩ reached) :
    taken = 0 ∧ reached = ⟨point, frame, state⟩ := by
  rcases steps.uncons with zero | ⟨_, _, _, first, _⟩
  · exact zero
  · exact (site.excludes_runtimeStep first).elim

inductive GeneratedAbortPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | entry {message : String} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.abort message origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {root : DemandNode} {owner : Nat} {loop : Option LoopCtx}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (owned : GeneratedSourceOwner selected source.context)
      (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root source.path (.statement loop (.abort message origin)) before)
      (site : GeneratedAbortSite occurrence source.rootsEnv.access required start)
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.inputFuture
        map.values map.runs ⟨start, initial, state⟩) :
      GeneratedAbortPrefixCursor cx results source before built initial start map required ⟨start, initial, state⟩

theorem accepted_generated_abort_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (message : String) (origin : OriginId) :
    GeneratedStatementPrefixFamily cx results selected loop (.abort message origin)
      (@GeneratedAbortPrefixCursor cfg env cx results) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  let site : GeneratedAbortSite occurrence source.rootsEnv.access required start := ⟨rows, input.atPoint, extended⟩
  refine ⟨owned, coverage, ?_⟩
  obtain ⟨_, rfl⟩ := site.prefix_zero steps
  exact .interior (.entry selected owned occurrence site coverage ⟨⟨_, input.atPoint, input.related⟩, source.frame, realized⟩)

end Goose.Lower
