import Goose.Lower.DemandGeneratedSequencePrefix
import Goose.Lower.DemandGeneratedClearSequence

namespace Goose.Lower

open Goose.Core Goose.GIR

inductive GeneratedGlobalClearPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | clear {global : GlobalId} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.clear (.global global) origin) state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
      {runtime : DemandRuntimePoint}
      (demanded : GeneratedClearDemand source map required cx before
        (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).2 built initial start
        (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1 runtime)
      (instruction : (∃ id op, instAt cx.fn runtime.point = some (.def id op)) ∨
        ∃ effect, instAt cx.fn runtime.point = some (.eff effect)) :
      GeneratedGlobalClearPrefixCursor cx results source before built initial start map required runtime

theorem accepted_generated_global_clear_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (global : GlobalId) (origin : OriginId) :
    GeneratedStatementPrefixFamily cx results selected loop (.clear (.global global) origin)
      (@GeneratedGlobalClearPrefixCursor cfg env cx results) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  have progress := accepted_generated_global_clear_prefix source selected owned occurrence rows coverage admitted bounded
    realized input.atPoint input.related extended steps
  refine ⟨owned, coverage, ?_⟩
  cases progress.progress with
  | interior demanded => exact .interior (.clear demanded.1 demanded.2)
  | complete count prefixSteps residual evaluated post => exact .complete count prefixSteps residual evaluated post

theorem accepted_generated_global_clears_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : GlobalClearStatements statements) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements
      (@GeneratedGlobalClearPrefixCursor cfg env cx results) := by
  induction fragment with
  | nil => exact accepted_generated_sequence_prefix_nil selected before loop bindings want block _
  | cons global origin remaining ih =>
    exact accepted_generated_sequence_prefix_cons selected before loop bindings want block _
      (accepted_generated_global_clear_prefix_family selected loop global origin) ih

theorem GeneratedGlobalClearPrefixCursor.frame {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint}
    (demanded : GeneratedGlobalClearPrefixCursor cx results source before built initial start map required runtime) :
    ∃ typing roots future, DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime := by
  cases demanded with
  | clear demanded instruction => exact demanded.frame

theorem GeneratedSequencePrefixCursor.globalClear_frame {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {initial runtime : DemandRuntimePoint}
    (demanded : GeneratedSequencePrefixCursor (@GeneratedGlobalClearPrefixCursor cfg env cx results)
      map required cx results before loop bindings block selected source initial runtime) :
    ∃ typing roots future, DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime := by
  induction demanded with
  | head canonical owned occurrence rows coverage demanded =>
    simpa only [canonical.world] using demanded.frame
  | tail canonical evaluated prefixSteps post demanded ih =>
    simpa only [canonical.world] using ih

end Goose.Lower
