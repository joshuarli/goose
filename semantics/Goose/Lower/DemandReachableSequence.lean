import Goose.Lower.DemandIfMixedSequence
import Goose.Lower.DemandStoppedSequenceFamily
import Goose.Lower.DemandGeneratedSequencePrefix
import Goose.Lower.DemandRunAtPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel Goose.Evidence

abbrev ReachableStatementPrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (statement : Stmt)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) : Prop :=
  InvariantStatementPrefixFamily cx results selected loop statement (@cursor)
    (fun point => RuntimePoint cx.cfg cx.fn point.point point.frame point.state)

abbrev ReachableSequencePrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) (statements : List Stmt)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) : Prop :=
  InvariantSequencePrefixFamily cx results selected before loop bindings want block statements (@cursor)
    (fun point => RuntimePoint cx.cfg cx.fn point.point point.frame point.state)

theorem accepted_generated_reachable_sequence_prefix_cons {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    {statement : Stmt} {rest : List Stmt}
    (headFamily : ReachableStatementPrefixFamily cx results selected loop statement (@cursor))
    (tailFamily : ReachableSequencePrefixFamily cx results selected before loop bindings want block rest (@cursor)) :
    ReachableSequencePrefixFamily cx results selected before loop bindings want block (statement :: rest) (@cursor) := by
  exact accepted_generated_invariant_sequence_prefix_cons selected before loop bindings want block cursor
    (fun point => RuntimePoint cx.cfg cx.fn point.point point.frame point.state)
    (fun valid steps => steps.reachable valid) headFamily tailFamily

abbrev ReachableStoppedStatementPrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (statement : Stmt) : Prop :=
  InvariantStoppedStatementPrefixFamily cx results selected loop statement
    (fun point => RuntimePoint cx.cfg cx.fn point.point point.frame point.state)

abbrev ReachableStoppedSequencePrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) (statements : List Stmt) : Prop :=
  InvariantStoppedSequencePrefixFamily cx results selected before loop bindings want block statements
    (fun point => RuntimePoint cx.cfg cx.fn point.point point.frame point.state)

theorem accepted_generated_reachable_stopped_sequence_cons {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    {statement : Stmt} {rest : List Stmt}
    (headFamily : ReachableStoppedStatementPrefixFamily cx results selected loop statement)
    (tailFamily : ReachableStoppedSequencePrefixFamily cx results selected before loop bindings want block rest) :
    ReachableStoppedSequencePrefixFamily cx results selected before loop bindings want block (statement :: rest) := by
  exact accepted_generated_invariant_stopped_sequence_cons selected before loop bindings want block
    (fun point => RuntimePoint cx.cfg cx.fn point.point point.frame point.state)
    (fun valid steps => steps.reachable valid) headFamily tailFamily


theorem GeneratedSequencePrefixFamily.reachable {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {before : LS} {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    {block : Core.Block} {statements : List Stmt}
    {cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (family : GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements (@cursor)) :
    ReachableSequencePrefixFamily cx results selected before loop bindings want block statements (@cursor) := by
  intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
  exact family source owned occurrence all scope value rows coverage admitted bounded realized input extended steps

theorem GeneratedStoppedSequencePrefixFamily.reachable {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {before : LS} {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    {block : Core.Block} {statements : List Stmt}
    (family : GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block statements) :
    ReachableStoppedSequencePrefixFamily cx results selected before loop bindings want block statements := by
  intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
  exact family source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout


theorem ReachableStatementPrefixFamily.mapCursor {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {loop : Option LoopCtx} {statement : Stmt}
    {cursor next : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (family : ReachableStatementPrefixFamily cx results selected loop statement cursor)
    (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → next source before built initial start map required runtime) :
    ReachableStatementPrefixFamily cx results selected loop statement next := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps
  have decomposition := family source owned occurrence rows coverage admitted bounded realized input extended callerStart steps
  refine ⟨decomposition.sourceOwner, decomposition.coverage, ?_⟩
  cases decomposition.progress with
  | interior demanded => exact .interior (convert source demanded)
  | complete count prefixSteps residual evaluated post => exact .complete count prefixSteps residual evaluated post


theorem ReachableSequencePrefixFamily.mapCursor {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {before : LS} {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    {block : Core.Block} {statements : List Stmt}
    {cursor next : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (family : ReachableSequencePrefixFamily cx results selected before loop bindings want block statements cursor)
    (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → next source before built initial start map required runtime) :
    ReachableSequencePrefixFamily cx results selected before loop bindings want block statements next := by
  intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps
  have decomposition := family source owned occurrence all scope value rows coverage admitted bounded realized input extended callerStart steps
  refine ⟨decomposition.sourceOwner, decomposition.coverage, ?_⟩
  cases decomposition.progress with
  | interior demanded => exact .interior (demanded.map convert)
  | complete count prefixSteps residual evaluated post => exact .complete count prefixSteps residual evaluated post

#print axioms ReachableSequencePrefixFamily.mapCursor
#print axioms ReachableStatementPrefixFamily.mapCursor
#print axioms GeneratedSequencePrefixFamily.reachable
#print axioms GeneratedStoppedSequencePrefixFamily.reachable
#print axioms accepted_generated_reachable_stopped_sequence_cons

#print axioms accepted_generated_reachable_sequence_prefix_cons
end Goose.Lower
