import Goose.Lower.DemandExpressionStatementEntry
import Goose.Lower.DemandReadStoppedFamily
import Goose.Lower.DemandControlStatementPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive StoppedStatementPrefix {cfg : Cfg} {env : Env} {statement : Stmt} {state : St}
    (source : StmtSource cfg env statement state) (map : RetainedSsaMap) (cx : FnCtx) (results : List Ty)
    (loop : Option LoopCtx) (before : LS) (initial : GIR.Frame) (start : Pt) (taken : Nat)
    (reached : DemandRuntimePoint) (stop : Stop) (after : St) : Prop
  | aborted (fuel : Nat) (evaluated : (execStmt fuel cfg env statement >>= prepareLoopFlow env loop) state = .stop stop after) :
      StoppedStatementPrefix source map cx results loop before initial start taken reached stop after
  | complete {fuel consumed remaining : Nat} {boundary : DemandRuntimePoint} {flow : Flow}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (evaluated : (execStmt fuel cfg env statement >>= prepareLoopFlow env loop) state = .ok flow boundary.state)
      (post : GeneratedStatementPrefixEnd source map cx before initial
        (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 loop flow boundary) :
      StoppedStatementPrefix source map cx results loop before initial start taken reached stop after

def GeneratedStoppedStatementPrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (statement : Stmt) : Prop :=
  ∀ {state : St} (source : StmtSource cfg env statement state) {before : LS}
    (_owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop statement) before)
    {required map : RetainedSsaMap} (_rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required),
    map.Covers required → map.Admitted cfg.mod.profile source.context.retained → map.Bounded before.vals.size →
    ∀ {initial : GIR.Frame} {start : Pt}, map.Realizes cfg.mod source.world env ⟨start, initial, state⟩ →
    GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start →
    ExtT (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks →
    ∀ {taken : Nat} {reached : DemandRuntimePoint}, DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached →
    ∀ {fuel : Nat} {stop : Stop} {after : St}, DemandInstructionStop cx fuel reached stop after → stop ≠ .timeout →
    StoppedStatementPrefix source map cx results loop before initial start taken reached stop after

def InvariantStoppedStatementPrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (statement : Stmt) (invariant : DemandRuntimePoint → Prop) : Prop :=
  ∀ {state : St} (source : StmtSource cfg env statement state) {before : LS}
    (_owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop statement) before)
    {required map : RetainedSsaMap} (_rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required),
    map.Covers required → map.Admitted cfg.mod.profile source.context.retained → map.Bounded before.vals.size →
    ∀ {initial : GIR.Frame} {start : Pt}, map.Realizes cfg.mod source.world env ⟨start, initial, state⟩ →
    GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start →
    ExtT (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks →
    invariant ⟨start, initial, state⟩ →
    ∀ {taken : Nat} {reached : DemandRuntimePoint}, DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached →
    ∀ {fuel : Nat} {stop : Stop} {after : St}, DemandInstructionStop cx fuel reached stop after → stop ≠ .timeout →
    StoppedStatementPrefix source map cx results loop before initial start taken reached stop after


theorem GeneratedStoppedStatementPrefixFamily.withInvariant {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {loop : Option LoopCtx} {statement : Stmt}
    (family : GeneratedStoppedStatementPrefixFamily cx results selected loop statement) (invariant : DemandRuntimePoint → Prop) :
    InvariantStoppedStatementPrefixFamily cx results selected loop statement invariant := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
  exact family source owned occurrence rows coverage admitted bounded realized input extended steps stopped nonTimeout

theorem accepted_generated_expression_statement_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (expression : Expr) (origin : OriginId)
    (childFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop expression) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.expr expression origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  obtain ⟨child, typing, roots, canonical, childOccurrence, childRows, childOwner, childAdmitted,
    childRealized, childInput, childExtended, lowered⟩ :=
    accepted_generated_expression_statement_entry source selected owned occurrence rows admitted realized input extended
  have childProgress := childFamily child childOwner childOccurrence childRows coverage childAdmitted bounded
    childRealized childInput childExtended steps stopped nonTimeout
  cases childProgress with
  | aborted sourceFuel stopped =>
    apply StoppedStatementPrefix.aborted (sourceFuel + 1)
    simp only [bind_apply, execStmt, stopped]
  | @complete sourceFuel consumed remaining boundary value count prefixSteps residual evaluated finished =>
    have raw : execStmt (sourceFuel + 1) cfg env (.expr expression origin) state = .ok (.normal .unit) boundary.state := by
      simp only [execStmt, bind_apply, evaluated, pure_apply]
    have prepared : (execStmt (sourceFuel + 1) cfg env (.expr expression origin) >>= prepareLoopFlow env loop) state =
        .ok (.normal .unit) boundary.state := by
      simp only [bind_apply, raw]
      cases loop <;> rfl
    have carried : map.Realizes cfg.mod source.world env boundary := by
      simpa only [RetainedSsaMap.Realizes, canonical.world] using finished.demanded.operands
    exact .complete count prefixSteps residual prepared
      (.normal (by rw [lowered]; exact Post.nil finished.post.pp finished.post.mono finished.post.same finished.post.rel)
        (source.result (sourceFuel + 1) (.normal .unit) raw) (by rw [lowered]; exact finished.bounded) carried)

#print axioms accepted_generated_expression_statement_stopped_family

end Goose.Lower
