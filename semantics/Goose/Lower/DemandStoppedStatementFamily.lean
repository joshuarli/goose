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

theorem accepted_generated_expression_statement_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (expression : Expr) (origin : OriginId)
    (childFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop expression) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.expr expression origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  obtain ⟨child, typing, roots, canonical⟩ := source.exprChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression expression) before := by
    rw [canonical.path]
    exact .first occurrence (.discard loop expression origin)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.discard loop expression origin)) required := .first (first := .discard loop expression origin) rows
    simpa only [roots, canonical.path] using inherited
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 0 (.expression expression) .expression rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
    rw [demandContextRetainedEq canonical.plans canonical.path rfl canonical.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 0 (.expression expression) .expression rfl (by trivial)
      (admitted profile alias member)
  have childRealized : map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv before initial start := by
    rw [typing, roots]
    exact input
  have lowered : (lowerStmt loop (.expr expression origin) (lowerEnv cfg.mod env.vars results) before).2 =
      (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 := by
    simp only [lowerStmt, bind_run, pure_run]
  have childExtended := extended
  rw [lowered] at childExtended
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
