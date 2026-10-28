import Goose.Lower.DemandGeneratedOwner
import Goose.Lower.DemandGeneratedClearTrace
import Goose.Lower.DemandRuntimePrefix
import Goose.Lower.LoopPrepare
import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive DemandPrefixDecomposition {α : Type} (cx : FnCtx) (source : Nat → M α)
    (cursor : DemandRuntimePoint → Prop) (completed : α → DemandRuntimePoint → Prop)
    (taken : Nat) (before reached : DemandRuntimePoint) : Prop
  | interior (demanded : cursor reached) :
      DemandPrefixDecomposition cx source cursor completed taken before reached
  | complete {sourceFuel consumed remaining : Nat} {boundary : DemandRuntimePoint} {value : α}
      (count : consumed + remaining = taken)
      (prefixSteps : DemandRuntimePrefix cx consumed before boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (evaluated : source sourceFuel before.state = .ok value boundary.state)
      (post : completed value boundary) :
      DemandPrefixDecomposition cx source cursor completed taken before reached

inductive GeneratedStatementPrefixEnd {cfg : Cfg} {env : Env} {statement : Stmt} {state : St}
    (source : StmtSource cfg env statement state) (map : RetainedSsaMap) (cx : FnCtx)
    (before : LS) (initial : GIR.Frame) (built : LS) (loop : Option LoopCtx) : Flow → DemandRuntimePoint → Prop
  | normal {runtime : DemandRuntimePoint}
      (post : Post cfg env cx before initial built runtime.frame runtime.point [])
      (result : StmtResult source (.normal .unit) runtime.state)
      (bounded : map.Bounded built.vals.size)
      (realized : map.Realizes cfg.mod source.world env runtime) :
      GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit) runtime
  | transfer {runtime : DemandRuntimePoint} {flow : Flow}
      (abnormal : ∀ value, flow ≠ .normal value)
      (post : StatementLoopPost cfg env cx before initial built loop flow runtime.point runtime.frame) :
      GeneratedStatementPrefixEnd source map cx before initial built loop flow runtime

structure GeneratedStatementPrefixDecomposition {cfg : Cfg} {env : Env} {statement : Stmt} {state : St}
    (source : StmtSource cfg env statement state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop statement) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (map : RetainedSsaMap) (initial : GIR.Frame) (start : Pt) (cursor : DemandRuntimePoint → Prop)
    (taken : Nat) (reached : DemandRuntimePoint) : Prop where
  sourceOwner : GeneratedSourceOwner selected source.context
  coverage : map.Covers required
  progress : DemandPrefixDecomposition cx (fun fuel => execStmt fuel cfg env statement >>= prepareLoopFlow env loop)
    cursor (GeneratedStatementPrefixEnd source map cx before initial
      (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 loop)
    taken ⟨start, initial, state⟩ reached

structure GeneratedPrefixInput (cfg : Cfg) (env : Env) (cx : FnCtx) (results : List Ty)
    (loop : Option LoopCtx) (typing : TEnv) (roots : PEnv) (before : LS) (frame : GIR.Frame) (point : Pt) : Prop where
  metadata : SourceResults typing roots results
  loops : LoopSourceMatches typing loop
  atPoint : before.pp = some point
  related : Rel cfg env cx frame before
  moduleEq : cx.cfg.mod = lower cfg.mod
  resultsEq : cx.fn.results = results
  depth : LoopDepthFits env loop
  targets : match loop with | none => True | some context => LoopTargets cx.fn context
  counter : LoopCounterAt loop before frame
  generated : GeneratedBuilderState before
  frames : LoopBuilderFrames loop before

def GeneratedStatementPrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (statement : Stmt)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) : Prop :=
  ∀ {state : St} (source : StmtSource cfg env statement state) {before : LS}
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop statement) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required),
    map.Covers required → map.Admitted cfg.mod.profile source.context.retained → map.Bounded before.vals.size →
    ∀ {initial : GIR.Frame} {start : Pt},
    map.Realizes cfg.mod source.world env ⟨start, initial, state⟩ →
    GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start →
    ExtT (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks →
    ∀ {taken : Nat} {reached : DemandRuntimePoint}, DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached →
    GeneratedStatementPrefixDecomposition source selected occurrence rows map initial start
      (cursor source before (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 initial start map required) taken reached

def InvariantStatementPrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (statement : Stmt)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) (invariant : DemandRuntimePoint → Prop) : Prop :=
  ∀ {state : St} (source : StmtSource cfg env statement state) {before : LS}
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop statement) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required),
    map.Covers required → map.Admitted cfg.mod.profile source.context.retained → map.Bounded before.vals.size →
    ∀ {initial : GIR.Frame} {start : Pt},
    map.Realizes cfg.mod source.world env ⟨start, initial, state⟩ →
    GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start →
    ExtT (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks →
    invariant ⟨start, initial, state⟩ →
    ∀ {taken : Nat} {reached : DemandRuntimePoint}, DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached →
    GeneratedStatementPrefixDecomposition source selected occurrence rows map initial start
      (cursor source before (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 initial start map required) taken reached


theorem GeneratedStatementPrefixFamily.withInvariant {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {loop : Option LoopCtx} {statement : Stmt}
    {cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (family : GeneratedStatementPrefixFamily cx results selected loop statement (@cursor)) (invariant : DemandRuntimePoint → Prop) :
    InvariantStatementPrefixFamily cx results selected loop statement (@cursor) invariant := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
  exact family source owned occurrence rows coverage admitted bounded realized input extended steps

theorem accepted_generated_global_clear_prefix {cfg : Cfg} {env : Env} {global : GlobalId} {origin : OriginId} {state : St}
    (source : StmtSource cfg env (.clear (.global global) origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.clear (.global global) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (atPoint : before.pp = some point) (related : Rel cfg env cx frame before)
    (extended : ExtT (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨point, frame, state⟩ reached) :
    GeneratedStatementPrefixDecomposition source selected occurrence rows map frame point
      (fun runtime => GeneratedClearDemand source map required cx before
        (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).2
        (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results) before).2 frame point
        (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1 runtime ∧
        ((∃ id op, instAt cx.fn runtime.point = some (.def id op)) ∨
          ∃ effect, instAt cx.fn runtime.point = some (.eff effect))) taken reached := by
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace (.global global) le before
  let middle : DemandRuntimePoint := ⟨(point.1, point.2 + 1), frame.set addressed.1 (.val (.ref ⟨.global global, []⟩)), state⟩
  obtain ⟨child, _, _, rootsEq, _, _, _, _, canonical⟩ := source.clearChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place (.global global)) before := by
    rw [canonical.path]
    exact .clearPlace occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.clearPlace occurrence) required := .clearPlace rows
    simpa only [rootsEq, canonical.path] using inherited
  have addressSite := GeneratedDemandInstruction.globalAddress_auto childOccurrence childRows atPoint
    (generated_clear_place_extended extended)
  have addressPost := (Post.def_leaf (Post.init related atPoint)
    (show emitDef (.globalAddr global) le before = (addressed.1, addressed.2) from rfl)
    (generated_clear_place_extended extended) (.val (.ref ⟨.global global, []⟩))).1
  have placed : evalPlace 1 cfg env (.global global) state = .ok ⟨.global global, []⟩ state := by
    simp only [evalPlace, pure_apply]
  have placeResult := child.result 1 ⟨.global global, []⟩ placed
  have childCarried : map.Realizes cfg.mod child.world env ⟨point, frame, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  have middleCarried := realized.retained addressPost.same bounded.1 bounded.2 RetainsAliases.refl
  have middleChildCarried : map.Realizes cfg.mod child.world env middle := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using middleCarried
  have firstStep (fuel : Nat) : DemandInstructionStep cx fuel ⟨point, frame, state⟩ middle := by
    apply DemandInstructionStep.definition addressSite.instruction
    simp only [execOp, execPure, pure_apply]
  refine ⟨owned, coverage, ?_⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨length, current, rfl, actual, tail⟩
  · exact .interior ⟨.address canonical addressSite coverage ⟨⟨_, atPoint, related⟩, child.frame, childCarried⟩, Or.inl ⟨_, _, addressSite.instruction⟩⟩
  · obtain ⟨actualFuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
    have same := actualStep.deterministic (firstStep actualFuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, boundary, rfl, cleared, residual⟩
    · have site := GeneratedDemandInstruction.clear_auto occurrence rows addressPost.pp extended
      exact .interior ⟨.clear canonical site coverage
        addressPost placeResult ⟨⟨_, addressPost.pp, addressPost.rel⟩, placeResult.frame, middleChildCarried⟩,
        Or.inr ⟨_, site.instruction⟩⟩
    · obtain ⟨_, _, _, _, _, _, _, evaluated, post, result, finalBounded, demanded⟩ :=
        accepted_generated_clear_runtime_step source occurrence rows coverage admitted bounded realized placed addressPost extended cleared
      have prepared : (execStmt 2 cfg env (.clear (.global global) origin) >>= prepareLoopFlow env loop) state =
          .ok (.normal .unit) boundary.state := by
        simp only [bind_apply, evaluated]
        cases loop <;> rfl
      exact .complete (by omega) (.next actual (.next cleared (.zero _))) residual prepared
        (.normal post result finalBounded demanded.operands)

end Goose.Lower
