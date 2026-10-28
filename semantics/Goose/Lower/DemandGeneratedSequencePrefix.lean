import Goose.Lower.DemandGeneratedStatementPrefix
import Goose.Proofs.Fuel

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

inductive GeneratedSequencePrefixCursor {cfg : Cfg} {env : Env}
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (map required : RetainedSsaMap) (cx : FnCtx) (results : List Ty) (before : LS)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (block : Core.Block) :
    {root : DemandNode} → {owner : Nat} →
    GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner →
    {statements : List Stmt} → {state : St} → StmtsSource cfg env statements state →
      DemandRuntimePoint → DemandRuntimePoint → Prop
  | head {root : DemandNode} {owner : Nat}
      {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {statement : Stmt} {rest : List Stmt} {state : St}
      {source : StmtsSource cfg env (statement :: rest) state} {head : StmtSource cfg env statement state}
      {initial : GIR.Frame} {start : Pt} {runtime : DemandRuntimePoint}
      (canonical : source.CanonicalHead head)
      (owned : GeneratedSourceOwner selected head.context)
      (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root head.path
        (.statement loop statement) (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2)
      (rows : GeneratedDemandRows cfg.mod head.rootsEnv.access occurrence required)
      (coverage : map.Covers required)
      (demanded : cursor head
        (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2
        (lowerStmt loop statement (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2
        initial start map required runtime) :
      @GeneratedSequencePrefixCursor cfg env (@cursor) map required cx results before loop bindings block root owner selected _ _ source
        ⟨start, initial, state⟩ runtime
  | tail {root : DemandNode} {owner : Nat}
      {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
      {statement : Stmt} {rest : List Stmt} {state : St}
      {source : StmtsSource cfg env (statement :: rest) state} {boundary runtime : DemandRuntimePoint}
      {next : StmtsSource cfg env rest boundary.state} {fuel consumed : Nat} {initial : GIR.Frame} {start : Pt}
      (canonical : source.CanonicalTail next)
      (evaluated : execStmt fuel cfg env statement state = .ok (.normal .unit) boundary.state)
      (prefixSteps : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary)
      (post : Post cfg env cx
        (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 initial
        (lowerStmt loop statement (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2
        boundary.frame boundary.point [])
      (demanded : @GeneratedSequencePrefixCursor cfg env (@cursor) map required cx results before loop bindings block root owner selected _ _ next boundary runtime) :
      @GeneratedSequencePrefixCursor cfg env (@cursor) map required cx results before loop bindings block root owner selected _ _ source
        ⟨start, initial, state⟩ runtime

inductive GeneratedSequencePrefixEnd {cfg : Cfg} {env : Env} {statements : List Stmt} {state : St}
    (source : StmtsSource cfg env statements state) (map : RetainedSsaMap) (cx : FnCtx)
    (before : LS) (initial : GIR.Frame) (built : LS) (loop : Option LoopCtx) : Flow → DemandRuntimePoint → Prop
  | normal {runtime : DemandRuntimePoint}
      (post : Post cfg env cx before initial built runtime.frame runtime.point [])
      (result : StmtsResult source (.normal .unit) runtime.state)
      (bounded : map.Bounded built.vals.size)
      (realized : map.Realizes cfg.mod source.world env runtime) :
      GeneratedSequencePrefixEnd source map cx before initial built loop (.normal .unit) runtime
  | transfer {runtime : DemandRuntimePoint} {flow : Flow}
      (abnormal : ∀ value, flow ≠ .normal value)
      (post : StatementLoopPost cfg env cx before initial built loop flow runtime.point runtime.frame) :
      GeneratedSequencePrefixEnd source map cx before initial built loop flow runtime

structure GeneratedSequencePrefixDecomposition {cfg : Cfg} {env : Env} {statements : List Stmt} {state : St}
    (source : StmtsSource cfg env statements state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS} {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)}
    {want : Bool} {block : Core.Block}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (map : RetainedSsaMap) (initial : GIR.Frame) (start : Pt)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (taken : Nat) (reached : DemandRuntimePoint) : Prop where
  sourceOwner : GeneratedSourceOwner selected source.context
  coverage : map.Covers required
  progress : DemandPrefixDecomposition cx
    (fun fuel => execStmts fuel cfg env statements >>= prepareLoopFlow env loop)
    (@GeneratedSequencePrefixCursor cfg env (@cursor) map required cx results before loop bindings block root owner selected _ _ source ⟨start, initial, state⟩)
    (GeneratedSequencePrefixEnd source map cx
      (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 initial
      (lowerStmts loop statements (lowerEnv cfg.mod env.vars results)
        (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 loop)
    taken ⟨start, initial, state⟩ reached

def GeneratedSequencePrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) (statements : List Stmt)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) : Prop :=
  ∀ {state : St} (source : StmtsSource cfg env statements state)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before),
    source.all = block.stmts → source.scope = block.scope → source.value = block.value →
    ∀ {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required),
    map.Covers required → map.Admitted cfg.mod.profile source.context.retained →
    map.Bounded (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2.vals.size →
    ∀ {initial : GIR.Frame} {start : Pt}, map.Realizes cfg.mod source.world env ⟨start, initial, state⟩ →
    GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 initial start →
    ExtT (lowerStmts loop statements (lowerEnv cfg.mod env.vars results)
      (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 cx.fn.blocks →
    ∀ {taken : Nat} {reached : DemandRuntimePoint}, DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached →
    GeneratedSequencePrefixDecomposition source selected occurrence rows map initial start (@cursor) taken reached

theorem prepared_sequence_cons_normal {cfg : Cfg} {env : Env} {statement : Stmt} {rest : List Stmt}
    {loop : Option LoopCtx} {state middle after : St} {headFuel tailFuel : Nat} {flow : Flow}
    (head : execStmt headFuel cfg env statement state = .ok (.normal .unit) middle)
    (tail : (execStmts tailFuel cfg env rest >>= prepareLoopFlow env loop) middle = .ok flow after) :
    ∃ fuel, (execStmts fuel cfg env (statement :: rest) >>= prepareLoopFlow env loop) state = .ok flow after := by
  simp only [bind_apply] at tail
  cases tailRun : execStmts tailFuel cfg env rest middle with
  | stop stop final => simp only [tailRun] at tail; cases tail
  | ok rawFlow rawState =>
    simp only [tailRun] at tail
    let common := max headFuel tailFuel
    have headRaised := ((monoAll headFuel common (Nat.le_max_left _ _)).stmt cfg env statement state).1 _ _ head
    have tailRaised := ((monoAll tailFuel common (Nat.le_max_right _ _)).stmts cfg env rest middle).1 _ _ tailRun
    refine ⟨common + 1, ?_⟩
    simp only [execStmts, bind_apply, headRaised, tailRaised]
    exact tail

theorem prepared_sequence_cons_transfer {cfg : Cfg} {env : Env} {statement : Stmt} {rest : List Stmt}
    {loop : Option LoopCtx} {state after : St} {fuel : Nat} {flow : Flow}
    (abnormal : ∀ value, flow ≠ .normal value)
    (head : (execStmt fuel cfg env statement >>= prepareLoopFlow env loop) state = .ok flow after) :
    (execStmts (fuel + 1) cfg env (statement :: rest) >>= prepareLoopFlow env loop) state = .ok flow after := by
  simp only [bind_apply] at head
  cases headRun : execStmt fuel cfg env statement state with
  | stop stop final => simp only [headRun] at head; cases head
  | ok rawFlow rawState =>
    simp only [headRun] at head
    cases rawFlow with
    | normal value =>
      have normal : prepareLoopFlow env loop (.normal value) rawState = .ok (.normal value) rawState := by cases loop <;> rfl
      rw [normal] at head
      obtain ⟨rfl, _⟩ := Res.ok.inj head
      exact (abnormal value rfl).elim
    | ret value | brk | cont =>
      simp only [execStmts, bind_apply, headRun]
      exact head

theorem transfer_after_builder {cfg : Cfg} {env : Env} {cx : FnCtx} {before first second : LS}
    {initial frame : GIR.Frame} {point : Pt} {loop : Option LoopCtx} {flow : Flow}
    (abnormal : ∀ value, flow ≠ .normal value)
    (post : StatementLoopPost cfg env cx before initial first loop flow point frame) :
    StatementLoopPost cfg env cx before initial second loop flow point frame := by
  rcases post with ⟨normal, _⟩ | returned | transferred
  · exact (abnormal .unit normal).elim
  · exact Or.inr (Or.inl returned)
  · exact Or.inr (Or.inr transferred)

theorem accepted_generated_sequence_prefix_nil {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block [] (@cursor) := by
  intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps
  have raw : execStmts 1 cfg env [] state = .ok (.normal .unit) state := by simp only [execStmts, pure_apply]
  have evaluated : (execStmts 1 cfg env [] >>= prepareLoopFlow env loop) state = .ok (.normal .unit) state := by
    simp only [bind_apply, raw]
    cases loop <;> rfl
  exact ⟨owned, coverage, .complete (consumed := 0) (by omega) (.zero _) steps evaluated
    (.normal (Post.init input.related input.atPoint) (source.result 1 (.normal .unit) raw) bounded realized)⟩

theorem accepted_generated_sequence_prefix_cons {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    {statement : Stmt} {rest : List Stmt}
    (headFamily : GeneratedStatementPrefixFamily cx results selected loop statement (@cursor))
    (tailFamily : GeneratedSequencePrefixFamily cx results selected before loop bindings want block rest (@cursor)) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block (statement :: rest) (@cursor) := by
  intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps
  obtain ⟨head, canonical, _, headTyping, headRoots, headOccurrence, headRows, _, headAdmitted, _, nextSource⟩ :=
    accepted_generated_statement_entry source occurrence all scope value rows coverage admitted input.atPoint input.related realized
  have headOwner : GeneratedSourceOwner selected head.context :=
    (owned.child rfl source.offset (.statement statement) .statement canonical.found (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have headRealized : map.Realizes cfg.mod head.world env ⟨start, initial, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  have headInput : GeneratedPrefixInput cfg env cx results loop head.typingEnv head.rootsEnv
      (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 initial start := by
    rw [headTyping, headRoots]
    exact input
  obtain ⟨currentBlock, current, _, _⟩ := LS.pp_some input.atPoint
  have lowerRun : (lowerStmts loop (statement :: rest) (lowerEnv cfg.mod env.vars results)
      (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 =
      (lowerStmts loop rest (lowerEnv cfg.mod env.vars results)
        (lowerStmt loop statement (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2).2 := by
    simp only [lowerStmts, bind_run, isLive_run current, ite_true]
  have restExtended := extended
  rw [lowerRun] at restExtended
  have headExtended := restExtended.of_adv (advB_lowerStmts loop rest _ _ _ _ rfl)
  have headProgress := headFamily head headOwner headOccurrence headRows coverage headAdmitted bounded headRealized headInput headExtended steps
  refine ⟨owned, coverage, ?_⟩
  cases headProgress.progress with
  | interior demanded =>
    exact .interior (.head canonical headOwner headOccurrence headRows coverage demanded)
  | @complete headFuel headConsumed headRemaining boundary flow count prefixSteps residual evaluated finished =>
    cases finished with
    | transfer abnormal post =>
      exact .complete count prefixSteps residual (prepared_sequence_cons_transfer abnormal evaluated)
        (.transfer abnormal (transfer_after_builder abnormal post))
    | normal headPost headResult headBounded headCarried =>
      have headRaw := preparedLoopFlow_normal_success evaluated
      obtain ⟨tail, tailTyping, tailRoots, _, tailCanonical⟩ := nextSource headFuel .unit boundary.state headRaw
      have tailOwner : GeneratedSourceOwner selected tail.context :=
        owned.transport tailCanonical.plans.symm tailCanonical.path.symm
          (by rw [tailCanonical.scope, tailCanonical.all, tailCanonical.value]) tailCanonical.context.symm
      have tailOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root tail.path (.block loop bindings want block) before := by rw [tailCanonical.path]; exact occurrence
      have tailRows : GeneratedDemandRows cfg.mod tail.rootsEnv.access tailOccurrence required := by
        simpa only [tailRoots, tailCanonical.path] using rows
      have tailAdmitted : map.Admitted cfg.mod.profile tail.context.retained := by rw [tailCanonical.retained]; exact admitted
      have tailBuilder : (lowerStmts loop (block.stmts.take tail.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 =
          (lowerStmt loop statement (lowerEnv cfg.mod env.vars results)
            (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
              (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 := by
        rw [tailCanonical.offset]
        have suffix : statement :: rest = block.stmts.drop source.offset := by simpa only [all] using source.suffix
        have first : (block.stmts.drop source.offset)[0]? = some statement := by rw [← suffix]; rfl
        have selectedAt : block.stmts[source.offset]? = some statement := by
          simpa only [List.getElem?_drop, Nat.add_zero] using first
        exact generated_statement_prefix_next selectedAt input.atPoint
      have tailInput : GeneratedPrefixInput cfg env cx results loop tail.typingEnv tail.rootsEnv
          (lowerStmts loop (block.stmts.take tail.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 boundary.frame boundary.point := by
        rw [tailBuilder]
        refine ⟨?_, ?_, headPost.pp, headPost.rel, input.moduleEq, input.resultsEq, input.depth,
          (by cases loop <;> exact input.targets), input.counter.afterPost headPost,
          input.generated.lowerStmt loop statement input.frames.toTargets rfl,
          input.frames.mono (advB_lowerStmt loop statement _ _ _ _ rfl).ext⟩
        · apply input.metadata.transport
          · rw [tailTyping, headResult.same.impl, headTyping]
          · rw [tailRoots]
        · apply input.loops.transport
          rw [tailTyping, headResult.same.loops, headTyping]
      have tailCarried : map.Realizes cfg.mod tail.world env boundary := by
        simpa only [RetainedSsaMap.Realizes, tailCanonical.world, canonical.world] using headCarried
      have tailProgress := tailFamily tail tailOwner tailOccurrence (tailCanonical.all.trans all)
        (tailCanonical.scope.trans scope) (tailCanonical.value.trans value) tailRows coverage tailAdmitted
        (by rw [tailBuilder]; exact headBounded) tailCarried tailInput (by rw [tailBuilder]; exact restExtended) residual
      cases tailProgress.progress with
      | interior demanded =>
        exact .interior (.tail tailCanonical headRaw prefixSteps headPost demanded)
      | @complete tailFuel tailConsumed tailRemaining final flow countTail tailSteps afterPrefix tailDone tailFinished =>
        obtain ⟨sourceFuel, sourceDone⟩ := prepared_sequence_cons_normal headRaw tailDone
        cases tailFinished with
        | normal tailPost tailResult tailBounded tailRealized =>
          rw [tailBuilder] at tailPost tailBounded
          have combined : Post cfg env cx
              (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
                (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 initial
              (lowerStmts loop (statement :: rest) (lowerEnv cfg.mod env.vars results)
                (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
                  (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2
              final.frame final.point [] := by
            rw [lowerRun]
            simpa only [List.nil_append] using headPost.comp tailPost
          have finalCarried : map.Realizes cfg.mod source.world env final := by
            simpa only [RetainedSsaMap.Realizes, tailCanonical.world] using tailRealized
          exact .complete (by omega) (prefixSteps.append tailSteps) afterPrefix sourceDone
            (.normal combined (source.result sourceFuel (.normal .unit) (preparedLoopFlow_normal_success sourceDone))
              (by rw [lowerRun]; exact tailBounded) finalCarried)
        | transfer abnormal tailPost =>
          rw [tailBuilder] at tailPost
          have combined := StatementLoopPost.prefix input.related headPost input.counter tailPost
          exact .complete (by omega) (prefixSteps.append tailSteps) afterPrefix sourceDone
            (.transfer abnormal (by rw [lowerRun]; exact combined))

end Goose.Lower
