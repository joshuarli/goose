import Goose.Lower.DemandStoppedStatementFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

inductive StoppedSequencePrefix {cfg : Cfg} {env : Env} {statements : List Stmt} {state : St}
    (source : StmtsSource cfg env statements state) (map : RetainedSsaMap) (cx : FnCtx) (results : List Ty)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (block : Core.Block)
    (initial : GIR.Frame) (start : Pt) (taken : Nat) (reached : DemandRuntimePoint) (stop : Stop) (after : St) : Prop
  | aborted (fuel : Nat) (evaluated : (execStmts fuel cfg env statements >>= prepareLoopFlow env loop) state = .stop stop after) :
      StoppedSequencePrefix source map cx results before loop bindings block initial start taken reached stop after
  | complete {fuel consumed remaining : Nat} {boundary : DemandRuntimePoint} {flow : Flow}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (evaluated : (execStmts fuel cfg env statements >>= prepareLoopFlow env loop) state = .ok flow boundary.state)
      (post : GeneratedSequencePrefixEnd source map cx
        (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 initial
        (lowerStmts loop statements (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 loop flow boundary) :
      StoppedSequencePrefix source map cx results before loop bindings block initial start taken reached stop after

def GeneratedStoppedSequencePrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) (statements : List Stmt) : Prop :=
  ∀ {state : St} (source : StmtsSource cfg env statements state)
    (_owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before),
    source.all = block.stmts → source.scope = block.scope → source.value = block.value →
    ∀ {required map : RetainedSsaMap} (_rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required),
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
    ∀ {fuel : Nat} {stop : Stop} {after : St}, DemandInstructionStop cx fuel reached stop after → stop ≠ .timeout →
    StoppedSequencePrefix source map cx results before loop bindings block initial start taken reached stop after

theorem prepared_sequence_cons_stopped_head {cfg : Cfg} {env : Env} {statement : Stmt} {rest : List Stmt}
    {loop : Option LoopCtx} {state after : St} {fuel : Nat} {stop : Stop}
    (head : (execStmt fuel cfg env statement >>= prepareLoopFlow env loop) state = .stop stop after) :
    (execStmts (fuel + 1) cfg env (statement :: rest) >>= prepareLoopFlow env loop) state = .stop stop after := by
  simp only [bind_apply] at head
  cases headRun : execStmt fuel cfg env statement state with
  | stop reason final => simp only [headRun, Res.stop.injEq] at head; obtain ⟨rfl, rfl⟩ := head; simp [execStmts, bind_apply, headRun]
  | ok flow middle =>
    simp only [headRun] at head
    cases flow with
    | normal value =>
      have normal : prepareLoopFlow env loop (.normal value) middle = .ok (.normal value) middle := by cases loop <;> rfl
      rw [normal] at head
      cases head
    | ret value | brk | cont =>
      simp only [execStmts, bind_apply, headRun]
      exact head

theorem prepared_sequence_cons_stopped_tail {cfg : Cfg} {env : Env} {statement : Stmt} {rest : List Stmt}
    {loop : Option LoopCtx} {state middle after : St} {headFuel tailFuel : Nat} {stop : Stop}
    (head : execStmt headFuel cfg env statement state = .ok (.normal .unit) middle)
    (tail : (execStmts tailFuel cfg env rest >>= prepareLoopFlow env loop) middle = .stop stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ fuel, (execStmts fuel cfg env (statement :: rest) >>= prepareLoopFlow env loop) state = .stop stop after := by
  let common := max headFuel tailFuel
  have headRaised := ((monoAll headFuel common (Nat.le_max_left _ _)).stmt cfg env statement state).1 _ _ head
  have monotone : MonoM (execStmts tailFuel cfg env rest >>= prepareLoopFlow env loop)
      (execStmts common cfg env rest >>= prepareLoopFlow env loop) :=
    MonoM.bind ((monoAll tailFuel common (Nat.le_max_right _ _)).stmts cfg env rest) (fun _ => MonoM.refl _)
  have tailRaised : (execStmts common cfg env rest >>= prepareLoopFlow env loop) middle = .stop stop after := by
    rcases (monotone middle).2 _ _ tail with timeout | result
    · have notTimeout : Goose.Proofs.Fuel.isTimeout stop = false := by
        cases stop with
        | timeout => exact (nonTimeout rfl).elim
        | abort | exit | fault => rfl
      rw [notTimeout] at timeout
      cases timeout
    · exact result
  refine ⟨common + 1, ?_⟩
  simp only [execStmts, bind_apply, headRaised]
  exact tailRaised

theorem accepted_generated_stopped_sequence_nil {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block) :
    GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block [] := by
  intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps fuel stop after stopped nonTimeout
  have raw : execStmts 1 cfg env [] state = .ok (.normal .unit) state := by simp only [execStmts, pure_apply]
  have evaluated : (execStmts 1 cfg env [] >>= prepareLoopFlow env loop) state = .ok (.normal .unit) state := by
    simp only [bind_apply, raw]
    cases loop <;> rfl
  exact .complete (consumed := 0) (by omega) (.zero _) steps evaluated
    (.normal (Post.init input.related input.atPoint) (source.result 1 (.normal .unit) raw) bounded realized)

theorem accepted_generated_stopped_sequence_cons {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    {statement : Stmt} {rest : List Stmt}
    (headFamily : GeneratedStoppedStatementPrefixFamily cx results selected loop statement)
    (tailFamily : GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block rest) :
    GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block (statement :: rest) := by
  intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
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
  have headProgress := headFamily head headOwner headOccurrence headRows coverage headAdmitted bounded headRealized headInput headExtended steps stopped nonTimeout
  cases headProgress with
  | aborted fuel done =>
    exact .aborted (fuel + 1) (prepared_sequence_cons_stopped_head done)
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
        (by rw [tailBuilder]; exact headBounded) tailCarried tailInput (by rw [tailBuilder]; exact restExtended) residual stopped nonTimeout
      cases tailProgress with
      | aborted fuel done =>
        obtain ⟨sourceFuel, sourceDone⟩ := prepared_sequence_cons_stopped_tail headRaw done nonTimeout
        exact .aborted sourceFuel sourceDone
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

inductive StoppedExpressionStatements : List Stmt → Prop
  | nil : StoppedExpressionStatements []
  | expression {expression : Expr} (origin : OriginId) (form : ReadStoppedExpression expression)
      {rest : List Stmt} (tail : StoppedExpressionStatements rest) : StoppedExpressionStatements (.expr expression origin :: rest)

theorem accepted_generated_expression_statements_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : StoppedExpressionStatements statements) :
    GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block statements := by
  induction fragment with
  | nil => exact accepted_generated_stopped_sequence_nil selected before loop bindings want block
  | @expression expression origin form rest tail ih =>
    have head : GeneratedStoppedStatementPrefixFamily cx results selected loop (.expr expression origin) := by
      intro state
      exact accepted_generated_expression_statement_stopped_family selected loop expression origin
        (accepted_generated_read_stopped_expressions selected loop form)
    intro state
    exact accepted_generated_stopped_sequence_cons selected before loop bindings want block head ih

#print axioms accepted_generated_expression_statements_stopped
#print axioms accepted_generated_stopped_sequence_cons

#print axioms prepared_sequence_cons_stopped_head
#print axioms prepared_sequence_cons_stopped_tail

end Goose.Lower
