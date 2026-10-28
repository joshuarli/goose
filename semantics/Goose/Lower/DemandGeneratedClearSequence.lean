import Goose.Lower.DemandGeneratedClearTrace

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GlobalClearStatements : List Stmt → Prop
  | nil : GlobalClearStatements []
  | cons (global : GlobalId) (origin : OriginId) {rest : List Stmt}
      (remaining : GlobalClearStatements rest) : GlobalClearStatements (.clear (.global global) origin :: rest)

theorem global_clear_source {cfg : Cfg} {env : Env} {fuel : Nat} {global : GlobalId}
    {origin : OriginId} {state after : St} {flow : Flow}
    (done : execStmt fuel cfg env (.clear (.global global) origin) state = .ok flow after) :
    flow = .normal .unit ∧ truncateLoc ⟨.global global, []⟩ 0 state = .ok () after := by
  cases fuel with
  | zero => simp [execStmt, timeout, M.stop] at done
  | succ fuel =>
    cases fuel with
    | zero => simp [execStmt, evalPlace, timeout, M.stop, bind_apply] at done
    | succ fuel =>
      simp only [execStmt, evalPlace, bind_apply, pure_apply] at done
      cases truncated : truncateLoc ⟨.global global, []⟩ 0 state with
      | stop stop final => simp [truncated] at done
      | ok result final =>
        cases result
        simp only [truncated, Res.ok.injEq] at done
        rcases done with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩

theorem GlobalClearStatements.normal {statements : List Stmt} (fragment : GlobalClearStatements statements)
    {cfg : Cfg} {env : Env} {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit := by
  induction fragment generalizing fuel state after with
  | nil =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, pure_apply, Res.ok.injEq] at done
      exact done.1.symm
  | cons global origin remaining ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg env (.clear (.global global) origin) state with
      | stop stop final => simp only [head] at done; cases done
      | ok headFlow middle =>
        obtain ⟨rfl, _⟩ := global_clear_source head
        simp only [head] at done
        exact ih done

private theorem global_clear_prefix {cfg : Cfg} {env : Env} {fuel : Nat} {global : GlobalId}
    {origin : OriginId} {rest : List Stmt} {state after : St}
    (done : execStmts (fuel + 1) cfg env (.clear (.global global) origin :: rest) state = .ok (.normal .unit) after) :
    ∃ middle, execStmt fuel cfg env (.clear (.global global) origin) state = .ok (.normal .unit) middle ∧
      truncateLoc ⟨.global global, []⟩ 0 state = .ok () middle ∧
      execStmts fuel cfg env rest middle = .ok (.normal .unit) after := by
  simp only [execStmts, bind_apply] at done
  cases head : execStmt fuel cfg env (.clear (.global global) origin) state with
  | stop stop final => simp only [head] at done; cases done
  | ok flow middle =>
    obtain ⟨rfl, truncated⟩ := global_clear_source head
    simp only [head] at done
    exact ⟨middle, rfl, truncated, done⟩

inductive GeneratedClearSequenceDemand {cfg : Cfg} {env : Env}
    (map required : RetainedSsaMap) (cx : FnCtx) (results : List Ty) (before : LS)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (block : Core.Block) :
    {stmts : List Stmt} → {state : St} → StmtsSource cfg env stmts state → DemandRuntimePoint → Prop
  | done {state : St} (source : StmtsSource cfg env [] state) {point : Pt} {frame : GIR.Frame}
      (atPoint : (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2.pp = some point)
      (related : Rel cfg env cx frame (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2)
      (coverage : map.Covers required) (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩) :
      GeneratedClearSequenceDemand map required cx results before loop bindings block source ⟨point, frame, state⟩
  | head {global : GlobalId} {origin : OriginId} {rest : List Stmt} {state : St}
      {source : StmtsSource cfg env (.clear (.global global) origin :: rest) state}
      {child : StmtSource cfg env (.clear (.global global) origin) state}
      {initial : GIR.Frame} {start : Pt} {runtime : DemandRuntimePoint}
      (canonical : source.CanonicalHead child)
      (demanded : GeneratedClearDemand child map required cx
        (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2
        (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2
        (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2
        initial start (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).1 runtime) :
      GeneratedClearSequenceDemand map required cx results before loop bindings block source runtime
  | tail {global : GlobalId} {origin : OriginId} {rest : List Stmt} {state after : St}
      {source : StmtsSource cfg env (.clear (.global global) origin :: rest) state}
      {next : StmtsSource cfg env rest after} {fuel : Nat} {runtime : DemandRuntimePoint}
      (canonical : source.CanonicalTail next)
      (evaluated : execStmt fuel cfg env (.clear (.global global) origin) state = .ok (.normal .unit) after)
      (demanded : GeneratedClearSequenceDemand map required cx results before loop bindings block next runtime) :
      GeneratedClearSequenceDemand map required cx results before loop bindings block source runtime

theorem GeneratedClearSequenceDemand.frame {cfg : Cfg} {env : Env}
    {map required : RetainedSsaMap} {cx : FnCtx} {results : List Ty} {before : LS}
    {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block}
    {stmts : List Stmt} {state : St} {source : StmtsSource cfg env stmts state} {runtime : DemandRuntimePoint}
    (valid : GeneratedClearSequenceDemand map required cx results before loop bindings block source runtime) :
    ∃ typing roots future, DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime := by
  induction valid with
  | done source atPoint related coverage realized =>
    exact ⟨_, _, _, ⟨⟨_, atPoint, related⟩, source.frame, realized⟩⟩
  | head canonical demanded =>
    obtain ⟨typing, roots, future, frame⟩ := demanded.frame
    exact ⟨typing, roots, future, by simpa only [canonical.world] using frame⟩
  | tail canonical evaluated demanded induction =>
    obtain ⟨typing, roots, future, frame⟩ := induction
    exact ⟨typing, roots, future, by simpa only [canonical.world] using frame⟩

theorem GeneratedClearSequenceDemand.realizes {cfg : Cfg} {env : Env}
    {map required : RetainedSsaMap} {cx : FnCtx} {results : List Ty} {before : LS}
    {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block}
    {stmts : List Stmt} {state : St} {source : StmtsSource cfg env stmts state} {runtime : DemandRuntimePoint}
    (valid : GeneratedClearSequenceDemand map required cx results before loop bindings block source runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  induction valid with
  | done source atPoint related coverage realized => exact realized
  | head canonical demanded =>
    simpa only [RetainedSsaMap.Realizes, canonical.world] using demanded.realizes
  | tail canonical evaluated demanded induction =>
    simpa only [RetainedSsaMap.Realizes, canonical.world] using induction

theorem accepted_generated_global_clears_traversal {cfg : Cfg} {env : Env} {stmts : List Stmt}
    (fragment : GlobalClearStatements stmts) {state after : St} (source : StmtsSource cfg env stmts state)
    {fuel : Nat} (evaluated : execStmts fuel cfg env stmts state = .ok (.normal .unit) after)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    (all : source.all = block.stmts) (scope : source.scope = block.scope) (value : source.value = block.value)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2.vals.size)
    {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (atPoint : (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2.pp = some point)
    (related : Rel cfg env cx frame (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2)
    (extended : ExtT (lowerStmts loop stmts (lowerEnv cfg.mod env.vars results)
      (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 cx.fn.blocks) :
    ∃ finalPoint finalFrame,
      DemandUniformTraversal cx (GeneratedClearSequenceDemand map required cx results before loop bindings block source)
        (stmts.length * 2) ⟨point, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      Post cfg env cx
        (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 frame
        (lowerStmts loop stmts (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2
        finalFrame finalPoint [] ∧
      map.Bounded (lowerStmts loop stmts (lowerEnv cfg.mod env.vars results)
        (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2.vals.size ∧
      map.Realizes cfg.mod source.world env ⟨finalPoint, finalFrame, after⟩ := by
  induction fragment generalizing state after fuel frame point with
  | nil =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at evaluated
    | succ fuel =>
      simp only [execStmts, pure_apply, Res.ok.injEq] at evaluated
      cases evaluated.2
      exact ⟨point, frame, .done (.done source atPoint related coverage realized), Post.init related atPoint, bounded, realized⟩
  | @cons global origin rest fragment induction =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at evaluated
    | succ fuel =>
      obtain ⟨middleState, headDone, truncated, tailDone⟩ := global_clear_prefix evaluated
      obtain ⟨head, canonical, _, _, _, headOccurrence, headRows, _, headAdmitted, _, nextSource⟩ :=
        accepted_generated_statement_entry source occurrence all scope value rows coverage admitted atPoint related realized
      obtain ⟨currentBlock, current, _, _⟩ := LS.pp_some atPoint
      have lowerRun : (lowerStmts loop (.clear (.global global) origin :: rest) (lowerEnv cfg.mod env.vars results)
          (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 =
          (lowerStmts loop rest (lowerEnv cfg.mod env.vars results)
            (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results)
              (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
                (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2).2 := by
        simp only [lowerStmts, bind_run, isLive_run current, ite_true]
      have headExtended := extended
      rw [lowerRun] at headExtended
      have headExt := headExtended.of_adv (advB_lowerStmts loop rest _ _ _ _ rfl)
      have headRealized : map.Realizes cfg.mod head.world env ⟨point, frame, state⟩ := by
        simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
      obtain ⟨middlePoint, middleFrame, first, headPost, _, middleBounded, middleRealized⟩ :=
        accepted_generated_global_clear_traversal head headOccurrence headRows coverage headAdmitted bounded
          headRealized atPoint related headExt truncated
      obtain ⟨tail, _, tailRoots, _, tailCanonical⟩ := nextSource fuel .unit middleState headDone
      have tailOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root tail.path (.block loop bindings want block) before := by rw [tailCanonical.path]; exact occurrence
      have tailRows : GeneratedDemandRows cfg.mod tail.rootsEnv.access tailOccurrence required := by simpa only [tailRoots, tailCanonical.path] using rows
      have tailAdmitted : map.Admitted cfg.mod.profile tail.context.retained := by rw [tailCanonical.retained]; exact admitted
      have tailBuilder : (lowerStmts loop (block.stmts.take tail.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 =
          (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results)
            (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
              (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 := by
        rw [tailCanonical.offset]
        have suffix : .clear (.global global) origin :: rest = block.stmts.drop source.offset := by
          simpa only [all] using source.suffix
        have first : (block.stmts.drop source.offset)[0]? = some (.clear (.global global) origin) := by rw [← suffix]; rfl
        have selected : block.stmts[source.offset]? = some (.clear (.global global) origin) := by
          simpa only [List.getElem?_drop, Nat.add_zero] using first
        exact generated_statement_prefix_next selected atPoint

      have tailRealized : map.Realizes cfg.mod tail.world env ⟨middlePoint, middleFrame, middleState⟩ := by
        simpa only [RetainedSsaMap.Realizes, tailCanonical.world, canonical.world] using middleRealized
      obtain ⟨finalPoint, finalFrame, remaining, tailPost, finalBounded, finalRealized⟩ :=
        induction tail tailDone tailOccurrence (tailCanonical.all.trans all) (tailCanonical.scope.trans scope)
          (tailCanonical.value.trans value) tailRows tailAdmitted
          (by rw [tailBuilder]; exact middleBounded) tailRealized
          (by rw [tailBuilder]; exact headPost.pp) (by rw [tailBuilder]; exact headPost.rel)
          (by rw [tailBuilder]; exact headExtended)
      have firstMapped := first.mono (fun reached valid => GeneratedClearSequenceDemand.head canonical valid)
      have tailMapped := remaining.mono (fun reached valid => GeneratedClearSequenceDemand.tail tailCanonical headDone valid)
      rw [tailBuilder] at tailPost finalBounded
      refine ⟨finalPoint, finalFrame, ?_, ?_, ?_, ?_⟩
      · simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using firstMapped.append tailMapped
      · rw [lowerRun]
        simpa only [tailBuilder, List.nil_append] using headPost.comp tailPost
      · rw [lowerRun]
        exact finalBounded
      · simpa only [RetainedSsaMap.Realizes, tailCanonical.world] using finalRealized

end Goose.Lower
