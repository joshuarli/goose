import Goose.Lower.DemandIfNestedStoppedFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive NestedIfElseStatementPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | condition {condition : Expr} {yes no : Core.Block} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.ifS condition yes (some no) origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env condition state)
      (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (demanded : CanonicalExpressionDemand map cx child runtime) :
      NestedIfElseStatementPrefixCursor cx results selected source before built initial start map required runtime
  | fork {condition : Expr} {yes no : Core.Block} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.ifS condition yes (some no) origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env condition state) (boolean : Bool) (fuel : Nat)
      (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (evaluated : evalExpr fuel cfg env condition state = .ok (.bool boolean) runtime.state)
      (boundary : GeneratedExpressionPrefixEnd child map cx before initial
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool boolean) runtime) :
      NestedIfElseStatementPrefixCursor cx results selected source before built initial start map required runtime
  | branch {condition : Expr} {yes no : Core.Block} {origin : OriginId} {state middle : St}
      {source : StmtSource cfg env (.ifS condition yes (some no) origin) state} {before built branchStart : LS}
      {initial conditionFrame : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env condition state) (boolean : Bool) (fuel : Nat)
      (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
      (evaluated : evalExpr fuel cfg env condition state = .ok (.bool boolean) middle)
      (branch : BlockSource cfg env [] (if boolean then yes else no) middle)
      (demanded : GeneratedGenericBlockPrefixDemand branch selected map required branchStart none conditionFrame
        (@IfMixedStatementCursor cfg { env with scopes := ((if boolean then yes else no).scope, middle.nextScope) :: env.scopes } cx results root owner selected)
        (GeneratedClearBlockDemand branch map required cx results branchStart none conditionFrame) runtime) :
      NestedIfElseStatementPrefixCursor cx results selected source before built initial start map required runtime
  | join {condition : Expr} {yes no : Core.Block} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.ifS condition yes (some no) origin) state} {before built : LS}
      {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (joinBlock : BlockId) (fuel : Nat)
      (evaluated : execStmt fuel cfg env (.ifS condition yes (some no) origin) state = .ok (.normal .unit) runtime.state)
      (step : ∀ targetFuel, DemandInstructionStep cx targetFuel runtime ⟨(joinBlock, 0), runtime.frame, runtime.state⟩)
      (post : GeneratedStatementPrefixEnd source map cx before initial built none (.normal .unit)
        ⟨(joinBlock, 0), runtime.frame, runtime.state⟩) :
      NestedIfElseStatementPrefixCursor cx results selected source before built initial start map required runtime



theorem accepted_generated_nested_if_some_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (yesFragment : ∀ state : St, IfMixedStatements cfg
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noFragment : ∀ state : St, IfMixedStatements cfg
      { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
    (yesNoValue : yes.value = none) (noNoValue : no.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected none condition (@CanonicalExpressionPrefixCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin)
      (@NestedIfElseStatementPrefixCursor cfg env cx results root owner selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  refine ⟨owned, coverage, ?_⟩
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_prefix source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps
  cases progress with
  | interior demanded => exact .interior (.condition child canonical demanded)
  | @complete fuel consumed remaining current value count executed residual evaluated boundary =>
    have typed := (child.result fuel value evaluated).typed
    rw [childType] at typed
    obtain ⟨boolean, rfl⟩ := hasTy_bool typed
    have lowered : lowerStmt none (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before =
        ((), (lowerStmt none (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before).2) := by
      generalize run : lowerStmt none (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before = output
      cases output with
      | mk returned builder => cases returned; rfl
    obtain ⟨yesBlock, noBlock, forked, yesStart, yesEnd, noStart, noEnd, yesValue, noValue, yesEndPoint, noEndPoint,
      forkRun, yesStartEq, yesRun, yesCurrent, noStartEq, noRun, noCurrent, joined, forkExtended, yesExtended, noExtended⟩ :=
      generated_if_some_fork lowered boundary.post.pp extended
    have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool boolean)) (by simp)
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, first, suffix⟩
    · exact .interior (.fork child boolean fuel canonical evaluated boundary)
    · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
      have equal := actual.deterministic (generated_if_branch_step (state := current.state) boolean forkRun boundary.post.pp forkExtended cell stepFuel)
      have nextEq : next = ⟨(if boolean then yesBlock else noBlock, 0), current.frame, current.state⟩ := by
        cases next
        exact equal
      subst next
      have branchForm : IfMixedStatements cfg
          { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes }
          (if boolean then yes else no).stmts := by
        cases boolean <;> first | exact noFragment current.state | exact yesFragment current.state
      have branchNoValue : (if boolean then yes else no).value = none := by cases boolean <;> assumption
      have bodyFamily : GeneratedSequencePrefixFamily
          (env := { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes })
          cx results selected (if boolean then yesStart else noStart) none [] false (if boolean then yes else no)
          (if boolean then yes else no).stmts
          (@IfMixedStatementCursor cfg { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes } cx results root owner selected) :=
        (accepted_generated_if_mixed_statements
          (env := { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes })
          selected (if boolean then yesStart else noStart) [] false (if boolean then yes else no) branchForm).1
      have branchProgress := accepted_generated_if_generic_selected_prefix source child canonical boolean evaluated selected owned occurrence rows
        coverage admitted input boundary forkRun forkExtended yesStartEq yesRun yesCurrent yesExtended noStartEq noRun noCurrent noExtended
        joined extended _ bodyFamily (fun done => branchForm.normal done) branchNoValue suffix
      rcases branchProgress with ⟨branch, demanded⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, joinStep, finalPost⟩
      · exact .interior (.branch child boolean fuel canonical evaluated branch demanded)
      · rcases branchResidual.uncons with ⟨_, rfl⟩ | ⟨rest', next', restCount', last, afterJoin⟩
        · exact .interior (.join noEnd.blocks.size sourceFuel sourceDone joinStep finalPost)
        · obtain ⟨lastFuel, actualLast⟩ := runtimeStep_demandInstructionStep last
          have equalLast := actualLast.deterministic (joinStep lastFuel)
          have nextEq : next' = ⟨(noEnd.blocks.size, 0), final.frame, final.state⟩ := by cases next'; exact equalLast
          subst next'
          apply DemandPrefixDecomposition.complete (sourceFuel := sourceFuel) (value := .normal .unit)
            (consumed := consumed + (branchCount + 1) + 1) (remaining := rest')
            (boundary := ⟨(noEnd.blocks.size, 0), final.frame, final.state⟩)
          · omega
          · exact (executed.append (.next first branchExecuted)).append (.next last (.zero _))
          · exact afterJoin
          · simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, pure_apply]
          · exact finalPost


#print axioms accepted_generated_nested_if_some_prefix_family
end Goose.Lower
