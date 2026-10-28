import Goose.Lower.DemandCallRows
import Goose.Lower.DemandControlProgressCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_call_first_value_prefix {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {expression : Expr} {rest : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context (.byVal expression :: rest) origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context (.byVal expression :: rest) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context (.byVal expression :: rest) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (form : ControlPrefixExpression expression)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ child : ExprSource cfg env expression state,
      source.ChildAt child 0 (by simp [DemandNode.child?, DemandNode.children]) ∧
      DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env expression)
        (GeneratedControlProgressCursor cx child before
          (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 initial start map required)
        (GeneratedExpressionPrefixEnd child map cx before initial
          (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2
          (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).1)
        taken ⟨start, initial, state⟩ reached := by
  obtain ⟨sources, metadata, canonical⟩ := source.callArgsCanonical 0 results input.metadata
  cases sources with
  | cons head tail =>
    cases head with
    | byVal child =>
      obtain ⟨found, childCanonical, tailCanonical⟩ := canonical
      have childAt := ArgSource.byVal_callChild source found child childCanonical
      obtain ⟨typing, roots⟩ := ArgSource.byVal_callMetadata source found child childCanonical
      have childOwner : GeneratedSourceOwner selected child.context :=
        (owned.child rfl 0 (.expression expression) .expression (by simp [DemandNode.child?, DemandNode.children]) (by trivial)).transport
          childAt.plans.symm childAt.path.symm rfl childAt.context.symm
      have argumentOccurrence := GeneratedDemandOccurrence.argument occurrence (index := 0) (argument := .byVal expression) rfl
      have tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0
          ((.byVal expression :: rest).take 0)
          (lowerArgs ((.byVal expression :: rest).take 0) (lowerEnv cfg.mod env.vars results) before).1 [] := by
        simpa [lowerArgs, pure_run] using (GeneratedCallArgumentRows.nil (access := source.rootsEnv.access) (path := source.path) 0)
      have argumentRows := GeneratedDemandRows.argument rows (index := 0) (argument := .byVal expression) (argumentAt := rfl) tracked
      have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root child.path (.expression expression) before := by
        rw [childAt.path]
        simpa [List.take_zero, lowerArgs, pure_run] using GeneratedDemandOccurrence.argumentValue argumentOccurrence
      have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
        have inherited := GeneratedDemandRows.argumentValue argumentRows
        simpa [roots, childAt.path, List.take_zero, lowerArgs, pure_run] using inherited
      have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
        intro profile alias member
        exact childAt.retained alias (admitted profile alias member)
      have childRealized : map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
        simpa only [childAt.world] using realized
      have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv before initial start := by
        simpa only [typing, roots] using input
      let le := lowerEnv cfg.mod env.vars results
      obtain ⟨ids, middle, after, argsRun, definition, tail⟩ := lowerExpr_call_split
        (show lowerExpr (.call context (.byVal expression :: rest) origin) le before =
          ((lowerExpr (.call context (.byVal expression :: rest) origin) le before).1,
            (lowerExpr (.call context (.byVal expression :: rest) origin) le before).2) from rfl)
      have afterExtended : ExtT after cx.fn.blocks := by
        rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
        · exact extended.of_adv (adv_emitTerm term)
        · exact extended
      have middleExtended := afterExtended.of_adv (adv_emitDef definition)
      simp only [lowerArgs, bind_eq] at argsRun
      obtain ⟨id, childBuilt, headRun, tailIds, afterArgs, tailRun, finish⟩ := argsRun
      rw [pure_run] at finish
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj finish
      have childExtended : ExtT (lowerExpr expression le before).2 cx.fn.blocks := by
        have headExt := middleExtended.of_adv (advB_lowerArgs rest _ _ _ _ tailRun)
        have loweredHead : lowerExpr expression le before = (id, childBuilt) := by simpa [lowerArg] using headRun
        rw [loweredHead]
        exact headExt
      have family : GeneratedExpressionPrefixFamily cx results selected loop expression
          (@GeneratedControlProgressCursor cfg env cx) := accepted_generated_control_progress_prefix_family selected loop form
      have progress := family child childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput childExtended steps
      exact ⟨child, childAt, progress.progress⟩

#print axioms accepted_generated_call_first_value_prefix
end Goose.Lower
