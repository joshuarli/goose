import Goose.Lower.DemandAssignmentSequence
import Goose.Lower.DemandCarried

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_literal_assignments_carried_traversal {cfg : Cfg} {env : Env} {state : St}
    {stmts : List Stmt} (fragment : LiteralAssignmentStatements stmts)
    (source : StmtsSource cfg env stmts state)
    {cx : FnCtx} {ls ls' : LS} {pt : Pt} {frame : GIR.Frame} {loop : Option LoopCtx}
    {results : List Ty} (map : RetainedSsaMap)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (bounded : map.Bounded ls.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨pt, frame, state⟩)
    (lowered : lowerStmts loop stmts (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (point : ls.pp = some pt) (extended : ExtT ls' cx.fn.blocks)
    (related : Rel cfg env cx frame ls) :
    ∃ (after : St) (finalPoint : Pt) (finalFrame : GIR.Frame),
      DemandUniformTraversal cx
        (fun runtime => LiteralAssignmentSequenceDemand cfg env cx runtime ∧
          map.Realizes cfg.mod source.world env runtime) (stmts.length * 3)
        ⟨pt, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      ls'.pp = some finalPoint ∧ Rel cfg env cx finalFrame ls' := by
  induction fragment generalizing state ls ls' pt frame with
  | nil =>
    simp only [lowerStmts, pure_run] at lowered
    obtain ⟨_, rfl⟩ := Prod.mk.inj lowered
    refine ⟨state, pt, frame, ?_, point, related⟩
    apply DemandUniformTraversal.done
    exact ⟨Or.inr ⟨state, source, ⟨⟨ls, point, related⟩, source.frame,
      by constructor <;> simp⟩⟩, realized⟩
  | @cons rest varId type number origin fragment induction =>
    obtain ⟨block, current, _, _⟩ := LS.pp_some point
    simp only [lowerStmts, bind_eq] at lowered
    obtain ⟨live, initial, checkedLive, lowered⟩ := lowered
    rw [isLive_run current] at checkedLive
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj checkedLive
    simp only [ite_true, bind_eq] at lowered
    obtain ⟨result, middle, headLowered, tailLowered⟩ := lowered
    have resultEq : result = () := Subsingleton.elim _ _
    subst result
    have middleExtended := extended.of_adv (advB_lowerStmts loop rest _ _ _ _ tailLowered)
    obtain ⟨head, _, _, headWorld, headRetained, next⟩ := source.splitDemand
    have headAdmitted : map.Admitted cfg.mod.profile head.context.retained :=
      fun shrink alias member => headRetained alias (admitted shrink alias member)
    have headRealized : map.Realizes cfg.mod head.world env ⟨pt, frame, state⟩ := by
      simpa only [headWorld] using realized
    obtain ⟨afterHead, address, value, alias, middlePoint, middleFrame,
      headDone, headTraversal, _, middlePointAt, middleRelated⟩ :=
      accepted_literal_assignment_carried_traversal head map headAdmitted bounded headRealized
        headLowered point middleExtended related
    obtain ⟨tail, _, _, _, tailWorld, tailRetained⟩ := next 2 .unit afterHead headDone
    have tailAdmitted : map.Admitted cfg.mod.profile tail.context.retained := by
      simpa only [tailRetained] using admitted
    have tailBounded : map.Bounded middle.vals.size :=
      bounded.mono (advB_lowerStmt loop _ _ _ _ _ headLowered).vals
    have tailRealized : map.Realizes cfg.mod tail.world env ⟨middlePoint, middleFrame, afterHead⟩ := by
      simpa only [tailWorld, headWorld] using headTraversal.last_valid.2
    obtain ⟨after, finalPoint, finalFrame, tailTraversal, finalPointAt, finalRelated⟩ :=
      induction tail tailAdmitted tailBounded tailRealized tailLowered middlePointAt extended middleRelated
    have first : DemandUniformTraversal cx
        (fun runtime => LiteralAssignmentSequenceDemand cfg env cx runtime ∧
          map.Realizes cfg.mod source.world env runtime) 3
        ⟨pt, frame, state⟩ ⟨middlePoint, middleFrame, afterHead⟩ :=
      headTraversal.mono (fun runtime valid => by
        have query : head.rootsEnv.access.aliasPlace (head.path ++ [0]) (.var varId) = .ok [alias] := by
          obtain ⟨stage, _, _, query, _⟩ := valid.1
          exact query
        exact ⟨Or.inl ⟨state, varId, type, number, origin, head, pt, address, alias, valid.1,
          literalAssignmentRhsContext.inputFuture head,
          fun shrink => literalAssignmentRhsContext.retains head shrink query⟩,
          by simpa only [headWorld] using valid.2⟩)
    have remaining : DemandUniformTraversal cx
        (fun runtime => LiteralAssignmentSequenceDemand cfg env cx runtime ∧
          map.Realizes cfg.mod source.world env runtime) (rest.length * 3)
        ⟨middlePoint, middleFrame, afterHead⟩ ⟨finalPoint, finalFrame, after⟩ := tailTraversal.mono (fun runtime valid =>
      ⟨valid.1, by simpa only [tailWorld] using valid.2⟩)
    refine ⟨after, finalPoint, finalFrame, ?_, finalPointAt, finalRelated⟩
    simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      first.append remaining

theorem accepted_literal_assignments_carried_prefix_invariant {cfg : Cfg} {env : Env} {state : St}
    {stmts : List Stmt} (fragment : LiteralAssignmentStatements stmts)
    (source : StmtsSource cfg env stmts state)
    {cx : FnCtx} {ls ls' : LS} {pt : Pt} {frame : GIR.Frame} {loop : Option LoopCtx}
    {results : List Ty} (map : RetainedSsaMap)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (bounded : map.Bounded ls.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨pt, frame, state⟩)
    (lowered : lowerStmts loop stmts (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (point : ls.pp = some pt) (extended : ExtT ls' cx.fn.blocks)
    (related : Rel cfg env cx frame ls) :
    ∀ (taken fuel : Nat) (reached : DemandRuntimePoint), taken ≤ stmts.length * 3 →
      DemandLinearPrefix cx taken fuel ⟨pt, frame, state⟩ reached →
      LiteralAssignmentSequenceDemand cfg env cx reached ∧ map.Realizes cfg.mod source.world env reached := by
  obtain ⟨after, finalPoint, finalFrame, traversal, _, _⟩ :=
    accepted_literal_assignments_carried_traversal fragment source map admitted bounded realized
      lowered point extended related
  intro taken fuel reached bounded steps
  exact traversal.prefix_invariant bounded steps

end Goose.Lower
