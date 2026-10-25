import Goose.Lower.DemandAssignmentMetadata

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive LiteralAssignmentStatements : List Stmt → Prop
  | nil : LiteralAssignmentStatements []
  | cons {rest : List Stmt} (varId : VarId) (type : IntTy) (number : Int) (origin : OriginId)
      (tail : LiteralAssignmentStatements rest) :
      LiteralAssignmentStatements (.assign (.var varId) (.lit type number) origin :: rest)

def LiteralAssignmentSequenceDemand (cfg : Cfg) (env : Env) (cx : FnCtx)
    (point : DemandRuntimePoint) : Prop :=
  (∃ (state : St) (varId : VarId) (type : IntTy) (number : Int) (origin : OriginId)
      (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state)
      (start : Pt) (address : ValueId) (alias : RetainedAlias),
    LiteralAssignmentDemand source cx address alias start point ∧
      (literalAssignmentRhsContext source).inputFuture = source.context.outputFuture ∧
      (cfg.mod.profile = .shrink → alias ∈ (literalAssignmentRhsContext source).retained)) ∨
  (∃ (state : St) (source : StmtsSource cfg env [] state),
    DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
      (blockSuffixFuture source.context source.offset) [] [] point)

theorem accepted_literal_assignments_demand_traversal {cfg : Cfg} {env : Env} {state : St}
    {stmts : List Stmt} (fragment : LiteralAssignmentStatements stmts)
    (source : StmtsSource cfg env stmts state)
    {cx : FnCtx} {ls ls' : LS} {pt : Pt} {frame : GIR.Frame} {loop : Option LoopCtx}
    {results : List Ty}
    (lowered : lowerStmts loop stmts (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (point : ls.pp = some pt) (extended : ExtT ls' cx.fn.blocks)
    (related : Rel cfg env cx frame ls) :
    ∃ (after : St) (finalPoint : Pt) (finalFrame : GIR.Frame),
      DemandUniformTraversal cx (LiteralAssignmentSequenceDemand cfg env cx) (stmts.length * 3)
        ⟨pt, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      ls'.pp = some finalPoint ∧ Rel cfg env cx finalFrame ls' := by
  induction fragment generalizing state ls ls' pt frame with
  | nil =>
    simp only [lowerStmts, pure_run] at lowered
    obtain ⟨_, rfl⟩ := Prod.mk.inj lowered
    refine ⟨state, pt, frame, ?_, point, related⟩
    apply DemandUniformTraversal.done
    exact Or.inr ⟨state, source, ⟨⟨ls, point, related⟩, source.frame, by constructor <;> simp⟩⟩
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
    obtain ⟨head, _, _, next⟩ := source.split
    obtain ⟨afterHead, address, value, alias, middlePoint, middleFrame,
      headDone, _, _, headTraversal, _, middlePointAt, middleRelated⟩ :=
      accepted_literal_assignment_demand_traversal head headLowered point middleExtended related
    obtain ⟨tail, _, _, _⟩ := next 2 .unit afterHead headDone
    obtain ⟨after, finalPoint, finalFrame, tailTraversal, finalPointAt, finalRelated⟩ :=
      induction tail tailLowered middlePointAt extended middleRelated
    have first : DemandUniformTraversal cx (LiteralAssignmentSequenceDemand cfg env cx) 3
        ⟨pt, frame, state⟩ ⟨middlePoint, middleFrame, afterHead⟩ :=
      headTraversal.mono (fun point valid => by
        have query : head.rootsEnv.access.aliasPlace (head.path ++ [0]) (.var varId) = .ok [alias] := by
          obtain ⟨stage, _, _, query, _⟩ := valid
          exact query
        exact Or.inl ⟨state, varId, type, number, origin, head, pt, address, alias, valid,
          literalAssignmentRhsContext.inputFuture head,
          fun shrink => literalAssignmentRhsContext.retains head shrink query⟩)
    refine ⟨after, finalPoint, finalFrame, ?_, finalPointAt, finalRelated⟩
    simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      first.append tailTraversal

theorem accepted_literal_assignments_prefix_invariant {cfg : Cfg} {env : Env} {state : St}
    {stmts : List Stmt} (fragment : LiteralAssignmentStatements stmts)
    (source : StmtsSource cfg env stmts state)
    {cx : FnCtx} {ls ls' : LS} {pt : Pt} {frame : GIR.Frame} {loop : Option LoopCtx}
    {results : List Ty}
    (lowered : lowerStmts loop stmts (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (point : ls.pp = some pt) (extended : ExtT ls' cx.fn.blocks)
    (related : Rel cfg env cx frame ls) :
    ∀ (taken fuel : Nat) (reached : DemandRuntimePoint), taken ≤ stmts.length * 3 →
      DemandLinearPrefix cx taken fuel ⟨pt, frame, state⟩ reached →
      LiteralAssignmentSequenceDemand cfg env cx reached := by
  obtain ⟨after, finalPoint, finalFrame, traversal, _, _⟩ :=
    accepted_literal_assignments_demand_traversal fragment source lowered point extended related
  intro taken fuel reached bounded steps
  exact traversal.prefix_invariant bounded steps

end Goose.Lower
