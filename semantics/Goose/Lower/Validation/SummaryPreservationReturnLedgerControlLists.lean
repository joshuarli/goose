import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlActions

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

structure StatementReturnCheckpoint (loop : Option LoopCtx) (statements : List Stmt) (env : LEnv)
    (initial : LS) (values : List ValueId) (origin : Option OriginId) where
  preceding : List Stmt
  statement : Stmt
  following : List Stmt
  decomposition : statements = preceding ++ statement :: following
  before : LS
  after : LS
  precedingRun : lowerStmts loop preceding env initial = ((), before)
  live : before.cur.isSome = true
  statementRun : lowerStmt loop statement env before = ((), after)
  member : .term (.ret values origin) ∈ after.insts

theorem StatementReturnCheckpoint.statement_member
    {loop : Option LoopCtx} {statements : List Stmt} {env : LEnv} {initial : LS}
    {values : List ValueId} {origin : Option OriginId}
    (checkpoint : StatementReturnCheckpoint loop statements env initial values origin) :
    checkpoint.statement ∈ statements := by
  exact (congrArg (fun list : List Stmt => checkpoint.statement ∈ list) checkpoint.decomposition).mpr
    (List.mem_append_right _ List.mem_cons_self)

theorem StatementReturnCheckpoint.roots_bounded
    {loop : Option LoopCtx} {statements : List Stmt} {env : LEnv} {initial : LS}
    {value : ValueId} {origin : Option OriginId} {target : List RootRef} {upper finalUpper : Prov}
    {scopeCount : Nat} (checkpoint : StatementReturnCheckpoint loop statements env initial [value] origin)
    (ledger : BuilderReturnsBound upper target checkpoint.after)
    (symbols : checkpoint.after.SymbolWF env scopeCount)
    (size : upper.vals.size = checkpoint.after.vals.size)
    (retained : ∀ index, index < upper.vals.size → rootsAt finalUpper.vals index = rootsAt upper.vals index) :
    ∀ root ∈ rootsAt finalUpper.vals value, root ∈ target := by
  have bound := (symbols.instructions _ checkpoint.member).uses value (by simp [Inst.uses, Term.uses])
  intro root member
  rw [retained value (by simpa only [size] using bound)] at member
  exact ledger value origin checkpoint.member root member

namespace ReturnLedgerControl

theorem statements_origin {loop : Option LoopCtx} {statements : List Stmt} {env : LEnv}
    {initial final : LS} {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (run : lowerStmts loop statements env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨
      Nonempty (StatementReturnCheckpoint loop statements env initial values origin) := by
  induction statements generalizing initial final with
  | nil =>
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact Or.inl member
  | cons statement rest ih =>
    cases current : initial.cur with
    | none =>
      have stopped : lowerStmts loop (statement :: rest) env initial = ((), initial) := by
        simp only [lowerStmts, bind_run, isLive_none current, Bool.false_eq_true, ite_false, pure_run]
      rw [stopped] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      exact Or.inl member
    | some block =>
      have executing : lowerStmts loop (statement :: rest) env initial =
          lowerStmts loop rest env (lowerStmt loop statement env initial).2 := by
        simp only [lowerStmts, bind_run, isLive_run current, ite_true]
      rw [executing] at run
      rcases ih run member with old | later
      · exact Or.inr ⟨⟨[], statement, rest, rfl, initial, (lowerStmt loop statement env initial).2,
          rfl, by simp [current], by cases (lowerStmt loop statement env initial).1; rfl, old⟩⟩
      · obtain ⟨checkpoint⟩ := later
        refine Or.inr ⟨⟨statement :: checkpoint.preceding, checkpoint.statement, checkpoint.following,
          ?_, checkpoint.before, checkpoint.after, ?_, checkpoint.live, checkpoint.statementRun, checkpoint.member⟩⟩
        · exact congrArg (List.cons statement) checkpoint.decomposition
        · simpa only [lowerStmts, bind_run, isLive_run current, ite_true] using checkpoint.precedingRun

end ReturnLedgerControl
end Goose.Lower.Validation.SummaryPreservation
