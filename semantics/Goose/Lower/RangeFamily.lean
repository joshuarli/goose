import Goose.Lower.RangeStatements
import Goose.Lower.TypedExpressionFamily

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem prepareLoopFlow_stmtRange (n : Nat) (cfg : Cfg) (env : Env) (x : VarId)
    (lo hi : Expr) (body : Core.Block) (origin : OriginId) (loop : Option LoopCtx) :
    (execStmt n cfg env (.forRange x lo hi body origin) >>= prepareLoopFlow env loop) =
      (execStmt n cfg env (.forRange x lo hi body origin) >>= prepareReturn env) := by
  cases n with
  | zero =>
    funext state
    simp [execStmt, GIR.bind_apply, timeout, M.stop]
  | succ n =>
    simp only [execStmt, bind_assoc]
    congr 1
    funext lower
    congr 1
    funext low
    obtain ⟨ty, start⟩ := low
    congr 1
    funext upper
    congr 1
    funext high
    obtain ⟨upperTy, bound⟩ := high
    congr 1
    funext same
    exact prepareLoopFlow_execRange n cfg env x ty start bound body loop

theorem typedStatementLoopSimulation_range {n : Nat} {cfg : Cfg} {results : List Ty}
    {x : VarId} {lo hi : Expr} {body : Core.Block} {origin : OriginId}
    (lowerSimulation : TypedExprClaim n cfg results lo)
    (upperSimulation : TypedExprClaim n cfg results hi)
    (blocks : ∀ fuel, fuel < n + 1 → ∀ loop pre pre',
      TypedBlockLoopSimulation fuel cfg results (some loop) pre pre' false body)
    (loop : Option LoopCtx) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.forRange x lo hi body origin) := by
  intro env state source metadata lexical input output result point cx frame lowered atPoint
    extension related module returned depth targets counter
  cases result
  rw [prepareLoopFlow_stmtRange]
  have simulation := stmt_range_checked_flow_sim_at source results metadata lowerSimulation upperSimulation
    blocks cx module returned loop input output frame point lowered atPoint extension related
  exact simulation.mono fun flow _ pt' fr' _ post =>
    post.elim (fun normal => Or.inl normal) (fun returned => Or.inr (Or.inl returned))

end Goose.Lower
