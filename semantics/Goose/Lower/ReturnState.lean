import Goose.Lower.Unwind
import Goose.Lower.Scope
import Goose.Lower.RuntimeSim

namespace Goose.Lower

open Goose.Core Goose.GIR

def prepareReturn (env : Env) : Flow → M Flow
  | .ret value => do
    releaseScopes env env.scopes
    pure (.ret value)
  | flow => pure flow

theorem prepareReturn_no_scopes (env : Env) (hscopes : env.scopes = []) :
    prepareReturn env = fun flow => pure flow := by
  funext flow
  cases flow <;> simp [prepareReturn, hscopes, releaseScopes, pure_bind]

structure ReturnSite (cx : FnCtx) (pt : Pt) (frame : GIR.Frame) (value : Val)
    (org : OriginId) : Prop where
  instruction : ∃ ids, instAt cx.fn pt = some (.term (.ret ids (some org))) ∧
    ((ids = [] ∧ value = .unit) ∨ ∃ id, ids = [id] ∧ frame.vals[id]? = some (.val value))
  scopes : frame.scopes = []

theorem ReturnSite.run {cx : FnCtx} {pt : Pt} {frame : GIR.Frame} {value : Val} {org : OriginId}
    (h : ReturnSite cx pt frame value org) (state : St) :
    ∀ extra, runAt cx pt frame (extra + 1) state = .ok value state := by
  intro extra
  obtain ⟨ids, hinst, hvalue⟩ := h.instruction
  rcases hvalue with ⟨rfl, rfl⟩ | ⟨id, rfl, hcell⟩
  · rw [runAt_ret0 hinst extra]
    rfl
  · rw [runAt_ret1 hinst hcell extra]
    rfl


def preparedCoreBlock (n : Nat) (cfg : Cfg) (env : Env) (scope : ScopeId)
    (stmts : List Stmt) (value : Option Expr) (pre : List (VarId × Val)) : M Flow := do
  let scopeInstance ← freshScope
  let inner : Env := { env with scopes := (scope, scopeInstance) :: env.scopes }
  bindAll env.act scopeInstance pre
  let flow ← execStmts n cfg inner stmts >>= prepareReturn inner
  match flow with
  | .ret value => pure (.ret value)
  | flow => do
    let result ← valueFlow n cfg value inner flow
    Core.releaseScope env scope scopeInstance
    pure result

theorem prepareReturn_execBlock (n : Nat) (cfg : Cfg) (env : Env) (scope : ScopeId)
    (stmts : List Stmt) (value : Option Expr) (pre : List (VarId × Val)) :
    (execBlock (n + 1) cfg env pre (.mk scope stmts value) >>= prepareReturn env) =
      preparedCoreBlock n cfg env scope stmts value pre := by
  rw [execBlock_pre]
  unfold prefixCoreBlock preparedCoreBlock
  simp only [bind_assoc]
  congr 1
  funext scopeInstance
  congr 1
  funext initialized
  congr 1
  funext flow
  cases flow with
  | normal v =>
    cases value <;> simp [valueFlow, prepareReturn, bind_assoc, pure_bind]
  | brk => simp [valueFlow, prepareReturn, bind_assoc, pure_bind]
  | cont => simp [valueFlow, prepareReturn, bind_assoc, pure_bind]
  | ret v => simp [valueFlow, prepareReturn, bind_assoc, pure_bind, releaseScopes_entered]


end Goose.Lower
