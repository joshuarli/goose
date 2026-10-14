import Goose.Lower.LoopFlow

namespace Goose.Lower

open Goose.Core Goose.GIR

def LoopDepthFits (env : Env) : Option LoopCtx → Prop
  | none => True
  | some loop => loop.depth ≤ env.scopes.length

def prepareLoopFlow (env : Env) (loop : Option LoopCtx) (flow : Flow) : M Flow := do
  let flow ← prepareReturn env flow
  match loop with
  | none => pure flow
  | some context => prepareLoopExit env context.depth flow

theorem prepareLoopFlow_none (env : Env) : prepareLoopFlow env none = prepareReturn env := by
  funext flow
  simp [prepareLoopFlow, bind_pure]

theorem prepareLoopFlow_normal_success {env : Env} {loop : Option LoopCtx}
    {flow : Flow} {value : Val} {before after : St}
    (h : prepareLoopFlow env loop flow before = .ok (.normal value) after) :
    flow = .normal value ∧ after = before := by
  cases flow with
  | normal returned =>
    cases loop <;>
      simp only [prepareLoopFlow, prepareReturn, prepareLoopExit, pure_bind, pure_apply,
        Res.ok.injEq, Flow.normal.injEq] at h <;>
      exact ⟨congrArg Flow.normal h.1, h.2.symm⟩
  | ret returned =>
    obtain ⟨middle, hrelease, _, _⟩ := releaseScopes_result env env.scopes before
    cases loop <;> simp only [prepareLoopFlow, prepareReturn, prepareLoopExit,
      bind_apply, hrelease, pure_apply] at h <;> cases h
  | brk | cont =>
    cases loop with
    | none => simp only [prepareLoopFlow, prepareReturn, pure_bind, pure_apply] at h; cases h
    | some context =>
      obtain ⟨middle, hrelease, _, _⟩ := releaseScopes_result env
        (env.scopes.take (env.scopes.length - context.depth)) before
      simp only [prepareLoopFlow, prepareReturn, prepareLoopExit, pure_bind,
        bind_apply, hrelease, pure_apply] at h
      cases h

theorem preparedLoopFlow_normal_success {env : Env} {loop : Option LoopCtx}
    {source : M Flow} {value : Val} {before after : St}
    (h : (source >>= prepareLoopFlow env loop) before = .ok (.normal value) after) :
    source before = .ok (.normal value) after := by
  rw [bind_apply] at h
  cases hsource : source before with
  | stop reason state => rw [hsource] at h; cases h
  | ok flow state =>
    rw [hsource] at h
    obtain ⟨rfl, rfl⟩ := prepareLoopFlow_normal_success h
    rfl

def loopStmtsTail (n : Nat) (cfg : Cfg) (env : Env) (loop : Option LoopCtx)
    (rest : List Stmt) : Flow → M Flow
  | .normal _ => execStmts n cfg env rest >>= prepareLoopFlow env loop
  | flow => pure flow

theorem prepareLoopFlow_execStmts (n : Nat) (cfg : Cfg) (env : Env) (loop : Option LoopCtx)
    (stmt : Stmt) (rest : List Stmt) :
    (execStmts (n + 1) cfg env (stmt :: rest) >>= prepareLoopFlow env loop) =
      ((execStmt n cfg env stmt >>= prepareLoopFlow env loop) >>=
        loopStmtsTail n cfg env loop rest) := by
  simp only [execStmts, bind_assoc]
  congr 1
  funext flow
  cases flow <;> cases loop <;>
    simp [prepareLoopFlow, prepareReturn, prepareLoopExit, loopStmtsTail, bind_assoc, pure_bind]

theorem releaseScopes_prefix_entered (env : Env) (scope : ScopeId) (scopeInstance : ScopeInst)
    (depth : Nat) (hdepth : depth ≤ env.scopes.length) :
    releaseScopes { env with scopes := (scope, scopeInstance) :: env.scopes }
        (((scope, scopeInstance) :: env.scopes).take
          (((scope, scopeInstance) :: env.scopes).length - depth)) =
      (Core.releaseScope env scope scopeInstance >>= fun _ =>
        releaseScopes env (env.scopes.take (env.scopes.length - depth))) := by
  have hlength : ((scope, scopeInstance) :: env.scopes).length - depth =
      (env.scopes.length - depth) + 1 := by simp only [List.length_cons]; omega
  rw [hlength, List.take_succ_cons]
  simp only [releaseScopes]
  rw [releaseScope_same_activation (env := { env with scopes := (scope, scopeInstance) :: env.scopes })
    (env' := env) rfl rfl]
  rw [releaseScopes_same_activation (env := { env with scopes := (scope, scopeInstance) :: env.scopes })
    (env' := env) rfl rfl]

def preparedCoreLoopBlock (n : Nat) (cfg : Cfg) (env : Env) (loop : Option LoopCtx)
    (scope : ScopeId) (stmts : List Stmt) (value : Option Expr) (pre : List (VarId × Val)) : M Flow := do
  let scopeInstance ← freshScope
  let inner : Env := { env with scopes := (scope, scopeInstance) :: env.scopes }
  bindAll env.act scopeInstance pre
  let flow ← execStmts n cfg inner stmts >>= prepareLoopFlow inner loop
  match flow with
  | .ret value => pure (.ret value)
  | .brk | .cont =>
    match loop with
    | some _ => pure flow
    | none => do
      Core.releaseScope env scope scopeInstance
      pure flow
  | .normal returned => do
    let result ← valueFlow n cfg value inner (.normal returned)
    Core.releaseScope env scope scopeInstance
    pure result

theorem prepareLoopFlow_execBlock (n : Nat) (cfg : Cfg) (env : Env) (loop : Option LoopCtx)
    (scope : ScopeId) (stmts : List Stmt) (value : Option Expr) (pre : List (VarId × Val))
    (hdepth : LoopDepthFits env loop) :
    (execBlock (n + 1) cfg env pre (.mk scope stmts value) >>= prepareLoopFlow env loop) =
      preparedCoreLoopBlock n cfg env loop scope stmts value pre := by
  rw [execBlock_pre]
  unfold prefixCoreBlock preparedCoreLoopBlock
  simp only [bind_assoc]
  congr 1
  funext scopeInstance
  congr 1
  funext initialized
  congr 1
  funext flow
  cases flow with
  | normal v =>
    cases value <;> cases loop <;>
      simp [valueFlow, prepareLoopFlow, prepareReturn, prepareLoopExit, bind_assoc, pure_bind]
  | ret v =>
    cases loop <;> simp [valueFlow, prepareLoopFlow, prepareReturn, prepareLoopExit,
      bind_assoc, pure_bind, releaseScopes_entered]
  | brk | cont =>
    cases loop with
    | none => simp [valueFlow, prepareLoopFlow, prepareReturn, prepareLoopExit, bind_assoc, pure_bind]
    | some context =>
      simp only [LoopDepthFits] at hdepth
      simp only [valueFlow, prepareLoopFlow, prepareReturn, prepareLoopExit, bind_assoc, pure_bind]
      rw [releaseScopes_prefix_entered env scope scopeInstance context.depth hdepth]
      simp only [bind_assoc]

end Goose.Lower
