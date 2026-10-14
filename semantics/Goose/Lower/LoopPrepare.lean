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

theorem prepareLoopFlow_at_depth (env : Env) (loop : LoopCtx)
    (hdepth : loop.depth = env.scopes.length) :
    prepareLoopFlow env (some loop) = prepareReturn env := by
  funext flow
  cases flow <;>
    simp [prepareLoopFlow, prepareReturn, prepareLoopExit, hdepth, releaseScopes,
      bind_assoc, pure_bind]

theorem execWhile_success_flow (fuel : Nat) (cfg : Cfg) (env : Env) (cond : Expr)
    (body : Core.Block) : ∀ (state after : St) (flow : Flow),
    execWhile fuel cfg env cond body state = .ok flow after →
      flow = .normal .unit ∨ ∃ value, flow = .ret value := by
  induction fuel with
  | zero => intro state after flow done; simp [execWhile, Core.timeout, M.stop] at done
  | succ fuel ih =>
    intro state after flow done
    simp only [execWhile, bind_apply] at done
    cases hcond : evalExpr fuel cfg env cond state with
    | stop reason middle => rw [hcond] at done; cases done
    | ok value middle =>
      simp only [hcond] at done
      cases hbool : expectBool value middle with
      | stop reason ready => rw [hbool] at done; cases done
      | ok branch ready =>
        simp only [hbool] at done
        cases branch with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, pure_apply] at done
          exact Or.inl (Res.ok.inj done).1.symm
        | true =>
          simp only [↓reduceIte, bind_apply] at done
          cases hbody : execBlock fuel cfg env [] body ready with
          | stop reason finished => rw [hbody] at done; cases done
          | ok result finished =>
            simp only [hbody] at done
            cases result with
            | normal value => exact ih finished after flow done
            | cont => exact ih finished after flow done
            | brk => exact Or.inl (Res.ok.inj done).1.symm
            | ret value => exact Or.inr ⟨value, (Res.ok.inj done).1.symm⟩

theorem prepareLoopFlow_execWhile (fuel : Nat) (cfg : Cfg) (env : Env) (loop : Option LoopCtx)
    (cond : Expr) (body : Core.Block) :
    (execWhile fuel cfg env cond body >>= prepareLoopFlow env loop) =
      (execWhile fuel cfg env cond body >>= prepareReturn env) := by
  funext state
  simp only [bind_apply]
  cases done : execWhile fuel cfg env cond body state with
  | stop reason after => rfl
  | ok flow after =>
    rcases execWhile_success_flow fuel cfg env cond body state after flow done with rfl | ⟨value, rfl⟩
    · cases loop <;> simp [prepareLoopFlow, prepareReturn, prepareLoopExit, pure_bind]
    · cases loop <;> simp [prepareLoopFlow, prepareReturn, prepareLoopExit, bind_assoc, pure_bind]

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

theorem prepareLoopFlow_execStmt_break (n : Nat) (cfg : Cfg) (env : Env) (loop : LoopCtx)
    (org : OriginId) :
    (execStmt n cfg env (.brk org) >>= prepareLoopFlow env (some loop)) =
      (execStmt n cfg env (.brk org) >>= prepareLoopExit env loop.depth) := by
  cases n with
  | zero => simp only [execStmt]; rfl
  | succ n => simp only [execStmt, pure_bind, prepareLoopFlow, prepareReturn]

theorem prepareLoopFlow_execStmt_continue (n : Nat) (cfg : Cfg) (env : Env) (loop : LoopCtx)
    (org : OriginId) :
    (execStmt n cfg env (.cont org) >>= prepareLoopFlow env (some loop)) =
      (execStmt n cfg env (.cont org) >>= prepareLoopExit env loop.depth) := by
  cases n with
  | zero => simp only [execStmt]; rfl
  | succ n => simp only [execStmt, pure_bind, prepareLoopFlow, prepareReturn]

theorem prepareLoopFlow_execStmt_return_none (n : Nat) (cfg : Cfg) (env : Env)
    (loop : Option LoopCtx) (org : OriginId) :
    (execStmt n cfg env (.ret none org) >>= prepareLoopFlow env loop) =
      (execStmt n cfg env (.ret none org) >>= prepareReturn env) := by
  cases n with
  | zero => simp only [execStmt]; rfl
  | succ n =>
    cases loop <;> simp [execStmt, prepareLoopFlow, prepareReturn, prepareLoopExit,
      bind_assoc, pure_bind]

theorem prepareLoopFlow_unitFlow (env : Env) (loop : Option LoopCtx) (flow : Flow) :
    prepareLoopFlow env loop (unitFlow flow) =
      (prepareLoopFlow env loop flow >>= fun prepared => pure (unitFlow prepared)) := by
  cases flow <;> cases loop <;>
    simp [unitFlow, prepareLoopFlow, prepareReturn, prepareLoopExit, bind_assoc, pure_bind]

def preparedLoopIf (n : Nat) (cfg : Cfg) (env : Env) (loop : Option LoopCtx)
    (cond : Expr) (thenBlock : Core.Block) (elseBlock : Option Core.Block) : M Flow := do
  let branch ← expectBool (← evalExpr n cfg env cond)
  let flow ← if branch then execBlock n cfg env [] thenBlock >>= prepareLoopFlow env loop
    else match elseBlock with
      | some block => execBlock n cfg env [] block >>= prepareLoopFlow env loop
      | none => pure (.normal .unit)
  pure (unitFlow flow)

theorem prepareLoopFlow_execStmt_if (n : Nat) (cfg : Cfg) (env : Env) (loop : Option LoopCtx)
    (cond : Expr) (thenBlock : Core.Block) (elseBlock : Option Core.Block) (org : OriginId) :
    (execStmt (n + 1) cfg env (.ifS cond thenBlock elseBlock org) >>= prepareLoopFlow env loop) =
      preparedLoopIf n cfg env loop cond thenBlock elseBlock := by
  simp only [execStmt, preparedLoopIf, bind_assoc]
  congr 1
  funext value
  congr 1
  funext branch
  cases branch <;> cases elseBlock <;>
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, unitFlow, prepareLoopFlow,
      prepareReturn, bind_assoc]
  · cases loop <;> simp only [prepareLoopExit, pure_bind]
  all_goals
    congr 1
    funext flow
    cases flow <;> cases loop <;>
      simp [prepareLoopFlow, prepareReturn, prepareLoopExit, unitFlow, bind_assoc, pure_bind]

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
