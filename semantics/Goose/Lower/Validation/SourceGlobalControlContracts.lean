import Goose.Lower.Validation.SourceGlobalReplayContracts

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def GlobalStatementReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty) (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (loop : Option LoopCtx)
    (scope : ScopeId) (statement : Stmt) (initial : LS) (upper : Prov) : Prop :=
  ∀ output start finish before after,
    Core.tyStmt typingEnv scope statement start = .ok (output, finish) →
    rpStmt env statement before = .ok ((), after) →
    EffectRefinement func after.eff target →
    SourceScopesWithin scopeCount (Core.stmtScopes none statement) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    NativeRows vt (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ∀ expected, ReturnBoundsPreserved expected initial upper
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next

def GlobalStatementsReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty) (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat) (loop : Option LoopCtx)
    (scope : ScopeId) (statements : List Stmt) (initial : LS) (upper : Prov) : Prop :=
  ∀ output start finish before after,
    Core.tyStmts typingEnv scope statements start = .ok (output, finish) →
    rpStmts env statements before = .ok ((), after) →
    EffectRefinement func after.eff target →
    SourceScopesWithin scopeCount (Core.stmtsScopes none statements) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    NativeRows vt (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ∀ expected, ReturnBoundsPreserved expected initial upper
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next


end Goose.Lower.Validation.SummaryPreservation
