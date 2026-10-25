import Goose.Lower.Validation.SummaryPreservationSourceControlKernelsBounds
import Goose.Lower.Validation.SummaryPreservationSourceScopeBounds
import Goose.Lower.Validation.SummaryPreservationReplayTypedPlacesContracts
import Goose.Lower.Validation.SummaryPreservationTypedResultBounds
import Goose.Lower.Validation.SummaryPreservationReturnTransfer

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def BlockReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (body : Core.Block) (initial : LS) (upper : Prov) : Prop :=
  ∀ type start finish before after sourceRoots range,
    Core.tyBlock typingEnv [] body start = .ok (type, finish) →
    rpBlockValue env [] body before = .ok ((sourceRoots, range), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    SourceScopesWithin scopeCount (Core.blockScopes none body) →
    (∀ binding ∈ bindings, binding.1 < env.impl.vars.size ∧ binding.2.2 < env.mod.origins.size) →
    (initial.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < initial.vals.size) →
    (∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) binding.1) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    NativeRows vt (lowerBlock loop bindings want body
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      (want = true →
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) initial upper
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next

def StatementReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (loop : Option LoopCtx)
    (scope : ScopeId) (statement : Stmt) (initial : LS) (upper : Prov) : Prop :=
  ∀ output start finish before after,
    Core.tyStmt typingEnv scope statement start = .ok (output, finish) →
    rpStmt env statement before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    SourceScopesWithin scopeCount (Core.stmtScopes none statement) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    NativeRows vt (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) initial upper
        (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next

def StatementsReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (loop : Option LoopCtx)
    (scope : ScopeId) (statements : List Stmt) (initial : LS) (upper : Prov) : Prop :=
  ∀ output start finish before after,
    Core.tyStmts typingEnv scope statements start = .ok (output, finish) →
    rpStmts env statements before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    SourceScopesWithin scopeCount (Core.stmtsScopes none statements) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    NativeRows vt (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) initial upper
        (lowerStmts loop statements (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next

end Goose.Lower.Validation.SummaryPreservation
