import Goose.Lower.Validation.SourceGlobalReplayContracts

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def GlobalExpressionReplayTrackedAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty) (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (expression : Expr) (initial : LS) (upper : Prov) : Prop :=
  ∀ type start finish before after sourceRoots,
    tyExpr typingEnv expression start = .ok (type, finish) →
    rpExpr env expression before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    GeneratedBuilderState initial →
    NativeRows vt (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ReplayValue func next
          (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2
          (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ∀ expected, ReturnBoundsPreserved expected initial upper
        (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next

theorem globalExpressionReplay_tracked {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {target : Core.Eff} {scopeCount : Nat} {expression : Expr} {initial : LS} {upper : Prov}
    (replay : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression initial upper) :
    GlobalExpressionReplayTrackedAt typingEnv env results vt func returnTypes slots target scopeCount expression initial upper := by
  intro type start finish before after roots source replayed ceiling ready generated native
  obtain ⟨next, completed, value, retained⟩ := replay type start finish before after roots source replayed ceiling ready generated native
  exact ⟨next, completed, value, retained, fun expected => ready.global_expression_returns expected source retained⟩

#print axioms globalExpressionReplay_tracked

end Goose.Lower.Validation.SummaryPreservation
