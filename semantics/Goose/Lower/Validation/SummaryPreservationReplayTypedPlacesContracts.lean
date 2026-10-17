import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SummaryPreservationReplayRefSlicePlace
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def ExpressionReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat)
    (expression : Expr) (initial : LS) (upper : Prov) : Prop :=
  ∀ type start finish before after sourceRoots,
    tyExpr typingEnv expression start = .ok (type, finish) →
    rpExpr env expression before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    GeneratedBuilderState initial →
    NativeRows vt (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 sourceRoots (.data type)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old

def PlaceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat)
    (place : Place) (initial : LS) (upper : Prov) : Prop :=
  ∀ info start finish before after sourceRoots,
    tyPlace typingEnv place start = .ok (info, finish) →
    rpPlace env place before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    GeneratedBuilderState initial →
    NativeRows vt (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 <
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
        RootsRefine (lowerContextAt env.mod env.ctx env.impl)
          (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) sourceRoots) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old

def ViewReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat)
    (view : View) (initial : LS) (upper : Prov) : Prop :=
  ∀ info start finish before after sourceRoots,
    tyView typingEnv view start = .ok (info, finish) →
    rpView env view before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    GeneratedBuilderState initial →
    NativeRows vt (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 sourceRoots (.view .readOnly info.1)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old

end Goose.Lower.Validation.SummaryPreservation
