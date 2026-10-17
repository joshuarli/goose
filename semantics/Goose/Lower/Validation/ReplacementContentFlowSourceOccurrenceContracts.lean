import Goose.Lower.Validation.ReplacementContentFlowSourceNativeContinuation
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites
import Goose.Lower.Validation.SummaryPreservationReplayTypedPlacesContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

def ExpressionOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (expression : Expr) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.expression expression)) →
  ∀ type start finish before after sourceRoots,
    tyExpr typingEnv expression start = .ok (type, finish) →
    rpExpr env expression before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.expression expression)
        (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerExpr expression (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def PlaceOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (place : Place) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.place place)) →
  ∀ info start finish before after sourceRoots,
    tyPlace typingEnv place start = .ok (info, finish) →
    rpPlace env place before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 <
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
        GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl)
          (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) sourceRoots) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.place place)
        (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

def ViewOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (view : View) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path (.view view)) →
  ∀ info start finish before after sourceRoots,
    tyView typingEnv view start = .ok (info, finish) →
    rpView env view before = .ok (sourceRoots, after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 sourceRoots (.view .readOnly info.1)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.view view)
        (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next

end Goose.Lower.Validation.ReplacementContentFlowSource
