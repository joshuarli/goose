import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsGlobal

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedExpressionsOccurrence (expressions : List Expr)
    (step : ∀ expression ∈ expressions, ∀ state provenance,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets
        expression state provenance) :
    ∀ initial upper, ExpressionsOccurrenceReplayAt typingEnv env results vt target scopeCount
      siteRoot siteTargets anchor expressions initial upper := by
  exact typedGlobalExpressionsOccurrence expressions step

theorem typedExpressionsAsOccurrence (expressions : List Expr)
    (step : ∀ expression ∈ expressions, ∀ state provenance,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets
        expression state provenance)
    (initial : LS) (upper : Prov) (anchored : ∃ path, DemandNodeAt siteRoot path anchor)
    (paths : ∀ expression ∈ expressions, ∃ path, DemandNodeAt anchor path (.expression expression))
    (element : Ty) (start finish : Nat) (before after : RState)
    (typed : tyExprsAs typingEnv element expressions start = .ok ((), finish)) :
    rpExprs env expressions before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper →
    ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
    NativeRows vt (lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl)
      (lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl)
      (lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1,
          value < (lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
          OperandOccurrence env anchor (lowerContextAt env.mod env.ctx env.impl) next value) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env anchor (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
        (lowerContextAt env.mod env.ctx env.impl) vt next :=
  typedExpressionsOccurrence expressions step initial upper anchored paths
    (List.replicate expressions.length element) start finish before after (tyExprsAs_structExprs typed)

end Goose.Lower.Validation.ReplacementContentFlowSource
