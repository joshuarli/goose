import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

def CanonicalGlobalExpressionsOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS)
    (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (siteRoot : DemandNode) (siteTargets : List BlockId) (anchor : DemandNode)
    (parent : Expr) (expressions : List Expr) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path anchor) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path
    (.expression parent) initial) →
  (Fragment.expression parent).children (lowerEnv env.mod env.impl.vars returnTypes) initial =
    expressionChildren (lowerEnv env.mod env.impl.vars returnTypes) expressions initial →
  (∀ expression, expression ∈ expressions → ∃ path, DemandNodeAt anchor path (.expression expression)) →
  ∀ types start finish before after,
    tyStructExprs typingEnv types expressions start = .ok ((), finish) →
    rpExprs env expressions before = .ok ((), after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial func vt upper →
    ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
    NativeRows vt (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).1,
          value < (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
          OperandOccurrence env anchor func next value) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env anchor func vt next initial
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

def CanonicalReferenceSlicePlaceOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS)
    (typingEnv : TEnv) (env : PEnv) (context : ContextId)
    (results : Array (List RootRef)) (vt : Array (Option VTy))
    (target : Core.Eff) (scopeCount : Nat) (siteRoot : DemandNode) (siteTargets : List BlockId)
    (initial : LS) (upper : Prov) : Prop :=
  ∀ index localVar, env.impl.vars[index]? = some localVar → localVar.ty.isRefSlice = true →
    (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList)
      ownerInitial path (.place (.deref (.read (.var index)))) initial) →
    ∀ before after roots,
      rpPlace env (.deref (.read (.var index))) before = .ok (roots, after) →
      ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
        (lowerContextAt env.mod env.ctx env.impl) vt upper →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
        (lowerContextAt env.mod env.ctx env.impl)
        (lowerPlace (.deref (.read (.var index)))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
      index < env.impl.params.size ∧ env.isRefSliceVar index = true ∧
      ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
          (typedContextSlotUpper env.mod env.ctx env.impl)
          (lowerPlace (.deref (.read (.var index)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
        ((lowerPlace (.deref (.read (.var index)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
          (lowerPlace (.deref (.read (.var index)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 <
              (lowerPlace (.deref (.read (.var index)))
                (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
          GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt next.vals
            (lowerPlace (.deref (.read (.var index)))
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) roots ∧
          ((env.cont index).isSome = true → ∀ root ∈ rootsAt next.vals
            (lowerPlace (.deref (.read (.var index)))
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1,
            root ∈ [RootRef.param index]) ∧
          rootsAt next.vals (lowerPlace (.deref (.read (.var index)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 =
              lowerValueRootCeiling env #[] (.refSliceVar index)) ∧
        (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
        OccurrenceLedger env (.place (.deref (.read (.var index))))
          (lowerContextAt env.mod env.ctx env.impl) vt next initial
          (lowerPlace (.deref (.read (.var index)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
        CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
          (lowerEnv env.mod env.impl.vars env.impl.results.toList)
          (lowerPlace (.deref (.read (.var index)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
          (lowerContextAt env.mod env.ctx env.impl) vt next

def CanonicalGlobalPrintArgumentsOccurrenceReplayAt (ownerRoot : Fragment) (ownerInitial baseline : LS)
    (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (siteRoot : DemandNode) (siteTargets : List BlockId) (anchor : DemandNode)
    (loop : Option LoopCtx) (origin : OriginId) (arguments : List PrintArg)
    (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path anchor) →
  (∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path
    (.statement loop (.print arguments origin)) initial) →
  (∀ expression, .expr expression ∈ arguments → ∃ path, DemandNodeAt anchor path (.expression expression)) →
  ∀ start finish before after,
    tyPrintArgs typingEnv arguments start = .ok ((), finish) →
    rpPrintArgs env arguments before = .ok ((), after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots initial upper →
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial func vt upper →
    ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
    NativeRows vt (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots
        (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1.flatMap PrintPart.uses,
          value < (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
          OperandOccurrence env anchor func next value) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env anchor func vt next initial
        (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next

end Goose.Lower.Validation.SourceReplacementWriterLedger
