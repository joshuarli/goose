import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsGlobalLeaves
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalWhole

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS} {typingEnv : TEnv} {env : PEnv}
  {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem canonical_globalExpressionOccurrence_literal (integer : IntTy) (value : Int) :
    CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      (.lit integer value) initial upper := by
  intro rooted cursor type start finish before after roots typed replay ceiling ready sites targetBounds generated native metadata continuation
  have shape : type = .int integer := by
    simp only [Core.tyExpr] at typed
    split at typed
    · exact congrArg Prod.fst ((st_pure_ok _ _ _).mp typed)
    · exact ((rej_ok _ _ _ _).mp typed).elim
  subst type
  have sameRoots : roots = [] := congrArg Prod.fst ((st_pure_ok _ _ _).mp replay)
  subst roots
  obtain ⟨next, nextReady, returned, retained⟩ := ready.emitTypedDef (.constInt integer value) [] (.data (.int integer))
    (by simp [Op.uses]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty _ target) (fun _ member => by cases member) (fun _ => rfl)
  refine ⟨next, nextReady, returned, retained, ?_⟩
  have oldSites := sites.toOld
  have oldResult := OccurrenceLedger.emitDef_sites (root := .expression (.lit integer value))
    (EmitsOnly.refl _ initial) oldSites ready nextReady rfl retained
    (by
      intro _ operand member
      simp [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member)
    (by intro address same; cases same)
    (by intro callee arguments org same; cases same)
    (by
      intro _ operand member
      simp [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member)
  have growth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize, nextReady.roots.valueSize]
    exact (advB_emitDef (.constInt integer value) (lowerEnv env.mod env.impl.vars returnTypes) initial _ _ rfl).vals
  exact ⟨oldResult.1, sites.emitDef rfl growth retained⟩

theorem canonical_globalExpressionOccurrence_boolean (value : Bool) :
    CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      (.bool value) initial upper := by
  intro rooted cursor type start finish before after roots typed replay ceiling ready sites targetBounds generated native metadata continuation
  have shape : type = .bool := congrArg Prod.fst ((st_pure_ok _ _ _).mp typed)
  subst type
  have sameRoots : roots = [] := congrArg Prod.fst ((st_pure_ok _ _ _).mp replay)
  subst roots
  obtain ⟨next, nextReady, returned, retained⟩ := ready.emitTypedDef (.constBool value) [] (.data .bool)
    (by simp [Op.uses]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty _ target) (fun _ member => by cases member) (fun _ => rfl)
  refine ⟨next, nextReady, returned, retained, ?_⟩
  have oldSites := sites.toOld
  have oldResult := OccurrenceLedger.emitDef_sites (root := .expression (.bool value))
    (EmitsOnly.refl _ initial) oldSites ready nextReady rfl retained
    (by
      intro _ operand member
      simp [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member)
    (by intro address same; cases same)
    (by intro callee arguments org same; cases same)
    (by
      intro _ operand member
      simp [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member)
  have growth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize, nextReady.roots.valueSize]
    exact (advB_emitDef (.constBool value) (lowerEnv env.mod env.impl.vars returnTypes) initial _ _ rfl).vals
  exact ⟨oldResult.1, sites.emitDef rfl growth retained⟩

#print axioms canonical_globalExpressionOccurrence_literal
#print axioms canonical_globalExpressionOccurrence_boolean

end Goose.Lower.Validation.SourceReplacementWriterLedger
