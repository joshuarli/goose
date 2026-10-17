import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsConsumed

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem globalExpressionOccurrence_literal (integer : IntTy) (value : Int) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.lit integer value) initial upper := by
  intro rooted type start finish before after roots typed replay ceiling ready sites targetBounds generated native metadata continuation
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
  apply OccurrenceLedger.emitDef_sites (EmitsOnly.refl _ initial) sites ready nextReady rfl retained
  · intro _ operand member
    simp [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member
  · intro address same; cases same
  · intro callee arguments org same; cases same
  · intro _ operand member
    simp [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member

theorem globalExpressionOccurrence_boolean (value : Bool) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.bool value) initial upper := by
  intro rooted type start finish before after roots typed replay ceiling ready sites targetBounds generated native metadata continuation
  have shape : type = .bool := congrArg Prod.fst ((st_pure_ok _ _ _).mp typed)
  subst type
  have sameRoots : roots = [] := congrArg Prod.fst ((st_pure_ok _ _ _).mp replay)
  subst roots
  obtain ⟨next, nextReady, returned, retained⟩ := ready.emitTypedDef (.constBool value) [] (.data .bool)
    (by simp [Op.uses]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty _ target) (fun _ member => by cases member) (fun _ => rfl)
  refine ⟨next, nextReady, returned, retained, ?_⟩
  apply OccurrenceLedger.emitDef_sites (EmitsOnly.refl _ initial) sites ready nextReady rfl retained
  · intro _ operand member
    simp [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member
  · intro address same; cases same
  · intro callee arguments org same; cases same
  · intro _ operand member
    simp [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member

#print axioms globalExpressionOccurrence_literal
#print axioms globalExpressionOccurrence_boolean

end Goose.Lower.Validation.ReplacementContentFlowSource
