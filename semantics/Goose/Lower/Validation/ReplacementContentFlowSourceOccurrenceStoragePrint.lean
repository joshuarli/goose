import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsPrintGlobal
import Goose.Lower.Validation.SourceStatementTypingTransfers
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrencePrintTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem statementOccurrence_print {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    {arguments : List PrintArg} {origin : OriginId} (tables : SourceRootTables typingEnv env)
    (child : ∀ expression, PrintArg.expr expression ∈ arguments → ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
        siteRoot siteTargets expression state provenance) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets loop scope (.print arguments origin) initial upper := by
  intro occurrence output start finish before after typed replay ceiling _scopes _stack ready sites targets generated _loop _bounds _counter _included native metadata continuation
  obtain ⟨_, sourceAfter, argsReplay, emitted⟩ := (st_bind_ok _ _ _ _).mp replay
  have same : after = {sourceAfter with eff := {sourceAfter.eff with outputs := true}} :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp emitted)
  have priorEffect : EffectRefinement func sourceAfter.eff after.eff := by
    rw [same]
    exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
      fun _ h => h, fun h => h, fun _ => rfl, fun h => h⟩
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerPrintArgs arguments le initial
  have paths : ∀ expression, PrintArg.expr expression ∈ arguments →
      ∃ path, DemandNodeAt (.statement (.print arguments origin)) path (.expression expression) := by
    intro expression member
    obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
    exact ⟨[index], .child (by simp [DemandNode.child?, DemandNode.children, List.getElem?_map, row]) (.here _)⟩
  obtain ⟨next, argsReady, values, retained, argsLedger, argsSites⟩ :=
    typedGlobalPrintArgumentsOccurrence arguments child initial upper occurrence paths start finish before sourceAfter (tyStmt_print_children typed).1 argsReplay
      (priorEffect.trans ceiling) ready sites targets generated
      (native.of_prefix (types_emitEffect (.print lowered.1 (some origin)) le lowered.2 _ _ rfl))
      (metadata.of_advance (advB_emitEffect (.print lowered.1 (some origin)) le lowered.2 _ _ rfl))
      (continuation.of_advance (advB_emitEffect (.print lowered.1 (some origin)) le lowered.2 _ _ rfl))
  have completed := argsReady.emitEffect_live (.print lowered.1 (some origin))
    (by intro live; apply Inst.SymbolsWithin.eff
        · intro value member
          exact (values live value member).1
        · intro candidate same; cases same; exact tables.mutation_origin_bound typed
        · trivial)
    (by intros; trivial)
    (by intro _
        apply (effectStep_print_refines (module := lower env.mod) (vt := vt) (provenance := next)
          (args := lowered.1) (origin := some origin) (effectRefinement_empty _ sourceAfter.eff)).trans
        simpa only [same] using ceiling)
  have finalLedger := occurrence_emitEffect_live (env := env) (root := .statement (.print arguments origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitEffect (.print lowered.1 (some origin)) le lowered.2 = _) (by
      intro live
      apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
        (consumed := InstructionOccurrences.no_references (by
          intro value member mutability payload reference
          exact printArguments_no_reference arguments tables (tyStmt_print_children typed).1 generated
            (native.of_prefix (types_emitEffect (.print lowered.1 (some origin)) le lowered.2 _ _ rfl)) live value
            (by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member)
            mutability payload reference))
      intro value member _
      exact (values live value (by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member)).2)
  have finalSites := argsSites.mutationEffect (effect := .print lowered.1 (some origin)) trivial rfl
    (Nat.le_refl _) (fun _ _ => rfl)
  exact ⟨next, completed, retained, (fun expected => occurrence_mutation_transfer loop typed rfl ready retained),
    argsLedger.trans finalLedger, finalSites⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
