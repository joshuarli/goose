import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlSteps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.SourceGlobalControlLeaves

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot : DemandNode} {siteTargets : List BlockId} {loop : Option LoopCtx}
  {scope : ScopeId} {initial : LS} {upper : Prov}

theorem globalStatementOccurrence_break {origin : OriginId} :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope
      (.brk origin) initial upper := by
  intro source output start finish before after typed replay ceiling scopes stack ready sites targetBound generated loopBounds loopReplay counterTyped included native _recipes _continuation
  obtain ⟨next, completed, retained, returns⟩ := globalStatementReplay_break
    output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  have growth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize, completed.roots.valueSize]
    exact (advB_lowerStmt loop (.brk origin) _ initial _ _ rfl).vals
  have initialSites := sites.ghost_retained growth retained
  have ledger : OccurrenceLedger env (.statement (.brk origin)) func vt next initial
      (lowerStmt loop (.brk origin) (lowerEnv env.mod env.impl.vars returnTypes) initial).2 := by
    cases loop with
    | none => exact .refl _ _
    | some context =>
      exact (occurrenceLedger_leaveAll (initial.stack.take (initial.stack.length - context.depth)) _ _ _ _ rfl).trans
        (emitsOnly_emitTerm _ (occurrenceInstructionTerm _) _ _ _ _ rfl)
  have finalSites : OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes)
      (lowerStmt loop (.brk origin) (lowerEnv env.mod env.impl.vars returnTypes) initial).2
      func vt next := by
    cases loop with
    | none => exact initialSites
    | some context =>
      have left := occurrenceSites_leaveAll (initial.stack.take (initial.stack.length - context.depth)) initialSites
      apply left.emitTerm (run := rfl)
      intro destination member
      have same : destination = context.breakTo := by simpa [Term.successors] using member
      subst destination
      exact Or.inl (included _ (by simp [LoopBuilderFrameTargets]))
  exact ⟨next, completed, retained, returns, ledger, finalSites⟩

theorem globalStatementOccurrence_continue {origin : OriginId} :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope
      (.cont origin) initial upper := by
  intro source output start finish before after typed replay ceiling scopes stack ready sites targetBound generated loopBounds loopReplay counterTyped included native _recipes _continuation
  obtain ⟨next, completed, retained, returns⟩ := globalStatementReplay_continue
    output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  have growth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize, completed.roots.valueSize]
    exact (advB_lowerStmt loop (.cont origin) _ initial _ _ rfl).vals
  have initialSites := sites.ghost_retained growth retained
  let le := lowerEnv env.mod env.impl.vars returnTypes
  have ledger : OccurrenceLedger env (.statement (.cont origin)) func vt next initial
      (lowerStmt loop (.cont origin) le initial).2 := by
    cases loop with
    | none => exact .refl _ _
    | some context =>
      have left := occurrenceLedger_leaveAll (env := env) (root := .statement (.cont origin))
        (func := func) (types := vt) (upper := next)
        (initial.stack.take (initial.stack.length - context.depth)) le initial _ _ rfl
      cases continuation : context.cont with
      | jump header =>
        simp only [lowerStmt, bind_run, continuation]
        exact left.trans (emitsOnly_emitTerm (.br header []) (occurrenceInstructionTerm _) _ _ _ _ rfl)
      | next header type counter =>
        have scalar : valRefLike vt counter = false := by
          have row : vt[counter]? = some (some (.data (.int type))) := by
            simpa only [OccurrenceLoopCounterTyped, continuation] using counterTyped
          simp only [valRefLike, row, Option.join_some, Option.any_some, VTy.refLike, Ty.isRefLike]
        have incremented : OccurrenceLedger env (.statement (.cont origin))
            func vt next
            (Goose.Lower.leaveTo context.depth le initial).2
            (emitDef (.next type counter) le (Goose.Lower.leaveTo context.depth le initial).2).2 :=
          emitsOnly_emitDef rfl (InstructionOccurrences.next _ counter type scalar)
        simp only [lowerStmt, bind_run, continuation]
        exact (left.trans incremented).trans (emitsOnly_emitTerm _ (occurrenceInstructionTerm _) _ _ _ _ rfl)
  have finalSites : OccurrenceSitesBuilder env siteRoot siteTargets le (lowerStmt loop (.cont origin) le initial).2
      func vt next := by
    cases loop with
    | none => exact initialSites
    | some context =>
      have left := occurrenceSites_leaveAll (initial.stack.take (initial.stack.length - context.depth)) initialSites
      cases continuation : context.cont with
      | jump header =>
        simp only [lowerStmt, bind_run, continuation]
        apply left.emitTerm (term := .br header []) (run := rfl)
        intro destination member
        have same : destination = header := by simpa [Term.successors] using member
        subst destination
        exact Or.inl (included _ (by simp [LoopBuilderFrameTargets, continuation]))
      | next header type counter =>
        simp only [lowerStmt, bind_run, continuation]
        have incremented := left.emitDef (op := .next type counter) (run := rfl) (Nat.le_refl _) (fun _ _ => rfl)
        apply incremented.emitTerm (run := rfl)
        intro destination member
        have same : destination = header := by simpa [Term.successors] using member
        subst destination
        exact Or.inl (included _ (by simp [LoopBuilderFrameTargets, continuation]))
  exact ⟨next, completed, retained, returns, ledger, finalSites⟩

#print axioms globalStatementOccurrence_break
#print axioms globalStatementOccurrence_continue

end Goose.Lower.Validation.ReplacementContentFlowSource
