import Goose.Lower.Validation.SummaryPreservationSourceControlKernels

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem stopped_printedArguments (args : List PrintArg) : StoppedGraph (lowerPrintArgs args) := by
  induction args with
  | nil => exact StoppedGraph.pure _
  | cons arg rest ih =>
    cases arg with
    | text text => exact StoppedGraph.bind ih fun _ => StoppedGraph.pure _
    | expr expression => exact StoppedGraph.bind (stopped_lowerExpr expression) fun _ =>
        StoppedGraph.bind ih fun _ => StoppedGraph.pure _

private theorem printedArgumentsReplay {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
    (args : List PrintArg)
    (child : ∀ expression, PrintArg.expr expression ∈ args → ∀ state provenance,
      ExpressionReplayAt typingEnv env results vt target scopeCount expression state provenance)
    {start finish : Nat} {before after : RState} {initial : LS} {upper : Prov}
    (typed : tyPrintArgs typingEnv args start = .ok ((), finish))
    (replay : rpPrintArgs env args before = .ok ((), after))
    (ceiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper)
    (generated : GeneratedBuilderState initial)
    (native : NativeRows vt (lowerPrintArgs args (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerPrintArgs args (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerPrintArgs args (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerPrintArgs args (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1.flatMap PrintPart.uses,
          value < (lowerPrintArgs args (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  induction args generalizing start before initial upper with
  | nil => exact ⟨upper, ready, by simp [lowerPrintArgs, pure_run], fun _ _ => rfl⟩
  | cons arg rest ih =>
    cases arg with
    | text text =>
      obtain ⟨next, completed, bounded, retained⟩ := ih
        (fun expression member => child expression (by simp [member])) typed replay ready generated native
      exact ⟨next, completed, by simpa only [lowerPrintArgs, bind_run, pure_run, List.flatMap_cons, PrintPart.uses, List.nil_append] using bounded, retained⟩
    | expr expression =>
      obtain ⟨type, middleCounter, expressionTyped, tailTyped⟩ := (st_bind_ok _ _ _ _).mp typed
      have tailTyped : tyPrintArgs typingEnv rest middleCounter = .ok ((), finish) := by
        cases type <;> first | exact tailTyped | exact ((rej_ok _ _ _ _).mp tailTyped).elim
      obtain ⟨roots, middleState, expressionReplay, tailReplay⟩ := (st_bind_ok _ _ _ _).mp replay
      let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
      let lowered := lowerExpr expression le initial
      have expressionEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.2.2.1 env rest) (rp_rebinds_mono_all.2.2.2.2.2.2.2.1 env rest)
        (rp_flags_mono_all.2.2.2.2.2.2.2.1 env rest) tailReplay ceiling
      have expressionNative : NativeRows vt lowered.2 := native.of_prefix (types_lowerPrintArgs rest le lowered.2 _ _ rfl)
      obtain ⟨middle, expressionReady, expressionValue, expressionPrefix⟩ := child expression (by simp) initial upper
        type start middleCounter before middleState roots expressionTyped expressionReplay expressionEffect ready generated expressionNative
      have tailGenerated := generated.lowerExpr expression (rfl : lowerExpr expression le initial = lowered)
      have tailNative : NativeRows vt (lowerPrintArgs rest le lowered.2).2 := native
      obtain ⟨next, completed, bounded, retained⟩ := ih
        (fun value member => child value (by simp [member])) tailTyped tailReplay expressionReady tailGenerated tailNative
      refine ⟨next, completed, ?_, ?_⟩
      · intro live value member
        simp only [lowerPrintArgs, bind_run, pure_run, List.flatMap_cons, PrintPart.uses, List.singleton_append,
          List.mem_cons] at member
        rcases member with rfl | tailMember
        · have childLive : lowered.2.cur.isSome = true := by
            cases current : lowered.2.cur with
            | some block => rfl
            | none =>
              have dead := (stopped_printedArguments rest le lowered.2 _ _ rfl current).1
              change (lowerPrintArgs rest le lowered.2).2.cur.isSome = true at live
              rw [dead] at live
              cases live
          exact Nat.lt_of_lt_of_le (expressionValue childLive).bound (advB_lowerPrintArgs rest le lowered.2 _ _ rfl).vals
        · exact bounded live value tailMember
      · intro old bound
        have grows : upper.vals.size ≤ middle.vals.size := by
          rw [ready.roots.valueSize, expressionReady.roots.valueSize]
          exact (advB_lowerExpr expression le initial _ _ rfl).vals
        exact (retained old (Nat.lt_of_lt_of_le bound grows)).trans (expressionPrefix old bound)

theorem statementReplay_print {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    {args : List PrintArg} {origin : OriginId}
    (tables : SourceRootTables typingEnv env)
    (child : ∀ expression, PrintArg.expr expression ∈ args → ∀ state provenance,
      ExpressionReplayAt typingEnv env results vt target scopeCount expression state provenance) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.print args origin) initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopTargets loopReplay native
  have children := tyStmt_print_children typed
  obtain ⟨_, sourceAfter, argsReplay, emitted⟩ := (st_bind_ok _ _ _ _).mp replay
  have same : after = { sourceAfter with eff := {sourceAfter.eff with outputs := true} } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp emitted)
  have priorEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) sourceAfter.eff after.eff := by
    rw [same]
    exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
      fun _ h => h, fun h => h, fun _ => rfl, fun h => h⟩
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerPrintArgs args le initial
  obtain ⟨next, argsReady, bounded, retained⟩ := printedArgumentsReplay args child children.1 argsReplay
    (priorEffect.trans ceiling) ready generated
    (native.of_prefix (types_emitEffect (.print lowered.1 (some origin)) le lowered.2 _ _ rfl))
  have completed := argsReady.emitEffect_live (.print lowered.1 (some origin))
    (by intro live; apply Inst.SymbolsWithin.eff
        · simpa only [Effect.uses] using bounded live
        · intro candidate same; cases same; exact tables.mutation_origin_bound typed
        · trivial)
    (by intros; trivial)
    (by
      intro _
      apply (effectStep_print_refines (module := lower env.mod) (vt := vt) (provenance := next)
        (args := lowered.1) (origin := some origin) (effectRefinement_empty _ sourceAfter.eff)).trans
      simpa only [same] using ceiling)
  exact ⟨next, completed, retained, mutation_statement_transfer loop typed rfl ready retained⟩

#print axioms statementReplay_print

end Goose.Lower.Validation.SummaryPreservation
