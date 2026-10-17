import Goose.Lower.ReflectionControl
import Goose.Lower.ReflectionBranchesSteps
import Goose.Lower.ReflectionEffects
import Goose.Lower.ReflectionMutations
import Goose.Lower.PrintSources
import Goose.Lower.Claims
import Goose.Lower.FinalStatements

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem PrintSourceCursor.atFuel {cfg : Cfg} {env : Env} {high low : Nat} {results : List Ty}
    {args : List PrintArg} {state : St}
    (cursor : PrintSourceCursor (cfg := cfg) env high results args state) (bound : low ≤ high) :
    PrintSourceCursor (cfg := cfg) env low results args state := by
  induction args generalizing low high state with
  | nil => cases cursor; exact .nil
  | cons arg args ih =>
      cases arg with
      | text text =>
          cases cursor with
          | text tail => exact .text (ih tail bound)
      | expr expression =>
          cases cursor with
          | expr source printable metadata resume =>
              refine .expr source printable metadata ?_
              intro part final done
              have promoted : execPrintArg (high + 1) cfg env (.expr expression) state = .ok part final := by
                have monotone := (monoAll (low + 1) (high + 1) (by omega)).printArg cfg env (.expr expression)
                exact (monotone state).1 part final done
              exact ih (resume promoted) bound

def TypedPrintArgsReflection (fuel : Nat) (cfg : Cfg) (results : List Ty)
    (args : List PrintArg) : Prop :=
  ∀ residual, residual ≤ fuel → ∀ expression, .expr expression ∈ args →
    TypedExprReflection residual cfg results expression

theorem PrintSourceCursor.resumeFamily {cfg : Cfg} {env : Env} {sourceFuel : Nat}
    {results : List Ty} {arg : PrintArg} {args : List PrintArg} {state final : St}
    (sources : ∀ fuel, PrintSourceCursor (cfg := cfg) env fuel results (arg :: args) state)
    {output : String}
    (done : execPrintArg (sourceFuel + 1) cfg env arg state = .ok output final) :
    ∀ fuel, PrintSourceCursor (cfg := cfg) env fuel results args final := by
  intro fuel
  let common := max sourceFuel fuel
  have cursor := sources common
  cases arg with
  | text text =>
      cases cursor with
      | text tail =>
          have values : output = text ∧ final = state := by
            have equal : Res.ok text state = Res.ok output final := by
              simpa only [execPrintArg, pure_apply] using done
            cases equal
            exact ⟨rfl, rfl⟩
          rcases values with ⟨rfl, rfl⟩
          exact tail.atFuel (Nat.le_max_right _ _)
  | expr expression =>
      cases cursor with
      | expr source printable metadata resume =>
          have widened : execPrintArg (common + 1) cfg env (.expr expression) state = .ok output final := by
            have monotone := (monoAll (sourceFuel + 1) (common + 1) (by omega)).printArg
              cfg env (.expr expression)
            exact (monotone state).1 output final done
          exact (resume widened).atFuel (Nat.le_max_right _ _)

private theorem printEvalOutput {cfg : Cfg} {env : Env} {expression : Expr} {state after : St}
    {sourceFuel : Nat} {value : Val} (source : ExprSource cfg env expression state)
    (printable : (∃ ty, source.ty = .int ty) ∨ source.ty = .bool)
    (done : evalExpr sourceFuel cfg env expression state = .ok value after) :
    ∃ output, render value = pure output ∧ render value after = .ok output after ∧
      execPrintArg (sourceFuel + 1) cfg env (.expr expression) state = .ok output after := by
  have typed := (source.result sourceFuel value done).typed
  rcases printable with intPrintable | boolPrintable
  · obtain ⟨integer, type⟩ := intPrintable
    rw [type] at typed
    obtain ⟨number, rfl⟩ := Core.Sound.hasTy_int typed
    refine ⟨toString number, ?_, ?_, ?_⟩
    · simp only [render]
    · simp only [render, pure_apply]
    · simp only [execPrintArg, bind_apply]
      simp only [done, render, pure_apply]
  · rw [boolPrintable] at typed
    obtain ⟨boolean, rfl⟩ := Core.Sound.hasTy_bool typed
    cases boolean with
    | false =>
        refine ⟨"false", ?_, ?_, ?_⟩
        · simp only [render]
        · simp only [render, pure_apply]
        · simp only [execPrintArg, bind_apply, done, render, pure_apply]
    | true =>
        refine ⟨"true", ?_, ?_, ?_⟩
        · simp only [render]
        · simp only [render, pure_apply]
        · simp only [execPrintArg, bind_apply, done, render, pure_apply]

private theorem printArgsFuelMonotone {cfg : Cfg} {env : Env} {args : List PrintArg} :
    FuelMonotone (fun n => mapList (execPrintArg (n + 1) cfg env) args) := by
  intro n k bound
  exact MonoM.mapList
    (fun arg => (monoAll (n + 1) (k + 1) (by omega)).printArg cfg env arg) args

theorem typedPrintArgsReflection {fuel : Nat} {cfg : Cfg} {results : List Ty} {env : Env}
    {args : List PrintArg} {state : St}
    (expressions : TypedPrintArgsReflection fuel cfg results args)
    (sources : ∀ n, PrintSourceCursor (cfg := cfg) env n results args state)
    {ls after : LS} {parts : List PrintPart} {pt : Pt} {cx : FnCtx} {fr : Frame}
    (lowering : lowerPrintArgs args (lowerEnv cfg.mod env.vars results) ls = (parts, after))
    (point : ls.pp = some pt)
    (extension : ExtT after cx.fn.blocks) (related : Rel cfg env cx fr ls)
    (moduleEq : cx.cfg.mod = lower cfg.mod) (resultsEq : cx.fn.results = results)
    (generated : GeneratedBuilderState ls) :
    ReflectAtFuel fuel cx pt fr (fun n => mapList (execPrintArg (n + 1) cfg env) args)
      (fun strings _ pt' fr' => ∃ cells, Post cfg env cx ls fr after fr' pt' cells ∧
        (∀ id ∈ partsIds parts, ∃ value, (id, value) ∈ cells) ∧ PartsRender fr' parts strings) state := by
  induction args generalizing fuel state ls after parts pt cx fr with
  | nil =>
      simp only [lowerPrintArgs, pure_run] at lowering
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj lowering
      simp only [mapList]
      exact ReflectAtFuel.ret fuel ⟨[], Post.init related point, by simp [partsIds], trivial⟩
  | cons arg args ih =>
      cases arg with
      | text text =>
          simp only [lowerPrintArgs, bind_eq] at lowering
          obtain ⟨suffix, middle, tailRun, finished⟩ := lowering
          rw [pure_run] at finished
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj finished
          have tailSources : ∀ n, PrintSourceCursor (cfg := cfg) env n results args state := by
            intro n
            cases sources n with
            | text tail => exact tail
          have tailExpressions : TypedPrintArgsReflection fuel cfg results args := by
            intro residual bound expression member
            exact expressions residual bound expression (by simp [member])
          have tailReflection := ih tailExpressions tailSources tailRun point extension related
            moduleEq resultsEq generated
          have outputReflection : ReflectAtFuel fuel cx pt fr
              (fun n => mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                pure (text :: strings))
              (fun strings _ pt' fr' => ∃ cells, Post cfg env cx ls fr middle fr' pt' cells ∧
                (∀ id ∈ partsIds (.text text :: suffix), ∃ value, (id, value) ∈ cells) ∧
                PartsRender fr' (.text text :: suffix) strings) state := by
            refine tailReflection.bind ?_ printArgsFuelMonotone (fun strings n k bound => MonoM.refl _)
            · intro n strings next pt' fr' done matched residual bound
              obtain ⟨cells, post, ids, rendered⟩ := matched
              exact ReflectAtFuel.ret residual ⟨cells, post, by simpa [partsIds] using ids,
                ⟨rfl, rendered⟩⟩
          have sourceEq : ∀ n,
              (mapList (execPrintArg (n + 1) cfg env) (.text text :: args) state) =
                ((mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                  pure (text :: strings)) state) := by
            intro n
            simp only [mapList, execPrintArg, pure_bind]
          exact outputReflection.of_source (fun n => ⟨n, sourceEq n⟩)
      | expr expression =>
          simp only [lowerPrintArgs, bind_eq] at lowering
          obtain ⟨id, middle, expressionRun, suffix, final, tailRun, finished⟩ := lowering
          rw [pure_run] at finished
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj finished
          have middleExtension : ExtT middle cx.fn.blocks :=
            extension.of_adv (advB_lowerPrintArgs args _ _ _ _ tailRun)
          cases cursor : sources fuel with
          | expr headSource printable headMetadata headResume =>
              have headReflection :=
                expressions fuel (Nat.le_refl _) expression (by simp)
                  env state headSource headMetadata ls middle id pt cx fr expressionRun point
                  middleExtension related moduleEq resultsEq generated
              have continuationMonotone : ∀ value,
                  FuelMonotone (fun n => render value >>= fun part =>
                    mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                      pure (part :: strings)) := by
                intro value n k bound
                exact MonoM.bind (MonoM.refl _) (fun part =>
                  MonoM.bind
                    (MonoM.mapList
                      (fun arg => (monoAll (n + 1) (k + 1) (by omega)).printArg cfg env arg) args)
                    (fun strings => MonoM.refl _))
              have composition : ReflectAtFuel fuel cx pt fr
                  (fun n => evalExpr n cfg env expression >>= fun value =>
                    render value >>= fun part =>
                      mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                        pure (part :: strings))
                  (fun strings _ pt' fr' => ∃ cells, Post cfg env cx ls fr final fr' pt' cells ∧
                    (∀ target ∈ partsIds (.val id :: suffix), ∃ value, (target, value) ∈ cells) ∧
                    PartsRender fr' (.val id :: suffix) strings) state := by
                refine headReflection.bind ?_
                  (fun n k bound => (monoAll n k bound).expr cfg env expression)
                  continuationMonotone
                intro sourceFuel value next pt1 fr1 done matched residual residualBound
                cases sourceCursor : sources sourceFuel with
                | expr reflectedSource reflectedPrintable reflectedMetadata reflectedResume =>
                    obtain ⟨part, renderPure, rendered, printDone⟩ :=
                      printEvalOutput reflectedSource reflectedPrintable done
                    have tailSources : ∀ n, PrintSourceCursor (cfg := cfg) env n results args next :=
                      PrintSourceCursor.resumeFamily sources printDone
                    have tailExpressions : TypedPrintArgsReflection residual cfg results args := by
                      intro remaining bound expression' member
                      exact expressions remaining (Nat.le_trans bound residualBound) expression'
                        (by simp [member])
                    have tailReflection := ih tailExpressions tailSources tailRun matched.pp extension
                      matched.rel moduleEq resultsEq (generated.lowerExpr expression expressionRun)
                    have mappedTail : ReflectAtFuel residual cx pt1 fr1
                        (fun n => mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                          pure (part :: strings))
                        (fun strings _ pt' fr' => ∃ cells,
                          Post cfg env cx ls fr final fr' pt' cells ∧
                          (∀ target ∈ partsIds (.val id :: suffix), ∃ cell, (target, cell) ∈ cells) ∧
                          PartsRender fr' (.val id :: suffix) strings) next := by
                      refine tailReflection.bind ?_ printArgsFuelMonotone
                        (fun strings n k bound => MonoM.refl (pure (part :: strings)))
                      intro n strings afterTail pt' fr' tailDone tailMatched lastFuel lastBound
                      obtain ⟨cells, post, ids, renderedTail⟩ := tailMatched
                      have headCell : fr'.vals[id]? = some (.val value) := by
                        rw [post.same id (matched.lt (id, .val value) (by simp))]
                        exact matched.has (id, .val value) (by simp)
                      have combinedPost : Post cfg env cx ls fr final fr' pt'
                          ((id, .val value) :: cells) := by
                        exact (matched.comp post).sub (by intro cell member; simpa using member)
                      have combinedIds : ∀ target ∈ partsIds (.val id :: suffix),
                          ∃ cell, (target, cell) ∈ (id, .val value) :: cells := by
                        intro target member
                        simp only [partsIds, List.mem_cons] at member
                        rcases member with head | tail
                        · subst target
                          exact ⟨.val value, by simp⟩
                        · obtain ⟨cell, present⟩ := ids target tail
                          exact ⟨cell, by simp [present]⟩
                      have combinedRender : PartsRender fr' (.val id :: suffix) (part :: strings) := by
                        exact ⟨⟨value, headCell, renderPure⟩, renderedTail⟩
                      exact ReflectAtFuel.ret lastFuel ⟨(id, .val value) :: cells,
                        combinedPost, combinedIds, combinedRender⟩
                    have sourceEq : ∀ n,
                        ((render value >>= fun headString =>
                          mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                            pure (headString :: strings)) next) =
                          ((mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                            pure (part :: strings)) next) := by
                      intro n
                      rw [renderPure, pure_bind]
                    exact mappedTail.of_source (fun n => ⟨n, sourceEq n⟩)
              have sourceEq : ∀ n,
                  (mapList (execPrintArg (n + 1) cfg env) (.expr expression :: args) state) =
                    ((evalExpr n cfg env expression >>= fun value =>
                      render value >>= fun part =>
                        mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                          pure (part :: strings)) state) := by
                intro n
                simp only [mapList, execPrintArg, bind_assoc]
              exact composition.of_source (fun n => ⟨n, sourceEq n⟩)

theorem typedStatementReflection_print {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {args : List PrintArg} {origin : OriginId}
    (expressions : TypedPrintArgsReflection fuel cfg results args) :
    TypedStatementReflection fuel cfg results loop (.print args origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension related moduleEq
    resultsEq depth targets counter generated frames
  let sources : ∀ n, PrintSourceCursor (cfg := cfg) env n results args state := fun n =>
    source.printSourceCursor n metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨parts, middle, partsRun, emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitEffect emit)
  have arguments := typedPrintArgsReflection expressions sources partsRun point middleExtension related
    moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
        Goose.Core.emit (String.join strings ++ "\n") >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine arguments.bind ?_ printArgsFuelMonotone (fun strings n k bound => MonoM.refl _)
    intro sourceFuel strings next ptk frk done matched residual bound
    obtain ⟨cells, argumentPost, ids, rendered⟩ := matched
    let output := String.join strings ++ "\n"
    have effectEqual : execEff cx.fn frk (.print parts (some origin)) =
        (Goose.Core.emit output >>= fun _ => pure frk) := by
      simp only [execEff, mapList_renderPart_of rendered, pure_bind, output]
    have effectReflection := normalEffectReflection (fuel := residual) (state := next) argumentPost emit extension
      (source := fun _ => Goose.Core.emit output)
      (monotone := fun n k bound => MonoM.refl _)
      (sourceFuel := 0) effectEqual
    exact effectReflection.mono (fun flow _ pt' fr' matched => Or.inl matched)
  have sourceEq : ∀ n,
      ((execStmt (n + 2) cfg env (.print args origin) >>= prepareLoopFlow env loop) state) =
        ((mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
          Goose.Core.emit (String.join strings ++ "\n") >>= fun _ => pure (Flow.normal .unit)) state) := by
    intro n
    cases loop <;>
      simp only [execStmt, prepareLoopFlow, prepareReturn, prepareLoopExit, bind_assoc, pure_bind]
  exact composition.of_source (fun n => ⟨n + 2, sourceEq n⟩)

theorem ReflectAtFuel.abortTerm {cx : FnCtx} {pt : Pt} {fr : Frame}
    {source : Nat → M α} {post : α → St → Pt → Frame → Prop} {state : St}
    {fuel sourceFuel : Nat} {kind : AbortKind} {origin : OriginId}
    (instruction : instAt cx.fn pt = some (.term (.abort kind (some origin))))
    (sourceRun : source sourceFuel state = .stop (.abort kind origin) state) :
    ReflectAtFuel fuel cx pt fr source post state := by
  cases fuel with
  | zero => exact ReflectAtFuel.zero cx pt fr source post state
  | succ fuel =>
    intro result nonTimeout run
    have targetRun : runAt cx pt fr (fuel + 1) state = .stop (.abort kind origin) state := by
      unfold runAt
      rw [instsAt_cons instruction]
      simp [exec, abortAtOrg, abortAt, M.stop]
    rw [targetRun] at run
    cases run
    exact Or.inr ⟨sourceFuel, .abort kind origin, state, sourceRun, rfl⟩

theorem typedStatementReflection_abort {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {message : String} {origin : OriginId} :
    TypedStatementReflection fuel cfg results loop (.abort message origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq
    depth targets counter generated frames
  obtain ⟨_, _, _, instruction⟩ := emitTerm_facts lowering point extension
  have sourceRun :
      (execStmt 1 cfg env (.abort message origin) >>= prepareLoopFlow env loop) state =
        .stop (.abort .userAbort origin) state := by
    simp only [execStmt, abortAt]
    rw [bind_apply]
    rfl
  exact ReflectAtFuel.abortTerm instruction sourceRun

theorem ReflectAtFuel.exitTerm {cx : FnCtx} {pt : Pt} {fr : Frame}
    {source : Nat → M α} {post : α → St → Pt → Frame → Prop} {state : St}
    {fuel sourceFuel : Nat} {id : ValueId} {integer : IntTy} {code : Int} {origin : Option OriginId}
    (instruction : instAt cx.fn pt = some (.term (.exit id origin)))
    (cell : fr.vals[id]? = some (.val (.int integer code)))
    (sourceRun : source sourceFuel state = .stop (.exit code) state) :
    ReflectAtFuel fuel cx pt fr source post state := by
  cases fuel with
  | zero => exact ReflectAtFuel.zero cx pt fr source post state
  | succ fuel =>
    intro result nonTimeout run
    have targetRun : runAt cx pt fr (fuel + 1) state = .stop (.exit code) state := by
      unfold runAt
      rw [instsAt_cons instruction]
      simp [exec, getVal_of cell, expectInt, M.stop]
    rw [targetRun] at run
    cases run
    exact Or.inr ⟨sourceFuel, .exit code, state, sourceRun, rfl⟩

theorem typedStatementReflection_exit {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : TypedExprReflection fuel cfg results expression) :
    TypedStatementReflection fuel cfg results loop (.exit expression origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq
    depth targets counter generated frames
  obtain ⟨expressionSource, integer, typing, roots, type⟩ := source.exitChild
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨id, middle, expressionRun, terminated⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitTerm terminated)
  have first := child env state expressionSource expressionMetadata ls middle id pt cx fr expressionRun
    point middleExtension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= fun value =>
        expectInt value >>= fun pair =>
          (M.stop (.exit pair.2) >>= prepareLoopFlow env loop))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ n k bound => MonoM.refl _)
    intro n value next pt' fr' done matched residual bound
    have typed := (expressionSource.result n value done).typed
    rw [type] at typed
    obtain ⟨number, rfl, typed⟩ := Core.Sound.hasTy_int typed
    obtain ⟨_, _, _, instruction⟩ := emitTerm_facts terminated matched.pp extension
    have cell := matched.has (id, .val (.int integer number)) (by simp)
    have sourceRun :
        ((expectInt (.int integer number) >>= fun pair => M.stop (.exit pair.2)) >>=
          prepareLoopFlow env loop) next = .stop (.exit number) next := by
      simp [expectInt, bind_apply, M.stop]
    exact ReflectAtFuel.exitTerm (sourceFuel := 0) instruction cell sourceRun
  have sourceEq : ∀ n,
      ((execStmt (n + 1) cfg env (.exit expression origin) >>= prepareLoopFlow env loop) state) =
        ((evalExpr n cfg env expression >>= fun value =>
          expectInt value >>= fun pair =>
            (M.stop (.exit pair.2) >>= prepareLoopFlow env loop)) state) := by
    intro n
    simp only [execStmt, bind_assoc]
  exact composition.of_source (fun n => ⟨n + 1, sourceEq n⟩)

theorem typedStatementReflection_assert {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : TypedExprReflection fuel cfg results expression) :
    TypedStatementReflection fuel cfg results loop (.assertS expression origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq
    depth targets counter generated frames
  obtain ⟨expressionSource, typing, roots, type⟩ := source.assertChild
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨conditionId, middle, expressionRun, branchRun⟩ := lowering
  have middleExtension := extension.of_adv (advB_assert_core conditionId origin _ _ _ _ branchRun)
  have first := child env state expressionSource expressionMetadata ls middle conditionId pt cx fr
    expressionRun point middleExtension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= fun value =>
        expectBool value >>= fun selected =>
          (if selected then pure (Flow.normal .unit) else abortAt .assert origin) >>=
            prepareLoopFlow env loop)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ n k bound => MonoM.refl _)
    intro n value next pt1 fr1 done matched residual bound
    have typed := (expressionSource.result n value done).typed
    rw [type] at typed
    obtain ⟨selected, rfl⟩ := Core.Sound.hasTy_bool typed
    simp only [expectBool, pure_bind]
    have conditionCell := matched.has (conditionId, .val (.bool selected)) (by simp)
    obtain ⟨conditionBlock, current, live, _⟩ := LS.pp_some matched.pp
    rw [whenLive_some _ _ _ current] at branchRun
    simp only [bind_eq] at branchRun
    obtain ⟨⟨thenBlock, elseBlock⟩, forkState, forkRun, u2, abortState, setElse,
      u3, termState, abortRun, setThen⟩ := branchRun
    cases u2
    cases u3
    have elseState : abortState = { forkState with cur := some elseBlock } := by
      rw [setCur_run] at setElse
      exact (Prod.mk.inj setElse).2.symm
    have finalState : after = { termState with cur := some thenBlock } := by
      rw [setCur_run] at setThen
      exact (Prod.mk.inj setThen).2.symm
    have finalExtension : ExtT termState cx.fn.blocks := by
      rw [finalState] at extension
      exact extension
    have elseExtension : ExtT abortState cx.fn.blocks := finalExtension.of_adv (adv_emitTerm abortRun)
    have forkExtension : ExtT forkState cx.fn.blocks := by
      rw [elseState] at elseExtension
      exact elseExtension
    obtain ⟨thenBlockEq, elseBlockEq, _, valsEq, stackFork, _, branchInstruction,
      thenAt, elseAt⟩ := fork_facts forkRun matched.pp forkExtension
    have elsePoint : abortState.pp = some (elseBlock, 0) := by
      rw [elseState]
      exact LS.pp_cur elseAt
    have thenPoint : after.pp = some (thenBlock, 0) := by
      rw [finalState]
      have thenAtFinal : termState.blocks[thenBlock]? = some ⟨[], #[]⟩ := by
        rw [emitTerm_run _ _ (show abortState.cur = some elseBlock by rw [elseState]) ] at abortRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj abortRun
        show (abortState.blocks.modify elseBlock _)[thenBlock]? = _
        have different : elseBlock ≠ thenBlock := by
          have ordered : thenBlock < elseBlock := by
            rw [thenBlockEq, elseBlockEq]
            exact Nat.lt_succ_self _
          exact Nat.ne_of_gt ordered
        rw [getElem?_modify_ne different]
        rw [elseState]
        exact thenAt
      exact LS.pp_cur thenAtFinal
    obtain ⟨valuesTerm, stackTerm, _, abortInstruction⟩ := emitTerm_facts abortRun elsePoint finalExtension
    have hstMiddle : middle.stack = ls.stack := matched.rel.stack.trans rel.stack.symm
    have hstFinal : after.stack = ls.stack := by
      rw [finalState, stackTerm, elseState]
      exact stackFork.trans hstMiddle
    have hvalsFinal : after.vals.size = middle.vals.size := by
      rw [finalState, valuesTerm, elseState, valsEq]
    have thenTarget : ∃ block, cx.fn.blocks[thenBlock]? = some block ∧ block.params = [] := by
      obtain ⟨block, atBlock, params⟩ := forkExtension.params thenAt
      exact ⟨block, atBlock, params⟩
    have elseTarget : ∃ block, cx.fn.blocks[elseBlock]? = some block ∧ block.params = [] := by
      obtain ⟨block, atBlock, params⟩ := forkExtension.params elseAt
      exact ⟨block, atBlock, params⟩
    obtain ⟨thenTargetBlock, thenTargetAt, thenParameters⟩ := thenTarget
    obtain ⟨elseTargetBlock, elseTargetAt, elseParameters⟩ := elseTarget
    have branchAt : instAt cx.fn pt1 = some (.term (.condbr conditionId thenBlock [] elseBlock [])) := by
      exact branchInstruction
    cases residual with
    | zero => exact ReflectAtFuel.zero cx pt1 fr1 _ _ next
    | succ residual =>
      cases selected with
      | false =>
        have abortSource :
            (if false then pure (Flow.normal .unit) else abortAt .assert origin) >>=
              prepareLoopFlow env loop = fun s => .stop (.abort .assert origin) s := by
          funext s
          simp only [Bool.false_eq_true, ↓reduceIte]
          change M.bind' (M.stop (.abort .assert origin) : M Flow)
            (prepareLoopFlow env loop) s = _
          rfl
        have sourceRun :
            ((if false then pure (Flow.normal .unit) else abortAt .assert origin) >>=
              prepareLoopFlow env loop) next = .stop (.abort .assert origin) next :=
          congrFun abortSource next
        have targetAbortInstruction :
            instAt cx.fn (elseBlock, 0) = some (.term (.abort .assert (some origin))) := by
          simpa only [instAt_eq] using abortInstruction
        have stopped : ReflectAtFuel residual cx (elseBlock, 0) fr1
            (fun _ => (if false then pure (Flow.normal .unit) else abortAt .assert origin) >>=
              prepareLoopFlow env loop)
            (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') next :=
          ReflectAtFuel.abortTerm (fuel := residual) (cx := cx) (pt := (elseBlock, 0))
            (fr := fr1) (source := fun _ =>
              (if false then pure (Flow.normal .unit) else abortAt .assert origin) >>=
                prepareLoopFlow env loop)
            (post := fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr')
            (state := next) (sourceFuel := 0)
            (kind := .assert) (origin := origin) targetAbortInstruction sourceRun
        exact ReflectAtFuel.condbr branchAt conditionCell thenTargetAt thenParameters elseTargetAt
          elseParameters stopped
      | true =>

        have finalPost : StatementLoopPost cfg env cx ls fr after loop (.normal .unit) (thenBlock, 0) fr1 :=
          Or.inl ⟨rfl, Post.nil thenPoint (by rw [hvalsFinal]; exact matched.mono)
            matched.same (matched.rel.stack_eq (hstFinal.trans hstMiddle.symm))⟩
        have normal : ReflectAtFuel residual cx (thenBlock, 0) fr1
            (fun _ => pure (Flow.normal .unit))
            (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') next :=
          ReflectAtFuel.ret residual finalPost
        have selectedBranch := ReflectAtFuel.condbr branchAt conditionCell thenTargetAt thenParameters
          elseTargetAt elseParameters normal
        cases loop <;> simpa [expectBool, prepareLoopFlow, prepareReturn, prepareLoopExit] using selectedBranch
  have sourceEq : ∀ n,
      ((execStmt (n + 1) cfg env (.assertS expression origin) >>= prepareLoopFlow env loop) state) =
        ((evalExpr n cfg env expression >>= fun value =>
          expectBool value >>= fun selected =>
            (if selected then pure (Flow.normal .unit) else abortAt .assert origin) >>=
              prepareLoopFlow env loop) state) := by
    intro n
    simp only [execStmt, bind_assoc]
  exact composition.of_source (fun n => ⟨n + 1, sourceEq n⟩)

end Goose.Lower
