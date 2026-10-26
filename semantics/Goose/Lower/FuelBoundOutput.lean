import Goose.Lower.FuelBoundTyped
import Goose.Lower.FuelBoundControlSteps
import Goose.Lower.FuelBoundTypedMethods
import Goose.Lower.PrintSources
import Goose.Lower.ReflectionBranchesSteps
import Goose.Lower.ReflectionOutput
import Goose.Lower.ReflectionTransfersCoercion

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem FuelBoundAt.abortTerm {sourceFuel fuel : Nat} {cx : FnCtx} {pt : Pt} {fr : Frame}
    {source : Nat → M α} {post : α → St → Pt → Frame → Prop} {state : St}
    {kind : AbortKind} {origin : OriginId}
    (instruction : instAt cx.fn pt = some (.term (.abort kind (some origin))))
    (sourceRun : source sourceFuel state = .stop (.abort kind origin) state) :
    FuelBoundAt sourceFuel fuel cx pt fr source post state := by
  cases fuel with
  | zero => exact FuelBoundAt.zero sourceFuel cx pt fr source post state
  | succ fuel =>
      intro result final done
      have targetRun : runAt cx pt fr (fuel + 1) state = .stop (.abort kind origin) state := by
        unfold runAt
        rw [instsAt_cons instruction]
        simp [exec, abortAtOrg, abortAt, M.stop]
      rw [targetRun] at done
      cases done
      exact Or.inr ⟨.abort kind origin, state, sourceRun, rfl⟩

theorem FuelBoundAt.exitTerm {sourceFuel fuel : Nat} {cx : FnCtx} {pt : Pt} {fr : Frame}
    {source : Nat → M α} {post : α → St → Pt → Frame → Prop} {state : St}
    {id : ValueId} {integer : IntTy} {code : Int} {origin : Option OriginId}
    (instruction : instAt cx.fn pt = some (.term (.exit id origin)))
    (cell : fr.vals[id]? = some (.val (.int integer code)))
    (sourceRun : source sourceFuel state = .stop (.exit code) state) :
    FuelBoundAt sourceFuel fuel cx pt fr source post state := by
  cases fuel with
  | zero => exact FuelBoundAt.zero sourceFuel cx pt fr source post state
  | succ fuel =>
      intro result final done
      have targetRun : runAt cx pt fr (fuel + 1) state = .stop (.exit code) state := by
        unfold runAt
        rw [instsAt_cons instruction]
        simp [exec, getVal_of cell, expectInt, M.stop]
      rw [targetRun] at done
      cases done
      exact Or.inr ⟨.exit code, state, sourceRun, rfl⟩

private theorem normalEffectFuelBoundAt {sourceFuel fuel : Nat} {cfg : Cfg} {env : Env}
    {cx : FnCtx} {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt}
    {cells : List (ValueId × RVal)} {state : St} {effect : Effect} {le : LEnv}
    {loop : Option LoopCtx} {source : M α}
    (base : Post cfg env cx ls fr lsk frk ptk cells)
    (emit : emitEffect effect le lsk = ((), ls1)) (extension : ExtT ls1 cx.fn.blocks)
    (equal : execEff cx.fn frk effect = source >>= fun _ => pure frk) :
    FuelBoundAt sourceFuel fuel cx ptk frk
      (fun _ => source >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls1 loop flow pt' fr') state := by
  cases fuel with
  | zero => exact FuelBoundAt.zero sourceFuel cx ptk frk _ _ state
  | succ fuel =>
      have effectBound := leaf_eff_fuelBoundAt (sourceFuel := sourceFuel) (fuel := fuel)
        base emit extension (source := fun _ => source) equal (state := state)
      refine effectBound.bind ?_
      intro _ afterEffect pt' fr' effectDone post residual residualBound
      exact FuelBoundAt.ret (Or.inl ⟨rfl, post⟩)

def TypedExprFuelBoundBelow (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (expression : Expr) : Prop :=
  ∀ residual, residual ≤ fuel → TypedExprFuelBound sourceFuel residual cfg results expression

def TypedPlaceFuelBoundBelow (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (place : Place) : Prop :=
  ∀ residual, residual ≤ fuel → TypedPlaceFuelBound sourceFuel residual cfg results place

def TypedViewFuelBoundBelow (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (view : View) : Prop :=
  ∀ residual, residual ≤ fuel → TypedViewFuelBound sourceFuel residual cfg results view

private theorem leaveAll_fuelBoundAt {sourceFuel targetFuel : Nat} {env : Env}
    {cx : FnCtx} {entered suffix : List (ScopeId × ScopeInst)} {le : LEnv}
    {ls ls' : LS} {r : Unit} {pt : Pt} {fr : Frame} {state : St}
    (slots : cx.fn.slots = env.vars.mapIdx (fun i lv => ⟨lv.ty, lv.kind, lv.scope, i⟩))
    (activation : fr.act = env.act) (scopes : fr.scopes = entered ++ suffix)
    (lowering : leaveAll (entered.map Prod.fst) le ls = (r, ls'))
    (point : ls.pp = some pt) (extension : ExtT ls' cx.fn.blocks) :
    FuelBoundAt sourceFuel targetFuel cx pt fr (fun _ => releaseScopes env entered)
      (fun _ _ pt' fr' => UnwindPost ls fr ls' fr' suffix pt') state := by
  induction entered generalizing targetFuel state ls ls' r pt fr with
  | nil =>
      simp only [List.map_nil, leaveAll, pure_run] at lowering
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj lowering
      simp only [releaseScopes]
      exact FuelBoundAt.ret ⟨point, rfl, rfl, by simpa using scopes, rfl, rfl, rfl⟩
  | cons scope rest ih =>
      obtain ⟨scopeId, scopeInstance⟩ := scope
      cases targetFuel with
      | zero =>
          exact FuelBoundAt.zero sourceFuel cx pt fr (fun _ => releaseScopes env
            ((scopeId, scopeInstance) :: rest))
            (fun _ _ nextPoint next => UnwindPost ls fr ls' next suffix nextPoint) state
      | succ targetFuel =>
          simp only [List.map_cons, leaveAll, bind_eq] at lowering
          obtain ⟨_, middle, leave, tail⟩ := lowering
          have middleExtension := extension.of_adv
            (advB_leaveAll (rest.map Prod.fst) le middle () ls' tail)
          obtain ⟨_, stack, middlePoint, instruction⟩ :=
            emitEffect_facts leave point middleExtension
          have values : middle.vals = ls.vals := by
            obtain ⟨_, current, _, _⟩ := LS.pp_some point
            rw [emitEffect_run _ _ current] at leave
            obtain ⟨_, rfl⟩ := Prod.mk.inj leave
            rfl
          have releaseEqual : GIR.releaseScope cx.fn fr.act scopeId scopeInstance =
              Core.releaseScope env scopeId scopeInstance := by
            funext current
            have slotsSize : cx.fn.slots.size = env.vars.size := by rw [slots]; simp
            simp only [GIR.releaseScope, Core.releaseScope, activation, slotsSize]
            rw [releaseSlots_eq slots]
          let nextFrame : Frame := { fr with scopes := rest ++ suffix }
          have effectEqual : execEff cx.fn fr (.leave scopeId) =
              Core.releaseScope env scopeId scopeInstance >>= fun _ => pure nextFrame := by
            simp only [execEff, scopes, List.cons_append, ↓reduceIte]
            rw [releaseEqual]
          have first : FuelBoundAt sourceFuel (targetFuel + 1) cx pt fr
              (fun _ => Core.releaseScope env scopeId scopeInstance)
              (fun _ _ nextPoint next =>
                nextPoint = (pt.1, pt.2 + 1) ∧ next = nextFrame) state := by
            exact FuelBoundAt.eff_step instruction effectEqual
          have composition : FuelBoundAt sourceFuel (targetFuel + 1) cx pt fr
              (fun n => Core.releaseScope env scopeId scopeInstance >>= fun _ =>
                releaseScopes env rest)
              (fun _ _ nextPoint next =>
                UnwindPost middle nextFrame ls' next suffix nextPoint) state := by
            refine first.bind ?_
            intro _ after nextPoint next done matched residual residualBound
            rcases matched with ⟨rfl, rfl⟩
            exact ih (targetFuel := residual) (state := after) (ls := middle)
              (ls' := ls') (fr := nextFrame)
              (by simpa [nextFrame] using activation) rfl tail middlePoint extension
          have sourceEqual :
              (releaseScopes env ((scopeId, scopeInstance) :: rest)) state =
                ((Core.releaseScope env scopeId scopeInstance >>= fun _ => releaseScopes env rest)
                  state) := by
            rfl
          have composed := composition.of_source (otherFuel := sourceFuel)
            (other := fun _ => releaseScopes env ((scopeId, scopeInstance) :: rest)) sourceEqual
          exact composed.mono fun _ _ nextPoint next post =>
            ⟨post.pp, by simpa [nextFrame] using post.values,
              by simpa [nextFrame] using post.activation, post.scopes, post.depth,
              post.builderValues.trans values, post.lexicalStack.trans stack⟩

private theorem leaveTo_fuelBoundAt {sourceFuel targetFuel : Nat} {env : Env}
    {cx : FnCtx} {le : LEnv} {depth : Nat} {ls unwound : LS} {unit : Unit}
    {pt : Pt} {fr : Frame} {state : St} (related : Rel cfg env cx fr ls)
    (lowering : leaveTo depth le ls = (unit, unwound)) (point : ls.pp = some pt)
    (extension : ExtT unwound cx.fn.blocks) :
    FuelBoundAt sourceFuel targetFuel cx pt fr
      (fun _ => releaseScopes env (env.scopes.take (env.scopes.length - depth)))
      (fun _ _ pt' fr' => UnwindPost ls fr unwound fr'
        (env.scopes.drop (env.scopes.length - depth)) pt') state := by
  simp only [leaveTo, bind_run, get_apply] at lowering
  have stackPrefix : ls.stack.take (ls.stack.length - depth) =
      (env.scopes.take (env.scopes.length - depth)).map Prod.fst := by
    rw [related.stack, List.length_map, List.map_take]
  rw [stackPrefix] at lowering
  exact leaveAll_fuelBoundAt related.slots related.act (by
    rw [related.scopes, List.take_append_drop]) lowering point extension

private theorem FuelBoundAt.of_reflectAtPure {sourceFuel fuel : Nat} {cx : FnCtx}
    {pt : Pt} {fr : Frame} {value : α} {post : α → St → Pt → Frame → Prop}
    {state : St}
    (reflection : ReflectAtFuel fuel cx pt fr (fun _ => pure value) post state) :
    FuelBoundAt sourceFuel fuel cx pt fr (fun _ => pure value) post state := by
  intro result final done
  rcases reflection result final done with success | stopped
  · obtain ⟨_, sourceValue, after, pt', fr', residual, sourceRun, matched, bound, targetRun⟩ := success
    change Res.ok value state = Res.ok sourceValue after at sourceRun
    cases sourceRun
    exact Or.inl ⟨value, state, pt', fr', residual, rfl, matched, bound, targetRun⟩
  · obtain ⟨_, stop, after, sourceRun, resultEq⟩ := stopped
    change Res.ok value state = Res.stop stop after at sourceRun
    cases sourceRun

def TypedPrintArgsFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (args : List PrintArg) : Prop :=
  ∀ residual, residual ≤ fuel → ∀ expression, .expr expression ∈ args →
    TypedExprFuelBound sourceFuel residual cfg results expression

private theorem fuelBoundPrintEvalOutput {cfg : Cfg} {env : Env} {expression : Expr}
    {state after : St} {sourceFuel : Nat} {value : Val}
    (source : ExprSource cfg env expression state)
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

theorem typedPrintArgsFuelBound {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {env : Env} {args : List PrintArg} {state : St}
    (expressions : TypedPrintArgsFuelBound sourceFuel fuel cfg results args)
    (sources : ∀ n, PrintSourceCursor (cfg := cfg) env n results args state)
    {ls after : LS} {parts : List PrintPart} {pt : Pt} {cx : FnCtx} {fr : Frame}
    (lowering : lowerPrintArgs args (lowerEnv cfg.mod env.vars results) ls = (parts, after))
    (point : ls.pp = some pt) (extension : ExtT after cx.fn.blocks)
    (related : Rel cfg env cx fr ls) (moduleEq : cx.cfg.mod = lower cfg.mod)
    (resultsEq : cx.fn.results = results) (generated : GeneratedBuilderState ls) :
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => mapList (execPrintArg (n + 1) cfg env) args)
      (fun strings _ pt' fr' => ∃ cells, Post cfg env cx ls fr after fr' pt' cells ∧
        (∀ id ∈ partsIds parts, ∃ value, (id, value) ∈ cells) ∧ PartsRender fr' parts strings) state := by
  induction args generalizing fuel state ls after parts pt cx fr with
  | nil =>
      simp only [lowerPrintArgs, pure_run] at lowering
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj lowering
      simp only [mapList]
      exact FuelBoundAt.ret ⟨[], Post.init related point, by simp [partsIds], trivial⟩
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
          have tailExpressions : TypedPrintArgsFuelBound sourceFuel fuel cfg results args := by
            intro residual bound expression member
            exact expressions residual bound expression (by simp [member])
          have tailBound := ih tailExpressions tailSources tailRun point extension related
            moduleEq resultsEq generated
          have outputBound : FuelBoundAt sourceFuel fuel cx pt fr
              (fun n => mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                pure (text :: strings))
              (fun strings _ pt' fr' => ∃ cells,
                Post cfg env cx ls fr middle fr' pt' cells ∧
                (∀ id ∈ partsIds (.text text :: suffix), ∃ value, (id, value) ∈ cells) ∧
                PartsRender fr' (.text text :: suffix) strings) state := by
            refine tailBound.bind ?_
            intro strings next pt' fr' done matched residual residualBound
            obtain ⟨cells, post, ids, rendered⟩ := matched
            exact FuelBoundAt.ret ⟨cells, post, by simpa [partsIds] using ids,
              ⟨rfl, rendered⟩⟩
          have sourceEq :
              (mapList (execPrintArg (sourceFuel + 1) cfg env) (.text text :: args) state) =
                ((mapList (execPrintArg (sourceFuel + 1) cfg env) args >>= fun strings =>
                  pure (text :: strings)) state) := by
            simp only [mapList, execPrintArg, pure_bind]
          exact outputBound.of_source sourceEq
      | expr expression =>
          simp only [lowerPrintArgs, bind_eq] at lowering
          obtain ⟨id, middle, expressionRun, suffix, final, tailRun, finished⟩ := lowering
          rw [pure_run] at finished
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj finished
          have middleExtension : ExtT middle cx.fn.blocks :=
            extension.of_adv (advB_lowerPrintArgs args _ _ _ _ tailRun)
          cases cursor : sources sourceFuel with
          | expr headSource printable headMetadata headResume =>
              have headBound := expressions fuel (Nat.le_refl _) expression (by simp)
                env state headSource headMetadata ls middle id pt cx fr expressionRun point
                middleExtension related moduleEq resultsEq generated
              have composition : FuelBoundAt sourceFuel fuel cx pt fr
                  (fun n => evalExpr n cfg env expression >>= fun value =>
                    render value >>= fun part =>
                      mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                        pure (part :: strings))
                  (fun strings _ pt' fr' => ∃ cells,
                    Post cfg env cx ls fr final fr' pt' cells ∧
                    (∀ target ∈ partsIds (.val id :: suffix), ∃ value, (target, value) ∈ cells) ∧
                    PartsRender fr' (.val id :: suffix) strings) state := by
                refine headBound.bind ?_
                intro value next pt1 fr1 done matched residual residualBound
                obtain ⟨part, renderPure, rendered, printDone⟩ :=
                  fuelBoundPrintEvalOutput headSource printable done
                have tailSources : ∀ n, PrintSourceCursor (cfg := cfg) env n results args next :=
                  PrintSourceCursor.resumeFamily sources printDone
                have tailExpressions :
                    TypedPrintArgsFuelBound sourceFuel residual cfg results args := by
                  intro remaining bound expression' member
                  exact expressions remaining (Nat.le_trans bound residualBound) expression'
                    (by simp [member])
                have tailBound := ih tailExpressions tailSources tailRun matched.pp extension
                  matched.rel moduleEq resultsEq (generated.lowerExpr expression expressionRun)
                have mappedTail : FuelBoundAt sourceFuel residual cx pt1 fr1
                    (fun n => mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
                      pure (part :: strings))
                    (fun strings _ pt' fr' => ∃ cells,
                      Post cfg env cx ls fr final fr' pt' cells ∧
                      (∀ target ∈ partsIds (.val id :: suffix), ∃ cell, (target, cell) ∈ cells) ∧
                      PartsRender fr' (.val id :: suffix) strings) next := by
                  refine tailBound.bind ?_
                  intro strings afterTail pt' fr' tailDone tailMatched lastFuel lastBound
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
                  exact FuelBoundAt.ret ⟨(id, .val value) :: cells, combinedPost,
                    combinedIds, combinedRender⟩
                have sourceEq :
                    ((render value >>= fun headString =>
                      mapList (execPrintArg (sourceFuel + 1) cfg env) args >>= fun strings =>
                        pure (headString :: strings)) next) =
                    ((mapList (execPrintArg (sourceFuel + 1) cfg env) args >>= fun strings =>
                      pure (part :: strings)) next) := by
                  rw [renderPure, pure_bind]
                exact mappedTail.of_source sourceEq
              have sourceEq :
                  (mapList (execPrintArg (sourceFuel + 1) cfg env) (.expr expression :: args) state) =
                    ((evalExpr sourceFuel cfg env expression >>= fun value =>
                      render value >>= fun part =>
                        mapList (execPrintArg (sourceFuel + 1) cfg env) args >>= fun strings =>
                          pure (part :: strings)) state) := by
                simp only [mapList, execPrintArg, bind_assoc]
              exact composition.of_source sourceEq

theorem typedStatementFuelBound_print {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {args : List PrintArg} {origin : OriginId}
    (expressions : TypedPrintArgsFuelBound sourceFuel fuel cfg results args) :
    TypedStatementFuelBound (sourceFuel + 2) fuel cfg results loop (.print args origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq
    resultsEq depth targets counter generated frames
  let sources : ∀ n, PrintSourceCursor (cfg := cfg) env n results args state := fun n =>
    source.printSourceCursor n metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨parts, middle, partsRun, emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitEffect emit)
  have arguments := typedPrintArgsFuelBound expressions sources partsRun entry middleExtension
    related moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx point fr
      (fun n => mapList (execPrintArg (n + 1) cfg env) args >>= fun strings =>
        Goose.Core.emit (String.join strings ++ "\n") >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine arguments.bind ?_
    intro strings next ptk frk done matched residual residualBound
    obtain ⟨cells, argumentPost, ids, rendered⟩ := matched
    let output := String.join strings ++ "\n"
    have effectEqual : execEff cx.fn frk (.print parts (some origin)) =
        (Goose.Core.emit output >>= fun _ => pure frk) := by
      simp only [execEff, mapList_renderPart_of rendered, pure_bind, output]
    cases residual with
    | zero => exact FuelBoundAt.zero sourceFuel cx ptk frk _ _ next
    | succ residual =>
        have effectBound := leaf_eff_fuelBoundAt (sourceFuel := sourceFuel) (fuel := residual)
          argumentPost emit extension effectEqual
          (source := fun _ => Goose.Core.emit output) (state := next)
        have completeEffect : FuelBoundAt sourceFuel (residual + 1) cx ptk frk
            (fun n => Goose.Core.emit output >>= fun _ => pure (Flow.normal .unit))
            (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') next := by
          refine effectBound.bind ?_
          intro _ afterEffect pt' fr' effectDone post remaining remainingBound
          exact FuelBoundAt.ret (Or.inl ⟨rfl, post⟩)
        exact completeEffect
  have sourceEq :
      (execStmt (sourceFuel + 2) cfg env (.print args origin) >>= prepareLoopFlow env loop) state =
        ((mapList (execPrintArg (sourceFuel + 1) cfg env) args >>= fun strings =>
          Goose.Core.emit (String.join strings ++ "\n") >>= fun _ => pure (Flow.normal .unit)) state) := by
    cases loop <;> simp only [execStmt, prepareLoopFlow, prepareReturn, prepareLoopExit,
      bind_assoc, pure_bind]
  exact composition.of_source sourceEq

theorem typedStatementFuelBound_abort {sourceFuel fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {message : String} {origin : OriginId} :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.abort message origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq
    resultsEq depth targets counter generated frames
  have termExtension := extension
  obtain ⟨_, _, _, instruction⟩ := emitTerm_facts lowering entry termExtension
  have sourceRun :
      (execStmt (sourceFuel + 1) cfg env (.abort message origin) >>= prepareLoopFlow env loop) state =
        .stop (.abort .userAbort origin) state := by
    simp only [execStmt, abortAt]
    rw [bind_apply]
    rfl
  exact FuelBoundAt.abortTerm instruction sourceRun

theorem typedStatementFuelBound_expr {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.expr expression origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq
    resultsEq depth targets counter generated frames
  obtain ⟨expressionSource, typing, roots⟩ := source.exprChild
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨id, middle, expressionRun, finish⟩ := lowering
  rw [pure_run] at finish
  obtain ⟨_, rfl⟩ := Prod.mk.inj finish
  have expressionBound := child env state expressionSource expressionMetadata ls middle id point cx fr
    expressionRun entry extension related moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx point fr
      (fun n => evalExpr n cfg env expression >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr middle loop flow pt' fr') state := by
    refine expressionBound.bind ?_
    intro value next pt' fr' done post residual residualBound
    exact FuelBoundAt.ret (Or.inl ⟨rfl, post.sub (by simp)⟩)
  have sourceEq :
      (execStmt (sourceFuel + 1) cfg env (.expr expression origin) >>= prepareLoopFlow env loop) state =
        (evalExpr sourceFuel cfg env expression >>= fun _ => pure (Flow.normal .unit)) state := by
    cases loop <;> simp only [execStmt, prepareLoopFlow, prepareReturn, prepareLoopExit,
      bind_assoc, pure_bind]
  exact composition.of_source sourceEq

theorem typedStatementFuelBound_clear {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {place : Place} {origin : OriginId}
    (placeChild : TypedPlaceFuelBound sourceFuel fuel cfg results place) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.clear place origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq
    resultsEq depth targets counter generated frames
  obtain ⟨child, _, typing, roots, _, _, _, _, _⟩ := source.clearChild
  have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitEffect emit)
  have first := placeChild env state child childMetadata ls middle address point cx fr placeRun entry
    middleExtension related moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx point fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        truncateLoc location 0 >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro location next pt' fr' placeDone placePost residual residualBound
    have addressCell := placePost.has (address, .val (.ref location)) (by simp)
    have equal : execEff cx.fn fr' (.clear address (some origin)) =
        truncateLoc location 0 >>= fun _ => pure fr' := by
      simp only [execEff, getVal_of addressCell, Goose.Core.expectRef, pure_bind]
    exact normalEffectFuelBoundAt (sourceFuel := sourceFuel) (fuel := residual)
      placePost emit extension equal (source := truncateLoc location 0) (loop := loop) (state := next)
  have sourceEq :
      (execStmt (sourceFuel + 1) cfg env (.clear place origin) >>= prepareLoopFlow env loop) state =
        (evalPlace sourceFuel cfg env place >>= fun location =>
          truncateLoc location 0 >>= fun _ => pure (Flow.normal .unit)) state := by
    cases loop <;> simp only [execStmt, prepareLoopFlow, prepareReturn, prepareLoopExit,
      bind_assoc, pure_bind]
  exact composition.of_source sourceEq

theorem typedStatementFuelBound_assign {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {place : Place} {expression : Expr} {origin : OriginId}
    (placeChild : TypedPlaceFuelBound sourceFuel fuel cfg results place)
    (expressionChild : TypedExprFuelBoundBelow sourceFuel fuel cfg results expression) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.assign place expression origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq resultsEq
    depth targets counter generated frames
  obtain ⟨destination, destinationTyping, destinationRoots, _, _, children⟩ := source.assignChildren
  have destinationMetadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [destinationTyping, destinationRoots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, valueId, last, expressionRun, emit⟩ := lowering
  have lastExtension := extension.of_adv (adv_emitEffect emit)
  have middleExtension := lastExtension.of_adv (advB_lowerExpr expression _ _ _ _ expressionRun)
  have first := placeChild env state destination destinationMetadata ls middle address point cx fr placeRun
    entry middleExtension related moduleEq resultsEq generated
  have middleGenerated := generated.lowerPlace place placeRun
  have composition : FuelBoundAt sourceFuel fuel cx point fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        evalExpr n cfg env expression >>= fun value =>
          writeLoc location value >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro location next pt1 fr1 placeDone placePost residual residualBound
    obtain ⟨child, childTyping, childRoots, _, _, _⟩ := children sourceFuel location next placeDone
    have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
      rw [childTyping, childRoots]
      exact metadata
    have second := expressionChild residual residualBound env next child childMetadata
      middle last valueId pt1 cx fr1 expressionRun placePost.pp lastExtension placePost.rel
      moduleEq resultsEq middleGenerated
    have continuation : FuelBoundAt sourceFuel residual cx pt1 fr1
        (fun n => evalExpr n cfg env expression >>= fun value =>
          writeLoc location value >>= fun _ => pure (Flow.normal .unit))
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') next := by
      refine second.bind ?_
      intro value final pt2 fr2 expressionDone expressionPost remaining remainingBound
      have combined := placePost.comp expressionPost
      have addressCell := combined.has (address, .val (.ref location)) (by simp)
      have valueCell := combined.has (valueId, .val value) (by simp)
      have equal : execEff cx.fn fr2 (.store address valueId (some origin)) =
          writeLoc location value >>= fun _ => pure fr2 := by
        simp only [execEff, getVal_of addressCell, getVal_of valueCell,
          Goose.Core.expectRef, pure_bind]
      exact normalEffectFuelBoundAt (sourceFuel := sourceFuel) (fuel := remaining)
        combined emit extension equal (source := writeLoc location value) (loop := loop)
        (state := final)
    exact continuation
  have sourceEq :
      (execStmt (sourceFuel + 1) cfg env (.assign place expression origin) >>= prepareLoopFlow env loop) state =
        (evalPlace sourceFuel cfg env place >>= fun location =>
          evalExpr sourceFuel cfg env expression >>= fun value =>
            writeLoc location value >>= fun _ => pure (Flow.normal .unit)) state := by
    cases loop <;> simp only [execStmt, prepareLoopFlow, prepareReturn, prepareLoopExit,
      bind_assoc, pure_bind]
  exact composition.of_source sourceEq

theorem typedStatementFuelBound_append {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {place : Place} {view : View} {origin : OriginId}
    (placeChild : TypedPlaceFuelBound sourceFuel fuel cfg results place)
    (viewChild : TypedViewFuelBoundBelow sourceFuel fuel cfg results view) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.append place view origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq resultsEq
    depth targets counter generated frames
  obtain ⟨destination, destinationTyping, destinationRoots, children⟩ := source.appendChildren
  have destinationMetadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [destinationTyping, destinationRoots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, viewId, last, viewRun, emit⟩ := lowering
  have lastExtension := extension.of_adv (adv_emitEffect emit)
  have middleExtension := lastExtension.of_adv (advB_lowerView view _ _ _ _ viewRun)
  have first := placeChild env state destination destinationMetadata ls middle address point cx fr placeRun
    entry middleExtension related moduleEq resultsEq generated
  have middleGenerated := generated.lowerPlace place placeRun
  have composition : FuelBoundAt sourceFuel fuel cx point fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        evalView n cfg env view >>= fun sourceView =>
          readRun sourceView >>= fun elements =>
            checkedAppendLoc location elements origin >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro location next pt1 fr1 placeDone placePost residual residualBound
    obtain ⟨viewSource, viewTyping, viewRoots⟩ := children sourceFuel location next placeDone
    have viewMetadata : SourceResults viewSource.typingEnv viewSource.rootsEnv results := by
      rw [viewTyping, viewRoots]
      exact metadata
    have second := viewChild residual residualBound env next viewSource viewMetadata
      middle last viewId pt1 cx fr1 viewRun placePost.pp lastExtension placePost.rel
      moduleEq resultsEq middleGenerated
    have composedView : FuelBoundAt sourceFuel residual cx pt1 fr1
        (fun n => evalView n cfg env view >>= fun sourceView =>
          readRun sourceView >>= fun elements =>
            checkedAppendLoc location elements origin >>= fun _ => pure (Flow.normal .unit))
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') next := by
      refine second.bind ?_
      intro sourceView final pt2 fr2 viewDone viewPost remaining remainingBound
      have combined := placePost.comp viewPost
      have addressCell := combined.has (address, .val (.ref location)) (by simp)
      have viewCell := combined.has (viewId, .view sourceView) (by simp)
      have equal : execEff cx.fn fr2 (.append address viewId (some origin)) =
          (readRun sourceView >>= fun elements => checkedAppendLoc location elements origin) >>=
            fun _ => pure fr2 := by
        simp only [execEff, getVal_of addressCell, getView_of viewCell, Goose.Core.expectRef,
          bind_assoc, pure_bind, Goose.Core.checkedAppendLoc, checkCapacityAtOrg,
          checkAppendCapacity, abortAtOrg, abortAt]
        rfl
      simpa only [bind_assoc] using normalEffectFuelBoundAt (sourceFuel := sourceFuel) (fuel := remaining)
        combined emit extension equal
        (source := readRun sourceView >>= fun elements => checkedAppendLoc location elements origin)
        (loop := loop) (state := final)
    exact composedView
  have sourceEq :
      (execStmt (sourceFuel + 1) cfg env (.append place view origin) >>= prepareLoopFlow env loop) state =
        (evalPlace sourceFuel cfg env place >>= fun location =>
          evalView sourceFuel cfg env view >>= fun sourceView =>
            readRun sourceView >>= fun elements =>
              checkedAppendLoc location elements origin >>= fun _ => pure (Flow.normal .unit)) state := by
    cases loop <;> simp only [execStmt, prepareLoopFlow, prepareReturn, prepareLoopExit,
      bind_assoc, pure_bind]
  exact composition.of_source sourceEq

theorem typedStatementFuelBound_exit {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.exit expression origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq
    resultsEq depth targets counter generated frames
  obtain ⟨expressionSource, integer, typing, roots, expressionType⟩ := source.exitChild
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨id, middle, expressionRun, terminated⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitTerm terminated)
  have first := child env state expressionSource expressionMetadata ls middle id point cx fr
    expressionRun entry middleExtension related moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx point fr
      (fun n => evalExpr n cfg env expression >>= fun value =>
        expectInt value >>= fun pair => M.stop (.exit pair.2) >>= prepareLoopFlow env loop)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro value next pt' fr' done matched residual residualBound
    have typed := (expressionSource.result sourceFuel value done).typed
    rw [expressionType] at typed
    obtain ⟨number, rfl, typed⟩ := Core.Sound.hasTy_int typed
    obtain ⟨_, _, _, instruction⟩ := emitTerm_facts terminated matched.pp extension
    have cell := matched.has (id, .val (.int integer number)) (by simp)
    have sourceRun :
        ((expectInt (.int integer number) >>= fun pair => M.stop (.exit pair.2)) >>=
          prepareLoopFlow env loop) next = .stop (.exit number) next := by
      simp [expectInt, bind_apply, M.stop]
    exact FuelBoundAt.exitTerm instruction cell sourceRun
  have sourceEq :
      (execStmt (sourceFuel + 1) cfg env (.exit expression origin) >>= prepareLoopFlow env loop) state =
        (evalExpr sourceFuel cfg env expression >>= fun value =>
          expectInt value >>= fun pair => M.stop (.exit pair.2) >>= prepareLoopFlow env loop) state := by
    simp only [execStmt, bind_assoc]
  exact composition.of_source sourceEq

theorem typedStatementFuelBound_assert {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.assertS expression origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq
    resultsEq depth targets counter generated frames
  obtain ⟨expressionSource, typing, roots, type⟩ := source.assertChild
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨conditionId, middle, expressionRun, branchRun⟩ := lowering
  have middleExtension := extension.of_adv (advB_assert_core conditionId origin _ _ _ _ branchRun)
  have first := child env state expressionSource expressionMetadata ls middle conditionId point cx fr
    expressionRun entry middleExtension related moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx point fr
      (fun n => evalExpr n cfg env expression >>= fun value =>
        expectBool value >>= fun selected =>
          (if selected then pure (Flow.normal .unit) else abortAt .assert origin) >>=
            prepareLoopFlow env loop)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro value next pt1 fr1 done matched residual residualBound
    have typed := (expressionSource.result sourceFuel value done).typed
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
        rw [emitTerm_run _ _ (show abortState.cur = some elseBlock by rw [elseState])] at abortRun
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
    have hstMiddle : middle.stack = ls.stack := matched.rel.stack.trans related.stack.symm
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
    have branchAt : instAt cx.fn pt1 = some (.term (.condbr conditionId thenBlock [] elseBlock [])) :=
      branchInstruction
    cases residual with
    | zero => exact FuelBoundAt.zero sourceFuel cx pt1 fr1 _ _ next
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
            have stopped := FuelBoundAt.abortTerm (sourceFuel := sourceFuel) (fuel := residual)
              (cx := cx) (pt := (elseBlock, 0)) (fr := fr1)
              (source := fun _ =>
                (if false then pure (Flow.normal .unit) else abortAt .assert origin) >>=
                  prepareLoopFlow env loop)
              (post := fun flow _ pt' fr' =>
                StatementLoopPost cfg env cx ls fr after loop flow pt' fr')
              (state := next) (kind := .assert) (origin := origin)
              targetAbortInstruction sourceRun
            exact FuelBoundAt.condbr_take0 branchAt conditionCell
              (by simpa only [Bool.false_eq_true, ↓reduceIte] using elseTargetAt)
              (by simpa only [Bool.false_eq_true, ↓reduceIte] using elseParameters)
              (by cases false <;> rfl) stopped
        | true =>
            have finalPost : StatementLoopPost cfg env cx ls fr after loop (.normal .unit)
                (thenBlock, 0) fr1 :=
              Or.inl ⟨rfl, Post.nil thenPoint (by rw [hvalsFinal]; exact matched.mono)
                matched.same (matched.rel.stack_eq (hstFinal.trans hstMiddle.symm))⟩
            have normal : FuelBoundAt sourceFuel residual cx (thenBlock, 0) fr1
                (fun _ => pure (Flow.normal .unit))
                (fun flow _ pt' fr' =>
                  StatementLoopPost cfg env cx ls fr after loop flow pt' fr') next :=
              FuelBoundAt.ret finalPost
            have branchSourceEq :
                (((if true then pure (Flow.normal .unit) else abortAt .assert origin) >>=
                  prepareLoopFlow env loop) next) =
                    ((pure (Flow.normal .unit) : M Flow) next) := by
              cases loop <;> simp [prepareLoopFlow, prepareReturn, prepareLoopExit]
            have selectedSource := normal.of_source
              (otherFuel := sourceFuel)
              (other := fun _ =>
                (if true then pure (Flow.normal .unit) else abortAt .assert origin) >>=
                  prepareLoopFlow env loop) branchSourceEq
            have selectedBranch := FuelBoundAt.condbr_take0 branchAt conditionCell
              (by simpa only [Bool.false_eq_true, ↓reduceIte] using thenTargetAt)
              (by simpa only [Bool.false_eq_true, ↓reduceIte] using thenParameters)
              (by cases true <;> rfl) selectedSource
            cases loop <;>
              simpa [expectBool, prepareLoopFlow, prepareReturn, prepareLoopExit] using selectedBranch
  have sourceEq :
      (execStmt (sourceFuel + 1) cfg env (.assertS expression origin) >>= prepareLoopFlow env loop) state =
        (evalExpr sourceFuel cfg env expression >>= fun value =>
          expectBool value >>= fun selected =>
            (if selected then pure (Flow.normal .unit) else abortAt .assert origin) >>=
              prepareLoopFlow env loop) state := by
    simp only [execStmt, bind_assoc]
  exact composition.of_source sourceEq

theorem typedStatementFuelBound_return_none {sourceFuel fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {origin : OriginId} :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.ret none origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq
    resultsEq depth targets counter generated frames
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨ids, middle, initial, unit, unwound, leave, term⟩ := lowering
  rw [pure_run] at initial
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj initial
  have unwindExtension := extension.of_adv (adv_emitTerm term)
  have clean := leaveTo_fuelBoundAt (sourceFuel := sourceFuel + 1) (targetFuel := fuel)
    (le := lowerEnv cfg.mod env.vars results) (state := state) related leave entry unwindExtension
  simp only [Nat.sub_zero, List.take_length, List.drop_length] at clean
  have composition : FuelBoundAt (sourceFuel + 1) fuel cx point fr
      (fun n => releaseScopes env env.scopes >>= fun _ => pure (Flow.ret .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine clean.bind ?_
    intro _ afterClean point' frame' cleanRun matched residual residualBound
    obtain ⟨_, _, _, terminator⟩ := emitTerm_facts term matched.pp extension
    have site : ReturnSite cx point' frame' .unit origin :=
      ⟨⟨[], terminator, Or.inl ⟨rfl, rfl⟩⟩, matched.scopes⟩
    exact FuelBoundAt.ret (Or.inr (Or.inl ⟨.unit, origin, rfl, site⟩))
  have sourceEq :
      (execStmt (sourceFuel + 1) cfg env (.ret none origin) >>= prepareLoopFlow env loop) state =
        ((releaseScopes env env.scopes >>= fun _ => pure (Flow.ret .unit)) state) := by
    rw [prepareLoopFlow_execStmt_return_none]
    simp [execStmt, prepareReturn, bind_assoc, pure_bind]
  exact composition.of_source sourceEq

theorem typedStatementFuelBound_break {sourceFuel fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {origin : OriginId} :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.brk origin) := by
  cases loop with
  | none =>
      intro env state source metadata loops ls after point cx fr lowering entry extension related
        moduleEq resultsEq depth targets counter generated frames
      have noLoop := loops.mp rfl
      have typed := source.typed
      simp only [tyStmt, noLoop, ite_true] at typed
      inv at typed
  | some loop =>
      intro env state source metadata loops ls after point cx fr lowering entry extension related
        moduleEq resultsEq depth targets counter generated frames
      have lowerRun := lowering
      simp only [lowerStmt, bind_eq] at lowering
      obtain ⟨unit, unwound, leave, term⟩ := lowering
      have unwindExtension := extension.of_adv (adv_emitTerm term)
      have clean := leaveTo_fuelBoundAt (sourceFuel := sourceFuel + 1) (targetFuel := fuel)
        (le := lowerEnv cfg.mod env.vars results) (state := state) related leave entry unwindExtension
      have sourceAdvance := advB_lowerStmt (some loop) (.brk origin)
        (lowerEnv cfg.mod env.vars results) ls () after lowerRun
      have finalFrames := frames.mono sourceAdvance.ext
      obtain ⟨builderBlock, builderAt, builderParams⟩ := finalFrames.1
      obtain ⟨targetBlock, targetAt, targetParams⟩ := extension.params builderAt
      have targetParameters : targetBlock.params = [] := targetParams.trans builderParams
      have composition : FuelBoundAt (sourceFuel + 1) fuel cx point fr
          (fun n => releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ =>
            pure Flow.brk)
          (fun flow _ pt' fr' =>
            StatementLoopPost cfg env cx ls fr after (some loop) flow pt' fr') state := by
        refine clean.bind ?_
        intro _ afterClean point' frame' cleanRun matched residual residualBound
        obtain ⟨_, _, _, branchInstruction⟩ := emitTerm_facts term matched.pp extension
        have branchPost : StatementLoopPost cfg env cx ls fr after (some loop) Flow.brk
            (loop.breakTo, 0) frame' := by
          refine Or.inr (Or.inr ⟨loop, rfl, Or.inl ⟨rfl, ?_⟩⟩)
          exact ⟨rfl, ⟨fun id bound => by rw [matched.values], matched.activation,
            matched.scopes, matched.depth⟩⟩
        cases residual with
        | zero =>
            exact FuelBoundAt.zero (sourceFuel + 1) cx point' frame'
              (fun _ => pure Flow.brk)
              (fun flow _ nextPoint nextFrame =>
                StatementLoopPost cfg env cx ls fr after (some loop) flow nextPoint nextFrame)
              afterClean
        | succ remaining =>
            exact FuelBoundAt.br0 branchInstruction targetAt targetParameters
              (FuelBoundAt.ret branchPost)
      have sourceEq :
          (execStmt (sourceFuel + 1) cfg env (.brk origin) >>= prepareLoopFlow env (some loop)) state =
            ((releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ =>
              pure Flow.brk) state) := by
        rw [prepareLoopFlow_execStmt_break]
        simp [execStmt, prepareLoopExit, pure_bind]
      exact composition.of_source sourceEq

theorem typedStatementFuelBound_continue {sourceFuel fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {origin : OriginId} :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.cont origin) := by
  cases loop with
  | none =>
      intro env state source metadata loops ls after point cx fr lowering entry extension related
        moduleEq resultsEq depth targets counter generated frames
      have noLoop := loops.mp rfl
      have typed := source.typed
      simp only [tyStmt, noLoop, ite_true] at typed
      inv at typed
  | some loop =>
      intro env state source metadata loops ls after point cx fr lowering entry extension related
        moduleEq resultsEq depth targets counter generated frames
      have lowerRun := lowering
      have sourceAdvance := advB_lowerStmt (some loop) (.cont origin)
        (lowerEnv cfg.mod env.vars results) ls () after lowerRun
      have finalFrames := frames.mono sourceAdvance.ext
      cases kind : loop.cont with
      | jump header =>
          simp only [lowerStmt, kind, bind_eq] at lowering
          obtain ⟨unit, unwound, leave, term⟩ := lowering
          have unwindExtension := extension.of_adv (adv_emitTerm term)
          have clean := leaveTo_fuelBoundAt (sourceFuel := sourceFuel + 1) (targetFuel := fuel)
            (le := lowerEnv cfg.mod env.vars results) (state := state) related leave entry unwindExtension
          simp only [LoopBuilderFrames, kind] at finalFrames
          obtain ⟨_, builderAt, builderParams⟩ := finalFrames.2
          obtain ⟨targetBlock, targetAt, targetParams⟩ := extension.params builderAt
          have targetParameters : targetBlock.params = [] := targetParams.trans builderParams
          have composition : FuelBoundAt (sourceFuel + 1) fuel cx point fr
              (fun n => releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ =>
                pure Flow.cont)
              (fun flow _ pt' fr' =>
                StatementLoopPost cfg env cx ls fr after (some loop) flow pt' fr') state := by
            refine clean.bind ?_
            intro _ afterClean point' frame' cleanRun matched residual residualBound
            obtain ⟨_, _, _, branchInstruction⟩ := emitTerm_facts term matched.pp extension
            have branchPost : StatementLoopPost cfg env cx ls fr after (some loop) Flow.cont
                (header, 0) frame' := by
              refine Or.inr (Or.inr ⟨loop, rfl, Or.inr ⟨rfl, ?_⟩⟩)
              rw [ContinuedAt, kind]
              exact ⟨rfl, ⟨fun id bound => by rw [matched.values], matched.activation,
                matched.scopes, matched.depth⟩⟩
            cases residual with
            | zero =>
                exact FuelBoundAt.zero (sourceFuel + 1) cx point' frame'
                  (fun _ => pure Flow.cont)
                  (fun flow _ nextPoint nextFrame =>
                    StatementLoopPost cfg env cx ls fr after (some loop) flow nextPoint nextFrame)
                  afterClean
            | succ remaining =>
                exact FuelBoundAt.br0 branchInstruction targetAt targetParameters
                  (FuelBoundAt.ret branchPost)
          have sourceEq :
              (execStmt (sourceFuel + 1) cfg env (.cont origin) >>= prepareLoopFlow env (some loop)) state =
                ((releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ =>
                  pure Flow.cont) state) := by
            rw [prepareLoopFlow_execStmt_continue]
            simp [execStmt, prepareLoopExit, pure_bind]
          exact composition.of_source sourceEq
      | next header hint counterId =>
          simp only [lowerStmt, kind, bind_eq] at lowering
          obtain ⟨unit, unwound, leave, nextValue, advanced, nextRun, term⟩ := lowering
          have advancedExtension := extension.of_adv (adv_emitTerm term)
          have unwindExtension := advancedExtension.of_adv (adv_emitDef nextRun)
          have clean := leaveTo_fuelBoundAt (sourceFuel := sourceFuel + 1) (targetFuel := fuel)
            (le := lowerEnv cfg.mod env.vars results) (state := state) related leave entry unwindExtension
          simp only [LoopCounterAt, kind] at counter
          obtain ⟨counterBound, runtimeTy, current, counterCell⟩ := counter
          simp only [LoopBuilderFrames, kind] at finalFrames
          obtain ⟨_, builderAt, builderParams⟩ := finalFrames.2
          obtain ⟨targetBlock, targetAt, targetParams⟩ := extension.params builderAt
          have targetParameters : targetBlock.params = [(counterId, .data (.int hint))] :=
            targetParams.trans builderParams
          have composition : FuelBoundAt (sourceFuel + 1) fuel cx point fr
              (fun n => releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ =>
                pure Flow.cont)
              (fun flow _ pt' fr' =>
                StatementLoopPost cfg env cx ls fr after (some loop) flow pt' fr') state := by
            refine clean.bind ?_
            intro _ afterClean point' frame' cleanRun matched residual residualBound
            obtain ⟨nextId, _, _, nextPoint, nextInstruction⟩ :=
              emitDef_facts nextRun matched.pp advancedExtension
            obtain ⟨_, _, _, branchInstruction⟩ := emitTerm_facts term nextPoint extension
            have counterAfterCleanup : frame'.vals[counterId]? = some (.val (.int runtimeTy current)) := by
              rw [matched.values]
              exact counterCell
            have nextPure : execPure cx frame' (.next hint counterId) =
                pure (.val (.int runtimeTy (current + 1))) := by
              simp [execPure, getVal_of counterAfterCleanup, expectInt]
            let inject : Unit → RVal := fun _ => .val (.int runtimeTy (current + 1))
            have nextCell := Frame.set_get frame' nextValue (.val (.int runtimeTy (current + 1)))
            let nextFrame := frame'.set nextValue (.val (.int runtimeTy (current + 1)))
            let headerFrame := nextFrame.set counterId (.val (.int runtimeTy (current + 1)))
            have counterNext : counterId < nextValue := by
              rw [nextId, matched.builderValues]
              exact counterBound
            have sameCleanup : Same counterId fr frame' := by
              intro value bound
              rw [matched.values]
            have sameNext : Same counterId frame' nextFrame :=
              Same.set frame' (Nat.le_of_lt counterNext) _
            have sameHeader : Same counterId nextFrame headerFrame :=
              Same.set nextFrame (Nat.le_refl _) _
            have continued : ContinuedAt loop fr ls.vals.size
                (env.scopes.drop (env.scopes.length - loop.depth)) (header, 0) headerFrame := by
              apply NextJumpPost.continuedAt kind counterCell
              exact ⟨rfl, sameCleanup.trans
                (sameNext.trans sameHeader (Nat.le_refl _)) (Nat.le_refl _), Frame.set_get _ _ _,
                matched.activation, matched.scopes, matched.depth⟩
            have branchPost : StatementLoopPost cfg env cx ls fr after (some loop) Flow.cont
                (header, 0) headerFrame :=
              Or.inr (Or.inr ⟨loop, rfl, Or.inr ⟨rfl, continued⟩⟩)
            cases residual with
            | zero =>
                exact FuelBoundAt.zero (sourceFuel + 1) cx point' frame'
                  (fun _ => pure Flow.cont)
                  (fun flow _ nextPoint nextFrame =>
                    StatementLoopPost cfg env cx ls fr after (some loop) flow nextPoint nextFrame)
                  afterClean
            | succ branchFuel =>
                cases branchFuel with
                | zero =>
                    intro result final run
                    have timeoutRun : runAt cx point' frame' 1 afterClean =
                        .stop .timeout afterClean := by
                      simp [runAt, instsAt_cons nextInstruction, exec, execOp, nextPure, setCell_eq]
                      rfl
                    have resultTimeout : result = .stop .timeout afterClean := by
                      rw [← run]
                      exact timeoutRun
                    exact (final afterClean resultTimeout).elim
                | succ remaining =>
                    let sourceOp : Nat → M Unit := fun _ => pure ()
                    have operationAt : FuelBoundM (sourceFuel + 1) (remaining + 1)
                        (fun n => sourceOp n >>= fun value => pure (inject value))
                        (fun n => execOp n cx frame' (.next hint counterId)) afterClean := by
                      intro result final operationRun
                      have targetOp : execOp (remaining + 1) cx frame' (.next hint counterId) =
                          fun opState => .ok (.val (.int runtimeTy (current + 1))) opState := by
                        funext opState
                        simp [execOp, nextPure, pure_apply]
                      change execOp (remaining + 1) cx frame' (.next hint counterId) afterClean = result
                        at operationRun
                      rw [targetOp] at operationRun
                      have sourceRun :
                          (sourceOp (sourceFuel + 1) >>= fun value => pure (inject value)) afterClean =
                            .ok (.val (.int runtimeTy (current + 1))) afterClean := by
                        simp [sourceOp, inject, pure_apply]
                      exact sourceRun.trans operationRun
                    have first := FuelBoundAt.def_step (sourceFuel := sourceFuel + 1)
                      (targetFuel := remaining + 1) (source := sourceOp) (inject := inject)
                      nextInstruction operationAt
                    have sequence : FuelBoundAt (sourceFuel + 1) (remaining + 2) cx point' frame'
                        (fun n => sourceOp n >>= fun _ => pure Flow.cont)
                        (fun flow _ pt' fr' =>
                          StatementLoopPost cfg env cx ls fr after (some loop) flow pt' fr') afterClean := by
                      refine first.bind ?_
                      intro _ afterOp nextPoint' nextFrame' sourceDone nextMatched nextResidual nextBound
                      rcases nextMatched with ⟨pointEq, frameEq⟩
                      subst nextPoint'
                      subst nextFrame'
                      cases nextResidual with
                      | zero =>
                          exact FuelBoundAt.zero (sourceFuel + 1) cx
                            (point'.1, point'.2 + 1)
                            (frame'.set nextValue (.val (.int runtimeTy (current + 1))))
                            (fun _ => pure Flow.cont)
                            (fun flow _ pt'' fr'' =>
                              StatementLoopPost cfg env cx ls fr after (some loop) flow pt'' fr'')
                            afterOp
                      | succ branchResidual =>
                          exact FuelBoundAt.br1 branchInstruction targetAt targetParameters nextCell
                            (by simpa [headerFrame, nextFrame] using
                              (FuelBoundAt.ret branchPost : FuelBoundAt (sourceFuel + 1) branchResidual
                                cx (header, 0) headerFrame (fun _ => pure Flow.cont)
                                (fun flow _ pt' fr' =>
                                  StatementLoopPost cfg env cx ls fr after (some loop) flow pt' fr') afterOp))
                    have sourceEq :
                        ((fun _ : Nat => (pure Flow.cont : M Flow)) (sourceFuel + 1)) afterClean =
                          ((sourceOp (sourceFuel + 1) >>= fun _ => pure Flow.cont) afterClean) := by
                      simp [sourceOp, M.bind', M.pure']
                    exact sequence.of_source sourceEq
          have sourceEq :
              (execStmt (sourceFuel + 1) cfg env (.cont origin) >>= prepareLoopFlow env (some loop)) state =
                ((releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ =>
                  pure Flow.cont) state) := by
            rw [prepareLoopFlow_execStmt_continue]
            simp [execStmt, prepareLoopExit, pure_bind]
          exact composition.of_source sourceEq

theorem typedStatementFuelBound_return_some {sourceFuel fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.ret (some expression) origin) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension related moduleEq
    resultsEq depth targets counter generated frames
  obtain ⟨expressionSource, implementation, target, implementationEq, declaration, typingEq, rootsEq,
    passable⟩ := source.retChild
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact metadata
  have expressionImplementation : expressionSource.typingEnv.impl = some implementation := by
    rw [typingEq]
    exact implementationEq
  have resultsOne : results = [target] := by
    obtain ⟨_, resultsEqImpl⟩ := expressionMetadata implementation expressionImplementation
    rw [resultsEqImpl, declaration]
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨id, middle, expressionRun, coerced, casted, castRun, ids, idsEq, idsRun,
    unit, unwound, leave, term⟩ := lowering
  have castLower : coerceTo target id origin (lowerEnv cfg.mod env.vars results) middle =
      (coerced, casted) := by
    simpa only [coerceResult, bind_run, read_apply, lowerEnv, resultsOne, List.head?_cons]
      using castRun
  rw [pure_run] at idsRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj idsRun
  have unwindExtension := extension.of_adv (adv_emitTerm term)
  have castExtension := unwindExtension.of_adv
    (advB_leaveTo 0 (lowerEnv cfg.mod env.vars results) casted unit unwound leave)
  have expressionExtension := castExtension.of_adv
    (advB_coerceResult id origin (lowerEnv cfg.mod env.vars results) middle coerced casted castRun)
  have expressionBound := child env state expressionSource expressionMetadata ls middle id point cx fr
    expressionRun entry expressionExtension related moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx point fr
      (fun n => evalExpr n cfg env expression >>= fun value =>
        (pure value : M Val) >>= fun result =>
          releaseScopes env env.scopes >>= fun _ => pure (Flow.ret result))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine expressionBound.bind ?_
    intro value nextState expressionPoint expressionFrame expressionDone expressionPost residual residualBound
    have sourceResult := expressionSource.result sourceFuel value expressionDone
    have shape := sourceResult.coercionValue passable
    have coercionReflection := coerceTo_reflectAtFuel (fuel := residual) (state := nextState)
      expressionPost shape castLower castExtension
    have coercion := FuelBoundAt.of_reflectAtPure (sourceFuel := sourceFuel) coercionReflection
    have continuation : FuelBoundAt sourceFuel residual cx expressionPoint expressionFrame
        (fun n => (pure value : M Val) >>= fun result =>
          releaseScopes env env.scopes >>= fun _ => pure (Flow.ret result))
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') nextState := by
      refine coercion.bind ?_
      intro coercedValue castState castPoint castFrame castDone castMatched remaining remainingBound
      rcases castMatched with ⟨rfl, castPost⟩
      have cleanup := leaveTo_fuelBoundAt (sourceFuel := sourceFuel) (targetFuel := remaining)
        (le := lowerEnv cfg.mod env.vars results) (state := castState) castPost.rel leave
        castPost.pp unwindExtension
      simp only [Nat.sub_zero, List.take_length, List.drop_length] at cleanup
      have finish : FuelBoundAt sourceFuel remaining cx castPoint castFrame
          (fun n => releaseScopes env env.scopes >>= fun _ => pure (Flow.ret coercedValue))
          (fun flow _ pt' fr' =>
            StatementLoopPost cfg env cx ls fr after loop flow pt' fr') castState := by
        refine cleanup.bind ?_
        intro _ cleanState cleanPoint cleanFrame cleanDone cleanMatched finalFuel finalBound
        obtain ⟨_, _, _, terminator⟩ := emitTerm_facts term cleanMatched.pp extension
        have resultCell : cleanFrame.vals[coerced]? = some (.val coercedValue) := by
          rw [cleanMatched.values]
          exact castPost.has (coerced, .val coercedValue) (by simp)
        have site : ReturnSite cx cleanPoint cleanFrame coercedValue origin :=
          ⟨⟨[coerced], terminator, Or.inr ⟨coerced, rfl, resultCell⟩⟩, cleanMatched.scopes⟩
        exact FuelBoundAt.ret (Or.inr (Or.inl ⟨coercedValue, origin, rfl, site⟩))
      exact finish
    exact continuation
  have sourceEq :
      (execStmt (sourceFuel + 1) cfg env (.ret (some expression) origin) >>= prepareLoopFlow env loop) state =
        ((evalExpr sourceFuel cfg env expression >>= fun value =>
          (pure value : M Val) >>= fun result =>
            releaseScopes env env.scopes >>= fun _ => pure (Flow.ret result)) state) := by
    rw [prepareLoopFlow_execStmt_return_some]
    simp [execStmt, prepareReturn, bind_assoc, pure_bind]
  exact composition.of_source sourceEq

end Goose.Lower
