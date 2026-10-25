import Goose.Lower.ReflectionControl
import Goose.Lower.ReflectionBranchesSteps
import Goose.Lower.ReflectionEffects
import Goose.Lower.ReflectionTransfersCoercion

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private theorem ReflectAtFuel.goes {fuel : Nat} {cx : FnCtx} {pt pt' : Pt}
    {fr fr' : Frame} {source : Nat → M α} {post : α → St → Pt → Frame → Prop}
    {state : St} (movement : Goes cx pt fr pt' fr')
    (reflection : ReflectAtFuel fuel cx pt' fr' source post state) :
    ReflectAtFuel fuel cx pt fr source post state := by
  obtain ⟨cost, exact⟩ := movement
  intro result nonTimeout run
  have extended := runAt_fuel_mono (Nat.le_add_right fuel cost) cx pt fr state nonTimeout run
  rw [exact fuel] at extended
  exact reflection result nonTimeout extended

private theorem leaveAll_reflectAtFuel (cfg : Cfg) (env : Env) (cx : FnCtx)
    (entered suffix : List (ScopeId × ScopeInst)) (le : LEnv)
    (ls ls' : LS) (r : Unit) (pt : Pt) (fr : Frame)
    (slots : cx.fn.slots = env.vars.mapIdx fun i lv => ⟨lv.ty, lv.kind, lv.scope, i⟩)
    (activation : fr.act = env.act) (scopes : fr.scopes = entered ++ suffix)
    (lowering : leaveAll (entered.map Prod.fst) le ls = (r, ls'))
    (point : ls.pp = some pt) (extension : ExtT ls' cx.fn.blocks) (fuel : Nat) (state : St) :
    ReflectAtFuel fuel cx pt fr (fun _ => releaseScopes env entered)
      (fun _ _ pt' fr' => UnwindPost ls fr ls' fr' suffix pt') state := by
  induction entered generalizing ls ls' r pt fr fuel state with
  | nil =>
    simp only [List.map_nil, leaveAll, pure_run] at lowering
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj lowering
    exact ReflectAtFuel.ret fuel ⟨point, rfl, rfl, by simpa using scopes, rfl, rfl, rfl⟩
  | cons scope rest ih =>
    obtain ⟨scopeId, scopeInstance⟩ := scope
    cases fuel with
    | zero =>
      exact ReflectAtFuel.zero cx pt fr
        (fun _ => releaseScopes env ((scopeId, scopeInstance) :: rest))
        (fun _ _ nextPoint next => UnwindPost ls fr ls' next suffix nextPoint) state
    | succ fuel =>
      simp only [List.map_cons, leaveAll, bind_eq] at lowering
      obtain ⟨ignored, middle, leave, tail⟩ := lowering
      cases ignored
      have middleExtension := extension.of_adv
        (advB_leaveAll (rest.map Prod.fst) le middle () ls' tail)
      obtain ⟨_, stack, middlePoint, instruction⟩ := emitEffect_facts leave point middleExtension
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
      have first : ReflectAtFuel (fuel + 1) cx pt fr
          (fun _ => Core.releaseScope env scopeId scopeInstance)
          (fun _ _ nextPoint next => nextPoint = (pt.1, pt.2 + 1) ∧ next = nextFrame) state :=
        ReflectAtFuel.eff_step (fuel := fuel) (state := state)
          (source := fun _ => Core.releaseScope env scopeId scopeInstance)
          (nextFrame := fun _ => nextFrame) (sourceFuel := 0) instruction effectEqual
      have composition := first.bind
        (by
          intro n value after nextPoint next effectRun matched residual bound
          rcases matched with ⟨rfl, rfl⟩
          exact ih middle ls' r (pt.1, pt.2 + 1) nextFrame
            (by simpa [nextFrame] using activation) rfl tail middlePoint
            extension residual after)
        (fun n k bound => MonoM.refl _)
        (fun _ n k bound => MonoM.refl _)
      refine composition.mono ?_
      intro result after nextPoint next matched
      exact ⟨matched.pp, matched.values, matched.activation, matched.scopes, matched.depth,
        matched.builderValues.trans values, matched.lexicalStack.trans stack⟩

private theorem leaveTo_reflectAtFuel {fuel : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {le : LEnv} {depth : Nat} {ls unwound : LS} {unit : Unit} {pt : Pt} {fr : Frame}
    {state : St} (rel : Rel cfg env cx fr ls)
    (lowering : leaveTo depth le ls = (unit, unwound)) (point : ls.pp = some pt)
    (extension : ExtT unwound cx.fn.blocks) :
    ReflectAtFuel fuel cx pt fr (fun _ => releaseScopes env (env.scopes.take (env.scopes.length - depth)))
      (fun _ _ pt' fr' => UnwindPost ls fr unwound fr'
        (env.scopes.drop (env.scopes.length - depth)) pt') state := by
  simp only [leaveTo, bind_run, get_apply] at lowering
  have stackPrefix : ls.stack.take (ls.stack.length - depth) =
      (env.scopes.take (env.scopes.length - depth)).map Prod.fst := by
    rw [rel.stack, List.length_map, List.map_take]
  rw [stackPrefix] at lowering
  have result := leaveAll_reflectAtFuel cfg env cx
    (env.scopes.take (env.scopes.length - depth))
    (env.scopes.drop (env.scopes.length - depth)) le ls unwound unit pt fr rel.slots rel.act
    (by rw [rel.scopes, List.take_append_drop]) lowering point extension fuel state
  simpa only [List.map_take] using result

theorem typedStatementReflection_return_none {fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {org : OriginId} :
    TypedStatementReflection fuel cfg results loop (.ret none org) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension rel module resultsEq
    depth targets counter generated frames
  have lowerRun := lowering
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨ids, middle, initial, unit, unwound, leave, term⟩ := lowering
  rw [pure_run] at initial
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj initial
  have unwindExtension := extension.of_adv (adv_emitTerm term)
  have clean := leaveTo_reflectAtFuel (fuel := fuel) (le := lowerEnv cfg.mod env.vars results)
    (state := state) rel leave entry unwindExtension
  simp only [Nat.sub_zero, List.take_length, List.drop_length] at clean
  have composition : ReflectAtFuel fuel cx point fr
      (fun n => releaseScopes env env.scopes >>= fun _ => pure (Flow.ret .unit))
      (fun flow _ point' frame' => StatementLoopPost cfg env cx ls fr after loop flow point' frame') state := by
    refine clean.bind ?_ (fun n k bound => MonoM.refl _)
      (fun _ _ _ _ => MonoM.refl _)
    intro n _ afterClean point' frame' cleanRun matched residual bound
    obtain ⟨_, _, _, terminator⟩ := emitTerm_facts term matched.pp extension
    have site : ReturnSite cx point' frame' .unit org :=
      ⟨⟨[], terminator, Or.inl ⟨rfl, rfl⟩⟩, matched.scopes⟩
    exact ReflectAtFuel.ret residual (Or.inr (Or.inl ⟨.unit, org, rfl, site⟩))
  refine composition.of_source fun n => ⟨1, ?_⟩
  rw [prepareLoopFlow_execStmt_return_none]
  simp [execStmt, prepareReturn, bind_assoc, pure_bind]

theorem typedStatementReflection_return_some {fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    (child : TypedExprReflection fuel cfg results expr) :
    TypedStatementReflection fuel cfg results loop (.ret (some expr) org) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension rel module resultsEq
    depth targets counter generated frames
  obtain ⟨exprSource, implementation, target, implementationEq, declaration,
    typingEq, rootsEq, passable⟩ := source.retChild
  have exprMetadata : SourceResults exprSource.typingEnv exprSource.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact metadata
  have exprImplementationEq : exprSource.typingEnv.impl = some implementation := by
    rw [typingEq]
    exact implementationEq
  have resultsOne : results = [target] := by
    obtain ⟨_, resultsEqImpl⟩ := exprMetadata implementation exprImplementationEq
    rw [resultsEqImpl, declaration]
  have lowerRun := lowering
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨id, middle, expressionRun, coerced, casted, castRun, ids, idsEq, idsRun,
    unit, unwound, leave, term⟩ := lowering
  have castLower : coerceTo target id org (lowerEnv cfg.mod env.vars results) middle =
      (coerced, casted) := by
    simpa only [coerceResult, bind_run, read_apply, lowerEnv, resultsOne, List.head?_cons]
      using castRun
  rw [pure_run] at idsRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj idsRun
  have unwindExtension := extension.of_adv (adv_emitTerm term)
  have castExtension := unwindExtension.of_adv (advB_leaveTo 0
    (lowerEnv cfg.mod env.vars results) casted unit unwound leave)
  have expressionExtension := castExtension.of_adv
    (advB_coerceResult id org (lowerEnv cfg.mod env.vars results) middle coerced casted castRun)
  have exprReflection := child env state exprSource exprMetadata ls middle id point cx fr
    expressionRun entry expressionExtension rel module resultsEq generated
  have generatedAfter := generated.lowerStmt loop (.ret (some expr) org) frames.toTargets lowerRun
  have composition : ReflectAtFuel fuel cx point fr
      (fun n => evalExpr n cfg env expr >>= fun value =>
        (pure value : M Val) >>= fun result =>
          releaseScopes env env.scopes >>= fun _ => pure (Flow.ret result))
      (fun flow _ point' frame' => StatementLoopPost cfg env cx ls fr after loop flow point' frame') state := by
    refine exprReflection.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expr)
      (fun _ n k bound => MonoM.refl _)
    intro n value nextState pt' fr' expressionDone expressionPost residual residualBound
    have sourceResult := exprSource.result n value expressionDone
    have shape := sourceResult.coercionValue passable
    have coercion := coerceTo_reflectAtFuel (fuel := residual) (state := nextState)
      expressionPost shape castLower castExtension
    refine coercion.bind ?_ (fun n k bound => MonoM.refl _)
      (fun _ n k bound => MonoM.refl _)
    intro k coercedValue castState castPoint castFrame castDone castMatched remaining remainingBound
    rcases castMatched with ⟨rfl, castPost⟩
    have cleanup := leaveTo_reflectAtFuel (fuel := remaining) (state := castState)
      (le := lowerEnv cfg.mod env.vars results) castPost.rel leave castPost.pp unwindExtension
    simp only [Nat.sub_zero, List.take_length, List.drop_length] at cleanup
    have finish : ReflectAtFuel remaining cx castPoint castFrame
        (fun j => releaseScopes env env.scopes >>= fun _ => pure (Flow.ret coercedValue))
        (fun flow _ point' frame' => StatementLoopPost cfg env cx ls fr after loop flow point' frame')
        castState := by
      refine cleanup.bind ?_ (fun n k bound => MonoM.refl _)
        (fun _ n k bound => MonoM.refl _)
      intro j _ cleanState cleanPoint cleanFrame cleanDone cleanMatched finalFuel finalBound
      obtain ⟨_, _, _, terminator⟩ := emitTerm_facts term cleanMatched.pp extension
      have resultCell : cleanFrame.vals[coerced]? = some (.val coercedValue) := by
        rw [cleanMatched.values]
        exact castPost.has (coerced, .val coercedValue) (by simp)
      have site : ReturnSite cx cleanPoint cleanFrame coercedValue org :=
        ⟨⟨[coerced], terminator, Or.inr ⟨coerced, rfl, resultCell⟩⟩, cleanMatched.scopes⟩
      exact ReflectAtFuel.ret finalFuel (Or.inr (Or.inl ⟨coercedValue, org, rfl, site⟩))
    exact finish
  refine composition.of_source fun n => ⟨n + 1, ?_⟩
  rw [prepareLoopFlow_execStmt_return_some]
  simp [execStmt, prepareReturn, bind_assoc, pure_bind]

theorem typedStatementReflection_break {fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {org : OriginId} :
    TypedStatementReflection fuel cfg results loop (.brk org) := by
  cases loop with
  | none =>
    intro env state source metadata loops ls after point cx fr lowering entry extension rel module resultsEq
      depth targets counter generated frames
    have noLoop := loops.mp rfl
    have typed := source.typed
    simp only [tyStmt, noLoop, ite_true] at typed
    inv at typed
  | some loop =>
    intro env state source metadata loops ls after point cx fr lowering entry extension rel module resultsEq
      depth targets counter generated frames
    have lowerRun := lowering
    simp only [lowerStmt, bind_eq] at lowering
    obtain ⟨unit, unwound, leave, term⟩ := lowering
    have unwindExtension := extension.of_adv (adv_emitTerm term)
    have clean := leaveTo_reflectAtFuel (fuel := fuel) (le := lowerEnv cfg.mod env.vars results)
      (state := state) rel leave entry unwindExtension
    have sourceAdvance := advB_lowerStmt (some loop) (.brk org) (lowerEnv cfg.mod env.vars results)
      ls () after lowerRun
    have finalFrames := frames.mono sourceAdvance.ext
    have generatedAfter := generated.lowerStmt (some loop) (.brk org) frames.toTargets lowerRun
    obtain ⟨builderBlock, builderAt, builderParams⟩ := finalFrames.1
    obtain ⟨targetBlock, targetAt, targetParams⟩ := extension.params builderAt
    have targetParameters : targetBlock.params = [] := targetParams.trans builderParams
    have composition : ReflectAtFuel fuel cx point fr
        (fun n => releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ => pure Flow.brk)
        (fun flow _ point' frame' => StatementLoopPost cfg env cx ls fr after (some loop) flow point' frame') state := by
      refine clean.bind ?_ (fun n k bound => MonoM.refl _)
        (fun _ n k bound => MonoM.refl _)
      intro n _ afterClean point' frame' cleanRun matched residual bound
      obtain ⟨_, _, _, branchInstruction⟩ := emitTerm_facts term matched.pp extension
      have branchPost : StatementLoopPost cfg env cx ls fr after (some loop) Flow.brk
          (loop.breakTo, 0) frame' := by
        refine Or.inr (Or.inr ⟨loop, rfl, Or.inl ⟨rfl, ?_⟩⟩)
        exact ⟨rfl, ⟨fun id bound => by rw [matched.values], matched.activation,
          matched.scopes, matched.depth⟩⟩
      cases residual with
      | zero =>
        exact ReflectAtFuel.zero cx point' frame' (fun _ => pure Flow.brk)
          (fun flow _ nextPoint nextFrame =>
            StatementLoopPost cfg env cx ls fr after (some loop) flow nextPoint nextFrame) afterClean
      | succ remaining =>
        exact ReflectAtFuel.br0 branchInstruction targetAt targetParameters
          (ReflectAtFuel.ret remaining branchPost)
    refine composition.of_source fun n => ⟨1, ?_⟩
    rw [prepareLoopFlow_execStmt_break]
    simp [execStmt, prepareLoopExit, pure_bind]

theorem typedStatementReflection_continue {fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {org : OriginId} :
    TypedStatementReflection fuel cfg results loop (.cont org) := by
  cases loop with
  | none =>
    intro env state source metadata loops ls after point cx fr lowering entry extension rel module resultsEq
      depth targets counter generated frames
    have noLoop := loops.mp rfl
    have typed := source.typed
    simp only [tyStmt, noLoop, ite_true] at typed
    inv at typed
  | some loop =>
    intro env state source metadata loops ls after point cx fr lowering entry extension rel module resultsEq
      depth targets counter generated frames
    have lowerRun := lowering
    have sourceAdvance := advB_lowerStmt (some loop) (.cont org) (lowerEnv cfg.mod env.vars results)
      ls () after lowerRun
    have finalFrames := frames.mono sourceAdvance.ext
    have generatedAfter := generated.lowerStmt (some loop) (.cont org) frames.toTargets lowerRun
    cases kind : loop.cont with
    | jump header =>
      simp only [lowerStmt, kind, bind_eq] at lowering
      obtain ⟨unit, unwound, leave, term⟩ := lowering
      have unwindExtension := extension.of_adv (adv_emitTerm term)
      have clean := leaveTo_reflectAtFuel (fuel := fuel)
        (le := lowerEnv cfg.mod env.vars results) (state := state) rel leave entry unwindExtension
      simp only [LoopBuilderFrames, kind] at finalFrames
      obtain ⟨_, builderAt, builderParams⟩ := finalFrames.2
      obtain ⟨targetBlock, targetAt, targetParams⟩ := extension.params builderAt
      have targetParameters : targetBlock.params = [] := targetParams.trans builderParams
      have composition : ReflectAtFuel fuel cx point fr
          (fun n => releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ => pure Flow.cont)
          (fun flow _ point' frame' => StatementLoopPost cfg env cx ls fr after (some loop) flow point' frame') state := by
        refine clean.bind ?_ (fun n k bound => MonoM.refl _)
          (fun _ n k bound => MonoM.refl _)
        intro n _ afterClean point' frame' cleanRun matched residual bound
        obtain ⟨_, _, _, branchInstruction⟩ := emitTerm_facts term matched.pp extension
        have branchPost : StatementLoopPost cfg env cx ls fr after (some loop) Flow.cont
            (header, 0) frame' := by
          refine Or.inr (Or.inr ⟨loop, rfl, Or.inr ⟨rfl, ?_⟩⟩)
          rw [ContinuedAt, kind]
          exact ⟨rfl, ⟨fun id bound => by rw [matched.values], matched.activation,
            matched.scopes, matched.depth⟩⟩
        cases residual with
        | zero =>
          exact ReflectAtFuel.zero cx point' frame' (fun _ => pure Flow.cont)
            (fun flow _ nextPoint nextFrame =>
              StatementLoopPost cfg env cx ls fr after (some loop) flow nextPoint nextFrame) afterClean
        | succ remaining =>
          exact ReflectAtFuel.br0 branchInstruction targetAt targetParameters
            (ReflectAtFuel.ret remaining branchPost)
      refine composition.of_source fun n => ⟨1, ?_⟩
      rw [prepareLoopFlow_execStmt_continue]
      simp [execStmt, prepareLoopExit, pure_bind]
    | next header hint counterId =>
      simp only [lowerStmt, kind, bind_eq] at lowering
      obtain ⟨unit, unwound, leave, nextValue, advanced, nextRun, term⟩ := lowering
      have advancedExtension := extension.of_adv (adv_emitTerm term)
      have unwindExtension := advancedExtension.of_adv (adv_emitDef nextRun)
      have clean := leaveTo_reflectAtFuel (fuel := fuel)
        (le := lowerEnv cfg.mod env.vars results) (state := state) rel leave entry unwindExtension
      simp only [LoopCounterAt, kind] at counter
      obtain ⟨counterBound, runtimeTy, current, counterCell⟩ := counter
      simp only [LoopBuilderFrames, kind] at finalFrames
      obtain ⟨_, builderAt, builderParams⟩ := finalFrames.2
      obtain ⟨targetBlock, targetAt, targetParams⟩ := extension.params builderAt
      have targetParameters : targetBlock.params = [(counterId, .data (.int hint))] :=
        targetParams.trans builderParams
      have composition : ReflectAtFuel fuel cx point fr
          (fun n => releaseScopes env (env.scopes.take (env.scopes.length - loop.depth)) >>= fun _ => pure Flow.cont)
          (fun flow _ point' frame' => StatementLoopPost cfg env cx ls fr after (some loop) flow point' frame') state := by
        refine clean.bind ?_ (fun n k bound => MonoM.refl _)
          (fun _ n k bound => MonoM.refl _)
        intro n _ afterClean point' frame' cleanRun matched residual bound
        obtain ⟨nextId, _, _, nextPoint, nextInstruction⟩ :=
          emitDef_facts nextRun matched.pp advancedExtension
        obtain ⟨_, _, _, branchInstruction⟩ := emitTerm_facts term nextPoint extension
        have counterAfterCleanup : frame'.vals[counterId]? = some (.val (.int runtimeTy current)) := by
          rw [matched.values]
          exact counterCell
        have nextPure : execPure cx frame' (.next hint counterId) =
            pure (.val (.int runtimeTy (current + 1))) := by
          simp [execPure, getVal_of counterAfterCleanup, expectInt]
        have nextGoes := Goes.def_pure nextInstruction (by simp) nextPure
        have nextCell := Frame.set_get frame' nextValue (.val (.int runtimeTy (current + 1)))
        let nextFrame := frame'.set nextValue (.val (.int runtimeTy (current + 1)))
        let headerFrame := nextFrame.set counterId (.val (.int runtimeTy (current + 1)))
        have branchGoes := goes_br1 branchInstruction targetAt targetParameters nextCell
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
          exact ReflectAtFuel.zero cx point' frame' (fun _ => pure Flow.cont)
            (fun flow _ nextPoint nextFrame =>
              StatementLoopPost cfg env cx ls fr after (some loop) flow nextPoint nextFrame) afterClean
        | succ remaining =>
          cases remaining with
          | zero =>
            intro result nonTimeout run
            have timeoutRun : runAt cx point' frame' 1 afterClean = .stop .timeout afterClean := by
              simp [runAt, instsAt_cons nextInstruction, exec, execOp, nextPure, setCell_eq]
              rfl
            have resultTimeout : result = .stop .timeout afterClean := by
              rw [← run]
              exact timeoutRun
            exact (nonTimeout afterClean resultTimeout).elim
          | succ remaining =>
            have atHeader : ReflectAtFuel (remaining + 2) cx (header, 0) headerFrame
                (fun _ => pure Flow.cont)
                (fun flow _ nextPoint nextFrame =>
                  StatementLoopPost cfg env cx ls fr after (some loop) flow nextPoint nextFrame)
                afterClean := ReflectAtFuel.ret (remaining + 2) branchPost
            simpa [Nat.add_assoc] using ReflectAtFuel.goes (fuel := remaining + 2)
              (nextGoes.trans branchGoes) atHeader
      refine composition.of_source fun n => ⟨1, ?_⟩
      rw [prepareLoopFlow_execStmt_continue]
      simp [execStmt, prepareLoopExit, pure_bind]

end Goose.Lower
