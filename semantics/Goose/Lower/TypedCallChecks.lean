import Goose.Lower.TypedCall
import Goose.Lower.TypedExpressionChecks

namespace Goose.Lower.TypedCallChecks

open Goose.Core Goose.GIR Goose.Proofs.Lower

private theorem emptyBlock_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {scope : ScopeId}
    {pre : List (SlotId × ValueId × OriginId)} {pre' : List (VarId × Val)} {le : LEnv}
    {ls ls' : LS} {r : ValueId} {pt : Pt} {fr : GIR.Frame}
    (hscope : ∀ item ∈ pre, ∃ lv, env.vars[item.1]? = some lv ∧ lv.scope = scope)
    (hlow : lowerBlock none pre false (.mk scope [] none) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hpre : PreRel fr pre pre') :
    SimG cx pt fr (execBlock 2 cfg env pre' (.mk scope [] none))
      (BlockFlowPost cfg env cx ls fr ls' (.mk scope [] none) false r) := by
  obtain ⟨entered, initialized, statements, valued, left, u0, u1, result,
    henter, hinit, hstatements, hvalue, hleave, hfinal, hresult⟩ := prefixBlock_unfold hlow
  simp only [lowerStmts, pure_run] at hstatements
  obtain ⟨_, rfl⟩ := Prod.mk.inj hstatements
  simp only [lowerBlockValue, ite_false, pure_run] at hvalue
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hvalue
  have hextLeft : ExtT left cx.fn.blocks := by simpa [hfinal, ExtT] using hext
  have hextInitialized : ExtT initialized cx.fn.blocks := hextLeft.of_adv (adv_emitEffect hleave)
  have hextEntered : ExtT { entered with stack := scope :: entered.stack } cx.fn.blocks :=
    hextInitialized.of_adv (advB_initSlots pre _ _ _ _ hinit)
  have hextBeforeStack : ExtT entered cx.fn.blocks := by simpa [ExtT] using hextEntered
  rw [execBlock_pre]
  simp only [prefixCoreBlock, execStmts, pure_bind, valueFlow]
  refine SimG.bind (block_enter hpp henter hextBeforeStack hrel)
    fun scopeInst pt1 fr1 ⟨hpp1, hsize1, hvals1, hrel1⟩ => ?_
  let inner : Env := { env with scopes := (scope, scopeInst) :: env.scopes }
  have hpre1 : PreRel fr1 pre pre' := PreRel.ext hvals1 hpre
  refine SimG.bind (initSlots_sim (env := inner) rfl pre pre' hscope hinit hpp1
    hextInitialized hrel1 hpre1) fun _ pt2 fr2 ⟨hpp2, hfr2, hstack2, hvals2⟩ => ?_
  subst fr2
  have hrel2 : Rel cfg inner cx fr1 initialized := hrel1.stack_eq hstack2
  refine SimG.bind (block_leave hpp2 hleave hextLeft hrel2)
    fun _ pt3 fr3 ⟨hpp3, hsize3, hvals3, hrel3⟩ => ?_
  have hrelFinal : Rel cfg env cx fr3 ls' := by simpa [hfinal] using hrel3
  have hppFinal : ls'.pp = some pt3 := by simpa [hfinal, LS.pp] using hpp3
  have hsizeFinal : ls'.vals.size = initialized.vals.size := by simpa [hfinal] using hsize3
  exact SimG.ret (Or.inl ⟨.unit, rfl, fun _ => rfl, by
    simp only [blockCells, Bool.false_eq_true, Bool.or_self, ite_false]
    exact (Post.init hrel2 hpp2).rescope (by simpa [hvals2] using hsize1) hvals1
      hppFinal hsizeFinal hvals3 hrelFinal⟩)

open TypedExpressionChecks in
theorem parameterized_body (profile : NumProfile) (depth : Nat) (values : List Val) (state : St)
    (hp : boolCallee.params.size = values.length) :
    CalleeBodyAt 2 ⟨profile, sourceModule⟩ 1 boolCallee depth values state := by
  let le := lowerEnv sourceModule boolCallee.vars boolCallee.results.toList
  let body := lowerBlock none (callPre boolCallee) false boolCallee.body le (callEntry boolCallee)
  let cx : FnCtx := ⟨⟨profile, lower sourceModule⟩, lowerImplAt sourceModule 1 boolCallee⟩
  have hextTail : ExtT (bodyTail boolCallee le body.1 body.2) cx.fn.blocks := by
    rw [lowerImplAt_call_blocks]
    exact extT_finish _
  have hextBody : ExtT body.2 cx.fn.blocks := hextTail.of_adv
    (advB_finishFunction boolCallee body.1 le body.2
      (finishFunction boolCallee body.1 le body.2).1 (bodyTail boolCallee le body.1 body.2) rfl)
  unfold CalleeBodyAt
  apply SimEAt.of_simG
  exact emptyBlock_sim (le := le) (callPre_scopes (m := sourceModule) (impl := boolCallee) (by cbv))
    rfl (callEntry_pp boolCallee) hextBody
    (callFrame_rel sourceModule profile 1 boolCallee state.nextAct (depth + 1) values)
    (callFrame_preRel boolCallee state.nextAct (depth + 1) values hp)

open TypedExpressionChecks in
theorem parameterized_call (profile : NumProfile) (depth : Nat) (state : St) :
    EventualM (enterCall 3 ⟨profile, sourceModule⟩ depth 1 [.bool true, .bool false])
      (fun fuel => callFn fuel ⟨profile, lower sourceModule⟩ depth 1 [.bool true, .bool false]) state :=
  typedCall_of_body (m := sourceModule) (c := 1) (ctx := ⟨1, "bools", [], [], []⟩)
    (impl := boolCallee) rfl rfl profile 2 depth _ state (parameterized_body profile depth _ state)

open TypedExpressionChecks in
#guard [NumProfile.release, .debug].all fun profile =>
  match enterCall 3 ⟨profile, sourceModule⟩ 4 1 [.bool true, .bool false] St.initial,
      callFn 20 ⟨profile, lower sourceModule⟩ 4 1 [.bool true, .bool false] St.initial with
  | .ok .unit coreState, .ok .unit girState =>
    coreState.trace == girState.trace && coreState.nextAct == girState.nextAct &&
      coreState.nextScope == girState.nextScope &&
      coreState.store.roots.isEmpty && girState.store.roots.isEmpty
  | _, _ => false

def readonlyArguments : List Arg := [.byRef .readOnly (.global 0), .byVal (.bool true)]

def readonlyCallee : Impl :=
  { name := "readonly", params := #[⟨0, .byRef⟩, ⟨1, .byValue⟩], results := #[.bool],
    vars := #[⟨"reference", .ref .readOnly .bool, .immutable, 0, 0⟩,
      ⟨"branch", .bool, .immutable, 0, 0⟩],
    body := .mk 0 [] (some (.bool true)), summary := .known ⟨[], [], [], [], [], false, false⟩ }

def readonlyContext : Context := ⟨1, "readonly", [(0, [.param 0])], [[]], []⟩

def readonlyModule (artifact : ArtifactProfile) : Core.Module :=
  { files := #["readonly-call.goose"], types := #[.bool, .ref .readOnly .bool],
    globals := #[⟨"flag", .bool, .mutable, .bool true, 0⟩,
      ⟨"selected", .bool, .mutable, .call 1 readonlyArguments 0, 0⟩],
    impls := #[initImpl, readonlyCallee], contexts := #[initContext, readonlyContext],
    entry := 0, origins := #[⟨0, 1, "global"⟩], profile := artifact }

def readonlyPrefixState : St :=
  { St.initial with nextAct := 1, store := Store.empty.introduce (.global 0) (.bool true) }

theorem readonly_prefix_actual (artifact : ArtifactProfile) (profile : NumProfile) :
    initGlobals 1 ⟨profile, readonlyModule artifact⟩ [0] St.initial =
      .ok () readonlyPrefixState := by
  simp [Core.initGlobals, lookupGlobal, readonlyModule, freshAct, evalExpr, bindRoot,
    readonlyPrefixState, St.initial, bind_apply, pure_apply]

theorem readonly_arguments_actual (artifact : ArtifactProfile) (profile : NumProfile) :
    mapList (evalArg 3 ⟨profile, readonlyModule artifact⟩ ⟨#[], 1, [], 0⟩)
      readonlyArguments { readonlyPrefixState with nextAct := 2 } =
      .ok [.ref ⟨.global 0, []⟩, .bool true] { readonlyPrefixState with nextAct := 2 } := by
  simp [readonlyArguments, mapList, evalArg, evalPlace, evalExpr, bind_apply, pure_apply]

theorem readonly_initialized_prefix (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (readonlyModule artifact) = .ok ()) :
    InitializedGlobals (readonlyModule artifact) 1 readonlyPrefixState :=
  InitializedGlobals.afterInitializer (cfg := ⟨profile, readonlyModule artifact⟩)
    (before := St.initial) (after := { St.initial with nextAct := 1 }) (value := .bool true)
    (g := 0) (global := ⟨"flag", .bool, .mutable, .bool true, 0⟩)
    accepted rfl (InitializedGlobals.initial _) 1 (by simp [evalExpr, pure_apply, St.initial])

theorem readonly_argument_source (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (readonlyModule artifact) = .ok ()) :
    ∃ source : ArgsSource 3 ⟨profile, readonlyModule artifact⟩ ⟨#[], 1, [], 0⟩
      readonlyArguments { readonlyPrefixState with nextAct := 2 }, source.resultsMatch [.bool] := by
  obtain ⟨source, typingEq, rootsEq, typeEq, countEq⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, readonlyModule artifact⟩) (state := readonlyPrefixState) (g := 1)
    (global := ⟨"selected", .bool, .mutable, .call 1 readonlyArguments 0, 0⟩)
    accepted rfl (readonly_initialized_prefix artifact profile accepted).invariant
  apply source.callArgs
  intro impl himpl
  rw [typingEq] at himpl
  cases himpl

theorem readonly_arguments_lower (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedArgsClaim 3 ⟨profile, readonlyModule artifact⟩ [.bool] readonlyArguments := by
  apply typedArgsClaim
  intro argument member
  simp [readonlyArguments] at member
  rcases member with rfl | rfl
  · exact typedArgClaim_byRef (typedPlaceClaim_global 2 _ _ 0) .readOnly
  · exact typedArgClaim_byVal (typedExprClaim_bool 2 _ _ true)

theorem readonly_call_lower (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 4 ⟨profile, readonlyModule artifact⟩ [.bool] (.call 1 readonlyArguments 0) := by
  apply typedExprClaim_call_of_blocks (readonly_arguments_lower artifact profile)
  intro ctx impl hcontext himplementation pre
  have hctx : ctx = readonlyContext := by simpa [readonlyModule] using hcontext.symm
  subst ctx
  have himpl : impl = readonlyCallee := by
    simpa [readonlyModule, readonlyContext] using himplementation.symm
  subst impl
  exact typedBlockLoopSimulation_succ 1 _ _ none (callPre readonlyCallee) pre false 0 []
    (some (.bool true)) (typedStatementsLoopSimulation_nil 1 _ _ none)
    (typedExprClaim_bool 1 _ _ true)

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := readonlyModule artifact
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := readonlyModule artifact
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 80 profile source, GIR.run 160 profile (lower source) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

#guard (lowerArgs readonlyArguments (lowerEnv (readonlyModule .pilot) #[] [.bool])
  { blocks := #[⟨[], #[]⟩], vals := #[], cur := some 0, stack := [] }).1 == [1, 2]

#guard
  let args : List ValueId × LS := lowerArgs readonlyArguments (lowerEnv (readonlyModule .pilot) #[] [.bool])
    { blocks := #[⟨[], #[]⟩], vals := #[], cur := some 0, stack := [] }
  match args.2.blocks[0]? with
  | some block =>
    match block.insts.toList with
    | [.def 0 (.globalAddr 0), .def 1 (.refFreeze 0), .def 2 (.constBool true)] => true
    | _ => false
  | none => false

theorem readonly_call_one (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 1 ⟨profile, readonlyModule artifact⟩ [.bool] (.call 1 readonlyArguments 0) :=
  typedExprClaim_call_one _ _ _ _ _

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [NumProfile.release, .debug].all fun profile =>
  match evalExpr 1 ⟨profile, readonlyModule artifact⟩ ⟨#[], 1, [], 0⟩ (.call 1 readonlyArguments 0)
      { readonlyPrefixState with nextAct := 2 } with
  | .stop .timeout state => state.nextAct == 2 && state.nextScope == 0 && state.trace == ""
  | _ => false

end Goose.Lower.TypedCallChecks
