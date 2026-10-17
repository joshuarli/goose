import Goose.Core.Sound.ArgumentRootReplay

namespace Goose.Core.Sound
open Goose.Core

private def TargetGlobals (m : Module) (targets : List Target) : Prop :=
  ∀ g, Target.global g ∈ targets → g < m.globals.size

private def EffectGlobals (m : Module) (effect : Eff) : Prop :=
  TargetGlobals m effect.reads ∧ TargetGlobals m effect.writes ∧
  TargetGlobals m effect.grows ∧ TargetGlobals m effect.shrinks ∧ TargetGlobals m effect.rebinds

private def PGlobals (m : Module) (action : P α) : Prop :=
  ∀ before output after, action before = .ok (output, after) →
    EffectGlobals m before.eff → EffectGlobals m after.eff

private theorem targetGlobals_addTargets {m : Module} {old added : List Target}
    (hold : TargetGlobals m old) (hadded : TargetGlobals m added) :
    TargetGlobals m (addTargets old added) := by
  induction added generalizing old with
  | nil => simpa [addTargets] using hold
  | cons target rest ih =>
    simp only [addTargets, List.foldl_cons]
    apply ih
    · split
      · exact hold
      · intro g member
        rcases List.mem_append.1 member with prior | fresh
        · exact hold g prior
        · have equal : Target.global g = target := List.mem_singleton.1 fresh
          exact hadded g (by simp [← equal])
    · intro g member
      exact hadded g (List.mem_cons_of_mem target member)

private theorem pGlobals_pure (m : Module) (value : α) : PGlobals m (pure value : P α) := by
  intro before output after replay valid
  have equal := (st_pure_ok value before (output, after)).1 replay
  cases equal
  exact valid

private theorem pGlobals_lift (m : Module) (value : V α) : PGlobals m (liftV value) := by
  intro before output after replay valid
  obtain ⟨_, equal⟩ := (liftV_ok _ _ _).1 replay
  cases equal
  exact valid

private theorem pGlobals_get (m : Module) : PGlobals m (get : P RState) := by
  intro before output after replay valid
  have equal := (st_get_ok before (output, after)).1 replay
  cases equal
  exact valid

private theorem pGlobals_modify (m : Module) (update : RState → RState)
    (preserves : ∀ state, EffectGlobals m state.eff → EffectGlobals m (update state).eff) :
    PGlobals m (modify update : P PUnit) := by
  intro before output after replay valid
  have equal := (st_modify_ok update before (output, after)).1 replay
  cases equal
  exact preserves before valid

private theorem pGlobals_bind {m : Module} {action : P α} {next : α → P β}
    (head : PGlobals m action)
    (tail : ∀ before value middle, action before = .ok (value, middle) → PGlobals m (next value)) :
    PGlobals m (action >>= next) := by
  intro before output after replay valid
  obtain ⟨value, middle, hhead, htail⟩ := (st_bind_ok _ _ _ _).1 replay
  exact tail before value middle hhead middle output after htail (head before value middle hhead valid)

private theorem pGlobals_rej (m : Module) (rule : Rule) (message : String) :
    PGlobals m (rejP rule message : P α) := by
  intro before output after replay
  exact ((rejP_ok _ _ _ _).1 replay).elim

private theorem pGlobals_ite {m : Module} {condition : Prop} [Decidable condition]
    {yes no : P α} (hyes : PGlobals m yes) (hno : PGlobals m no) :
    PGlobals m (if condition then yes else no) := by
  by_cases choice : condition <;> simp [choice, hyes, hno]

private theorem pGlobals_reads {m : Module} {roots : List RootRef}
    (valid : TargetGlobals m (rootsTargets roots)) : PGlobals m (addReads roots) := by
  unfold addReads addRoots
  apply pGlobals_modify
  intro state hstate
  exact ⟨targetGlobals_addTargets hstate.1 valid, hstate.2⟩

private theorem pGlobals_writes {m : Module} {roots : List RootRef}
    (valid : TargetGlobals m (rootsTargets roots)) : PGlobals m (addWrites roots) := by
  unfold addWrites addRoots
  apply pGlobals_modify
  intro state hstate
  exact ⟨hstate.1, targetGlobals_addTargets hstate.2.1 valid, hstate.2.2⟩

private theorem pGlobals_grows {m : Module} {roots : List RootRef}
    (valid : TargetGlobals m (rootsTargets roots)) : PGlobals m (addGrows roots) := by
  unfold addGrows addRoots
  apply pGlobals_modify
  intro state hstate
  exact ⟨hstate.1, hstate.2.1, targetGlobals_addTargets hstate.2.2.1 valid, hstate.2.2.2⟩

private theorem pGlobals_shrinks {m : Module} {roots : List RootRef}
    (valid : TargetGlobals m (rootsTargets roots)) : PGlobals m (addShrinks roots) := by
  unfold addShrinks addRoots
  apply pGlobals_modify
  intro state hstate
  exact ⟨hstate.1, hstate.2.1, hstate.2.2.1,
    targetGlobals_addTargets hstate.2.2.2.1 valid, hstate.2.2.2.2⟩

private theorem summaryTargets_globals {m : Module} {impl : Impl} {what : String}
    {targets : List Target} (checked : checkSummaryTargets m impl what targets = .ok ()) :
    TargetGlobals m targets := by
  intro g member
  have check := (forAll_ok _ _).1 checked (.global g) member
  dsimp only at check
  split at check
  · assumption
  · inv at check

private theorem summary_globals {m : Module} {impl : Impl} {ctx : Context}
    {effect : Eff} {summary : Summary}
    (checked : checkSummary m impl ctx effect = .ok ())
    (known : impl.summary = .known summary) :
    TargetGlobals m summary.reads ∧ TargetGlobals m summary.writes ∧
    TargetGlobals m summary.grows ∧ TargetGlobals m summary.shrinks ∧
    TargetGlobals m summary.rebinds := by
  unfold checkSummary at checked
  simp only [known] at checked
  inv at checked
  obtain ⟨reads, writes, grows, shrinks, rebinds, _, _, _, _, _, _, _, _⟩ := checked
  exact ⟨summaryTargets_globals reads, summaryTargets_globals writes,
    summaryTargets_globals grows, summaryTargets_globals shrinks, summaryTargets_globals rebinds⟩

private theorem paramGlobals_globals {m : Module} {callee : Impl} {ctx : Context}
    (contextOk : CtxOk m callee ctx) (index : Nat) :
    TargetGlobals m (paramGlobals callee ctx index) := by
  unfold paramGlobals
  cases varAt : callee.vars[index]? <;> cases annotation : ctx.varRoots.find? (·.1 == index)
  all_goals try (solve | intro g member; simp at member)
  rename_i localVar row
  rcases row with ⟨annotationVar, annotationRoots⟩
  simp only [varAt, annotation]
  split
  · intro g member
    obtain ⟨reference, referenceIn, mapped⟩ := List.mem_filterMap.1 member
    cases reference with
    | «local» _ | param _ => simp at mapped
    | global found =>
      have equal : found = g := by simpa using mapped
      subst found
      have roots : (ctx.varRoots.find? (·.1 == index)).map (·.2) = some annotationRoots := by
        simp [annotation]
      obtain ⟨global, lookup⟩ :=
        checkAnnotationShape_rootDeclaration contextOk.annotationShape roots referenceIn
      exact (Array.getElem?_eq_some_iff.1 lookup).1
  · intro g member
    simp at member

private theorem mapCallTargets_globals {m : Module} {callee : Impl} {ctx : Context}
    {args : List (List RootRef)} {targets : List Target}
    (contextOk : CtxOk m callee ctx)
    (argumentGlobals : ∀ i : Nat, TargetGlobals m (rootsTargets (args[i]?.getD [])))
    (targetGlobals : TargetGlobals m targets) :
    TargetGlobals m (mapCallTargets callee ctx args targets) := by
  induction targets with
  | nil => intro g member; simp [mapCallTargets] at member
  | cons target rest ih =>
    have restGlobals : TargetGlobals m rest := by
      intro g member
      exact targetGlobals g (List.mem_cons_of_mem target member)
    have tailGlobals := ih restGlobals
    cases target with
    | global found =>
      intro g member
      simp only [mapCallTargets, List.mem_cons] at member
      rcases member with equal | member
      · exact targetGlobals g (List.mem_cons.2 (Or.inl equal))
      · exact tailGlobals g member
    | param i =>
      intro g member
      simp only [mapCallTargets, List.mem_append] at member
      rcases member with (argument | annotation) | later
      · exact argumentGlobals i g argument
      · exact paramGlobals_globals contextOk i g annotation
      · exact tailGlobals g later

private theorem argumentFlatten_globals {m : Module} {args : List (List RootRef)}
    (argumentGlobals : ∀ i : Nat, TargetGlobals m (rootsTargets (args[i]?.getD []))) :
    TargetGlobals m (rootsTargets args.flatten) := by
  induction args with
  | nil => intro g member; simp [rootsTargets] at member
  | cons roots rest ih =>
    have headGlobals : TargetGlobals m (rootsTargets roots) := by
      simpa only [List.getElem?_cons_zero, Option.getD_some] using argumentGlobals 0
    have tailGlobals : TargetGlobals m (rootsTargets rest.flatten) := ih (fun i => by
      simpa only [List.getElem?_cons_succ] using argumentGlobals (i + 1))
    intro g member
    simp only [List.flatten_cons, rootsTargets, List.filterMap_append, List.mem_append] at member
    rcases member with head | tail
    · exact headGlobals g head
    · exact tailGlobals g tail

private theorem callEffects_globals {m : Module} {callee : Impl} {ctx : Context}
    {args : List (List RootRef)} {before : Eff}
    (contextOk : CtxOk m callee ctx)
    (argumentGlobals : ∀ i : Nat, TargetGlobals m (rootsTargets (args[i]?.getD [])))
    (beforeGlobals : EffectGlobals m before) :
    EffectGlobals m (callEffects callee ctx args before) := by
  cases known : callee.summary with
  | unknown =>
    simp only [callEffects, known, EffectGlobals]
    exact ⟨beforeGlobals.1,
      targetGlobals_addTargets beforeGlobals.2.1 (argumentFlatten_globals argumentGlobals),
      beforeGlobals.2.2⟩
  | known summary =>
    obtain ⟨_, _, _, _, _, checked⟩ := contextOk.body
    obtain ⟨reads, writes, grows, shrinks, rebinds⟩ := summary_globals checked known
    simp only [callEffects, known, EffectGlobals]
    exact ⟨targetGlobals_addTargets beforeGlobals.1
        (mapCallTargets_globals contextOk argumentGlobals reads),
      targetGlobals_addTargets beforeGlobals.2.1
        (mapCallTargets_globals contextOk argumentGlobals writes),
      targetGlobals_addTargets beforeGlobals.2.2.1
        (mapCallTargets_globals contextOk argumentGlobals grows),
      targetGlobals_addTargets beforeGlobals.2.2.2.1
        (mapCallTargets_globals contextOk argumentGlobals shrinks),
      targetGlobals_addTargets beforeGlobals.2.2.2.2
        (mapCallTargets_globals contextOk argumentGlobals rebinds)⟩

private theorem pGlobals_call {m : Module} {penv : PEnv} {context : ContextId}
    {args : List (List RootRef)}
    (modP : penv.mod = m) (moduleOk : ModOk m)
    (argumentGlobals : ∀ i : Nat, TargetGlobals m (rootsTargets (args[i]?.getD []))) :
    PGlobals m (rpCall penv context args) := by
  intro before output after replay valid
  unfold rpCall at replay
  cases ctxAt : penv.mod.contexts[context]? with
  | none =>
    simp only [ctxAt] at replay
    exact ((rejP_ok _ _ _ _).1 replay).elim
  | some ctx =>
    simp only [ctxAt] at replay
    cases implAt : penv.mod.impls[ctx.impl]? with
    | none =>
      simp only [implAt] at replay
      exact ((rejP_ok _ _ _ _).1 replay).elim
    | some callee =>
      simp only [implAt] at replay
      obtain ⟨_, middle, checked, tail⟩ := (st_bind_ok _ _ _ _).1 replay
      obtain ⟨_, checkedState⟩ := (liftV_ok _ _ _).1 checked
      have middleEq : middle = before := checkedState
      subst middle
      obtain ⟨_, modified, update, result⟩ := (st_bind_ok _ _ _ _).1 tail
      have updatedState := (st_modify_ok _ _ _).1 update
      have modifiedEffect : modified.eff = callEffects callee ctx args before.eff := by
        exact congrArg (fun pair => pair.2.eff) updatedState
      obtain ⟨_, resultState⟩ := (liftV_ok _ _ _).1 result
      have afterEq : after = modified := resultState
      subst after
      obtain ⟨checkedCallee, checkedImpl, contextOk⟩ :=
        moduleOk.ctx context ctx (by simpa [modP] using ctxAt)
      have calleeEq : checkedCallee = callee :=
        Option.some.inj (checkedImpl.symm.trans (by simpa [modP] using implAt))
      subst checkedCallee
      rw [modifiedEffect]
      exact callEffects_globals contextOk argumentGlobals valid

private theorem globalStmt_tables (env : TEnv) (scope : Nat) (stmt : Stmt)
    (n n' : Nat) (env' : TEnv)
    (ht : tyStmt env scope stmt n = .ok (env', n')) :
    env'.mod = env.mod ∧ env'.vars = env.vars := by
  cases stmt with
  | resize owner size fill origin =>
    cases fill
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all
    all_goals try (split <;> simp_all)
  | ret value origin =>
    cases value
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all
    all_goals try (split <;> simp_all)
  | ifS condition yes no origin =>
    cases no
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all
    all_goals try (split <;> simp_all)
  | _ =>
    skip
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all
    all_goals try (split <;> simp_all)

private def PlaceTyped (penv : PEnv) (place : Place) : Prop :=
  ∃ tenv info n n', tenv.mod = penv.mod ∧ tenv.vars = penv.impl.vars ∧
    tyPlace tenv place n = .ok (info, n')
private def ViewTyped (penv : PEnv) (view : View) : Prop :=
  ∃ tenv info n n', tenv.mod = penv.mod ∧ tenv.vars = penv.impl.vars ∧
    tyView tenv view n = .ok (info, n')
private def ExprTyped (penv : PEnv) (expr : Expr) : Prop :=
  ∃ tenv ty n n', tenv.mod = penv.mod ∧ tenv.vars = penv.impl.vars ∧
    tyExpr tenv expr n = .ok (ty, n')
private def BoundTyped (penv : PEnv) (bound : Bound) : Prop :=
  ∃ tenv n n', tenv.mod = penv.mod ∧ tenv.vars = penv.impl.vars ∧
    tyBound tenv bound n = .ok ((), n')
private def StmtTyped (penv : PEnv) (stmt : Stmt) : Prop :=
  ∃ tenv inner scope n n', tenv.mod = penv.mod ∧ tenv.vars = penv.impl.vars ∧
    tyStmt tenv scope stmt n = .ok (inner, n')
private def BlockTyped (penv : PEnv) (block : Block) : Prop :=
  ∃ tenv ty n n', tenv.mod = penv.mod ∧ tenv.vars = penv.impl.vars ∧
    tyBlock tenv [] block n = .ok (ty, n')
private def ExprsTyped (penv : PEnv) (exprs : List Expr) : Prop :=
  ∀ expr, expr ∈ exprs → ExprTyped penv expr
private def ArgsTyped (penv : PEnv) (args : List Arg) : Prop :=
  ∀ arg, arg ∈ args → match arg with
    | .byVal expr => ExprTyped penv expr
    | .byRef _ place => PlaceTyped penv place
private def StmtsTyped (penv : PEnv) (stmts : List Stmt) : Prop :=
  ∀ stmt, stmt ∈ stmts → StmtTyped penv stmt
private def PrintsTyped (penv : PEnv) (args : List PrintArg) : Prop :=
  ∀ arg, arg ∈ args → match arg with
    | .text _ => True
    | .expr expr => ExprTyped penv expr

private theorem placeTyped_globals {m : Module} {penv : PEnv} {place : Place}
    {before after : RState} {roots : List RootRef}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : PlaceTyped penv place)
    (replay : rpPlace penv place before = .ok (roots, after)) :
    TargetGlobals m (rootsTargets roots) := by
  obtain ⟨tenv, info, n, n', modT, vars, htyped⟩ := typed
  exact tyPlace_replayGlobalIndex modT modP vars contextOk moduleOk htyped replay

private theorem viewTyped_globals {m : Module} {penv : PEnv} {view : View}
    {before after : RState} {roots : List RootRef}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : ViewTyped penv view)
    (replay : rpView penv view before = .ok (roots, after)) :
    TargetGlobals m (rootsTargets roots) := by
  obtain ⟨tenv, info, n, n', modT, vars, htyped⟩ := typed
  exact tyView_replayGlobalIndex modT modP vars contextOk moduleOk htyped replay

private theorem pGlobals_readRoots (m : Module) (penv : PEnv) (place : Place) :
    PGlobals m (readRoots penv place) := by
  intro before output after replay valid
  have same := (readRoots_ok penv place before (output, after) replay).1
  have afterEq : after = before := same
  simpa only [afterEq] using valid

private theorem pGlobals_noteAborts (m : Module) : PGlobals m noteAborts := by
  unfold noteAborts
  exact pGlobals_modify m _ (fun _ valid => valid)

private theorem pGlobals_noteOutputs (m : Module) : PGlobals m noteOutputs := by
  unfold noteOutputs
  exact pGlobals_modify m _ (fun _ valid => valid)

private theorem storeRebinds_globals (m : Module) (penv : PEnv) (place : Place) :
    TargetGlobals m (storeRebinds penv place) := by
  intro g member
  unfold storeRebinds at member
  cases holder : place.derefVar? with
  | none => simp [holder] at member
  | some x =>
    simp only [holder] at member
    split at member <;> simp at member

private theorem pGlobals_readVariable (m : Module) (penv : PEnv) (x : VarId) :
    PGlobals m (rpExpr penv (.read (.var x))) := by
  simp only [rpExpr, rpPlace]
  refine pGlobals_bind (pGlobals_pure m _) (fun _ roots _ hroot => ?_)
  have equal : roots = [.local x] := congrArg Prod.fst ((st_pure_ok _ _ _).1 hroot)
  subst roots
  refine pGlobals_bind (pGlobals_reads ?_) (fun _ _ _ _ => pGlobals_readRoots m penv _)
  intro g member
  simp [rootsTargets, rootTarget] at member

local syntax "collect_global_typing " ident : tactic
macro_rules
| `(tactic| collect_global_typing $h:ident) => do
  `(tactic|
    first
    | (have impossible := (rej_ok _ _ _ _).1 $h
       exact impossible.elim)
    | (rw [st_bind_ok] at $h:ident
       rcases $h:ident with ⟨head, middle, hhead, htail⟩
       collect_global_typing hhead
       collect_global_typing htail)
    | (rw [st_ite_ok] at $h:ident
       rcases $h:ident with ⟨condition, hbranch⟩ | ⟨condition, hbranch⟩
       all_goals collect_global_typing hbranch)
    | (split at $h:ident <;> collect_global_typing $h)
    | skip)

local syntax "make_global_typed" : tactic
macro_rules
| `(tactic| make_global_typed) => `(tactic| (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 6
    assumption
    all_goals simp_all only [exprEnv]))


private theorem exprsAs_typed {penv : PEnv} {tenv : TEnv} {element : Ty}
    {exprs : List Expr} {n n' : Nat}
    (modT : tenv.mod = penv.mod) (vars : tenv.vars = penv.impl.vars)
    (typed : tyExprsAs tenv element exprs n = .ok ((), n')) : ExprsTyped penv exprs := by
  induction exprs generalizing n with
  | nil => intro expr member; simp at member
  | cons expr rest ih =>
    simp only [tyExprsAs] at typed
    inv at typed
    obtain ⟨ty, next, hExpr, _, htail⟩ := typed
    intro found member
    rcases List.mem_cons.1 member with rfl | later
    · exact ⟨tenv, ty, n, next, modT, vars, hExpr⟩
    · exact ih htail found later

private theorem structExprs_typed {penv : PEnv} {tenv : TEnv} {types : List Ty}
    {exprs : List Expr} {n n' : Nat}
    (modT : tenv.mod = penv.mod) (vars : tenv.vars = penv.impl.vars)
    (typed : tyStructExprs tenv types exprs n = .ok ((), n')) : ExprsTyped penv exprs := by
  induction exprs generalizing types n with
  | nil => intro expr member; simp at member
  | cons expr rest ih =>
    cases types with
    | nil => simp only [tyStructExprs] at typed; inv at typed
    | cons ty types =>
      simp only [tyStructExprs] at typed
      inv at typed
      obtain ⟨headTy, next, hExpr, _, htail⟩ := typed
      intro found member
      rcases List.mem_cons.1 member with rfl | later
      · exact ⟨tenv, headTy, n, next, modT, vars, hExpr⟩
      · exact ih htail found later

private theorem args_checker_typed {penv : PEnv} {tenv : TEnv} {callee : Impl}
    {params : List Param} {args : List Arg} {n n' : Nat}
    (modT : tenv.mod = penv.mod) (vars : tenv.vars = penv.impl.vars)
    (lengths : params.length = args.length)
    (typed : tyArgs tenv callee params args n = .ok ((), n')) : ArgsTyped penv args := by
  induction args generalizing params n with
  | nil => intro arg member; simp at member
  | cons arg args ih =>
    cases params with
    | nil => simp at lengths
    | cons param params =>
      have tailLength : params.length = args.length := by simpa using lengths
      cases varAt : callee.vars[param.var]? with
      | none => cases arg <;> (simp only [tyArgs, varAt] at typed; inv at typed)
      | some lv =>
        cases arg with
        | byVal expr =>
          simp only [tyArgs, varAt] at typed
          inv at typed
          obtain ⟨_, exprTy, next, hExpr, _, htail⟩ := typed
          intro found member
          rcases List.mem_cons.1 member with rfl | later
          · exact ⟨tenv, exprTy, n, next, modT, vars, hExpr⟩
          · exact ih tailLength htail found later
        | byRef mode place =>
          simp only [tyArgs, varAt] at typed
          inv at typed
          obtain ⟨_, ty, binding, contents, next, hPlace, _, _, htail⟩ := typed
          have htail : tyArgs tenv callee params args next = .ok ((), n') := by
            rcases htail with ⟨_, _, _, htail⟩ | ⟨_, _, htail⟩ <;> exact htail
          intro found member
          rcases List.mem_cons.1 member with rfl | later
          · exact ⟨tenv, ⟨ty, binding, contents⟩, n, next, modT, vars, hPlace⟩
          · exact ih tailLength htail found later

private theorem stmts_checker_typed {penv : PEnv} {tenv inner : TEnv}
    {stmts : List Stmt} {scope n n' : Nat}
    (modT : tenv.mod = penv.mod) (vars : tenv.vars = penv.impl.vars)
    (typed : tyStmts tenv scope stmts n = .ok (inner, n')) : StmtsTyped penv stmts := by
  induction stmts generalizing tenv n with
  | nil => intro stmt member; simp at member
  | cons stmt rest ih =>
    simp only [tyStmts] at typed
    obtain ⟨middle, next, head, tail⟩ := (st_bind_ok _ _ _ _).1 typed
    obtain ⟨modEq, varsEq⟩ := globalStmt_tables tenv scope stmt n next middle head
    intro found member
    rcases List.mem_cons.1 member with rfl | later
    · exact ⟨tenv, middle, scope, n, next, modT, vars, head⟩
    · exact ih (modEq.trans modT) (varsEq.trans vars) tail found later

private theorem prints_checker_typed {penv : PEnv} {tenv : TEnv}
    {args : List PrintArg} {n n' : Nat}
    (modT : tenv.mod = penv.mod) (vars : tenv.vars = penv.impl.vars)
    (typed : tyPrintArgs tenv args n = .ok ((), n')) : PrintsTyped penv args := by
  induction args generalizing n with
  | nil => intro arg member; simp at member
  | cons arg rest ih =>
    cases arg with
    | text text =>
      intro found member
      rcases List.mem_cons.1 member with rfl | later
      · trivial
      · exact ih typed found later
    | expr expr =>
      simp only [tyPrintArgs] at typed
      obtain ⟨ty, next, head, tail⟩ := (st_bind_ok _ _ _ _).1 typed
      cases ty <;> try (solve | inv at tail)
      all_goals
        intro found member
        rcases List.mem_cons.1 member with rfl | later
        · exact ⟨tenv, _, n, next, modT, vars, head⟩
        · exact ih tail found later

local syntax "prove_global_effect " ident ident ident : tactic
set_option hygiene false in
macro_rules
| `(tactic| prove_global_effect $modP:ident $contextOk:ident $moduleOk:ident) => `(tactic|
    first
    | exact pGlobals_pure _ _
    | exact pGlobals_lift _ _
    | exact pGlobals_get _
    | exact pGlobals_noteAborts _
    | exact pGlobals_noteOutputs _
    | exact pGlobals_rej _ _ _
    | exact pGlobals_readRoots _ _ _
    | (apply pGlobals_reads
       first
       | (apply placeTyped_globals $modP $contextOk $moduleOk
          rotate_left
          assumption
          make_global_typed)
       | (apply viewTyped_globals $modP $contextOk $moduleOk
          rotate_left
          assumption
          make_global_typed))
    | (apply pGlobals_writes
       apply placeTyped_globals $modP $contextOk $moduleOk
       rotate_left
       assumption
       make_global_typed)
    | (apply pGlobals_grows
       apply placeTyped_globals $modP $contextOk $moduleOk
       rotate_left
       assumption
       make_global_typed)
    | (apply pGlobals_shrinks
       apply placeTyped_globals $modP $contextOk $moduleOk
       rotate_left
       assumption
       make_global_typed)
    | (apply placeGlobalEffect $modP $contextOk $moduleOk; make_global_typed)
    | (apply viewGlobalEffect $modP $contextOk $moduleOk; make_global_typed)
    | (apply exprGlobalEffect $modP $contextOk $moduleOk; make_global_typed)
    | (apply boundGlobalEffect $modP $contextOk $moduleOk
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
       rotate_left 5
       assumption
       all_goals simp_all only [exprEnv])
    | (apply exprsGlobalEffect $modP $contextOk $moduleOk
       first
       | (apply exprsAs_typed <;> assumption)
       | (apply structExprs_typed <;> assumption))
    | (apply blockGlobalEffect (by simpa only using $modP) (by simpa only using $contextOk) $moduleOk
       make_global_typed)
    | (refine pGlobals_bind ?_ (fun _ _ _ hhead => ?_)
       · prove_global_effect $modP $contextOk $moduleOk
       · prove_global_effect $modP $contextOk $moduleOk)
    | (refine pGlobals_ite ?_ ?_ <;> prove_global_effect $modP $contextOk $moduleOk)
    | (split <;> prove_global_effect $modP $contextOk $moduleOk)
    | (apply printsGlobalEffect $modP $contextOk $moduleOk
       apply prints_checker_typed <;> assumption)
    | (apply pGlobals_modify
       intro state valid
       first
       | exact valid
       | (refine ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1,
           targetGlobals_addTargets valid.2.2.2.2 ?_⟩
          first
          | exact storeRebinds_globals _ _ _
          | (intro g member; simp at member))))


set_option maxHeartbeats 3000000 in
mutual
private theorem placeGlobalEffect {m : Module} {penv : PEnv} {place : Place}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : PlaceTyped penv place) : PGlobals m (rpPlace penv place) := by
  obtain ⟨tenv, info, n, n', modT, vars, typed⟩ := typed
  cases place with
  | var _ | global _ => exact pGlobals_pure m _
  | deref expr =>
    cases shortcut : sliceRefTy tenv expr with
    | some ty =>
      obtain ⟨x, _, _, _, _, same, _⟩ := sliceRefTy_replayFacts shortcut
      subst expr
      exact pGlobals_readVariable m penv x
    | none =>
      simp only [tyPlace, shortcut] at typed
      collect_global_typing typed
      simp only [rpPlace]
      prove_global_effect modP contextOk moduleOk
  | elem view index origin =>
    simp only [tyPlace] at typed
    collect_global_typing typed
    simp only [rpPlace]
    prove_global_effect modP contextOk moduleOk
  | field owner field =>
    simp only [tyPlace] at typed
    collect_global_typing typed
    simp only [rpPlace]
    prove_global_effect modP contextOk moduleOk
termination_by sizeOf place

private theorem viewGlobalEffect {m : Module} {penv : PEnv} {view : View}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : ViewTyped penv view) : PGlobals m (rpView penv view) := by
  obtain ⟨tenv, info, n, n', modT, vars, typed⟩ := typed
  cases view <;> simp only [tyView] at typed
  all_goals collect_global_typing typed
  all_goals simp only [rpView]
  all_goals prove_global_effect modP contextOk moduleOk
termination_by sizeOf view

private theorem boundGlobalEffect {m : Module} {penv : PEnv} {bound : Bound}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : BoundTyped penv bound) : PGlobals m (rpBound penv bound) := by
  obtain ⟨tenv, n, n', modT, vars, typed⟩ := typed
  cases bound <;> simp only [tyBound] at typed
  all_goals collect_global_typing typed
  all_goals simp only [rpBound]
  all_goals prove_global_effect modP contextOk moduleOk
termination_by sizeOf bound

private theorem exprGlobalEffect {m : Module} {penv : PEnv} {expr : Expr}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : ExprTyped penv expr) : PGlobals m (rpExpr penv expr) := by
  obtain ⟨tenv, ty, n, n', modT, vars, typed⟩ := typed
  cases expr with
  | call context args origin =>
    simp only [tyExpr] at typed
    obtain ⟨_, start, _, checked⟩ := (st_bind_ok _ _ _ _).1 typed
    cases ctxAt : tenv.mod.contexts[context]? with
    | none => simp only [ctxAt] at checked; inv at checked
    | some ctx =>
      simp only [ctxAt] at checked
      cases calleeAt : tenv.mod.impls[ctx.impl]? with
      | none => simp only [calleeAt] at checked; inv at checked
      | some callee =>
        simp only [calleeAt] at checked
        by_cases lengths : callee.params.size = args.length
        · simp only [lengths, ↓reduceIte] at checked
          obtain ⟨_, next, argTyped, _⟩ := (st_bind_ok _ _ _ _).1 checked
          simp only [rpExpr]
          refine pGlobals_bind (argsGlobalEffect modP contextOk moduleOk
            (args_checker_typed modT vars (by simpa using lengths) argTyped))
            (fun before roots after replay => ?_)
          refine pGlobals_bind (pGlobals_lift m _) (fun _ _ _ _ => ?_)
          exact pGlobals_call modP moduleOk
            (tyArgs_replayGlobalIndex modT modP vars contextOk moduleOk
              lengths argTyped replay)
        · simp only [lengths, ↓reduceIte] at checked
          inv at checked
  | push owner arg origin =>
    cases profileEq : tenv.mod.profile <;> cases origin
    all_goals simp only [tyExpr, profileEq] at typed
    all_goals collect_global_typing typed
    all_goals try (solve | inv at typed)
    all_goals simp only [rpExpr]
    all_goals prove_global_effect modP contextOk moduleOk
  | arrLit type _ | fill type _ =>
    cases type
    all_goals simp only [tyExpr] at typed
    all_goals collect_global_typing typed
    all_goals try (solve | inv at typed)
    all_goals simp only [rpExpr]
    all_goals prove_global_effect modP contextOk moduleOk
  | _ =>
    simp only [tyExpr] at typed
    collect_global_typing typed
    all_goals try (solve | inv at typed)
    all_goals simp only [rpExpr]
    all_goals prove_global_effect modP contextOk moduleOk
termination_by sizeOf expr


private theorem blockGlobalEffect {m : Module} {penv : PEnv} {block : Block}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : BlockTyped penv block) : PGlobals m (rpBlockValue penv [] block) := by
  obtain ⟨tenv, ty, n, n', modT, vars, typed⟩ := typed
  obtain ⟨inner, next, _, hstmts, hvalue, modEq, varsEq, _, _⟩ :=
    tyBlock_innerVisible typed
  cases block with
  | mk scope stmts value =>
    have stmtsTyped : StmtsTyped {penv with scopes := scope :: penv.scopes} stmts :=
      stmts_checker_typed (by simpa only using modT) (by simpa only using vars) hstmts
    have innerMod : inner.mod = penv.mod := modEq.trans modT
    have innerVars : inner.vars = penv.impl.vars := varsEq.trans vars
    intro before output after replay valid
    rcases output with ⟨roots, range⟩
    obtain ⟨_, middle, stmtsReplay, valueReplay, _, _⟩ :=
      rpBlockValue_ok penv [] scope stmts value before roots range after replay
    have middleValid := stmtsGlobalEffect (penv := {penv with scopes := scope :: penv.scopes}) modP contextOk moduleOk stmtsTyped
      before () middle (by simpa using stmtsReplay) valid
    cases value with
    | none =>
      obtain ⟨_, rfl⟩ := valueReplay
      exact middleValid
    | some expr =>
      exact exprGlobalEffect (penv := {penv with scopes := scope :: penv.scopes})
        modP contextOk moduleOk
        ⟨inner, ty, next, n', innerMod, innerVars, hvalue⟩
        middle roots after valueReplay middleValid
termination_by sizeOf block
private theorem stmtGlobalEffect {m : Module} {penv : PEnv} {stmt : Stmt}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : StmtTyped penv stmt) : PGlobals m (rpStmt penv stmt) := by
  obtain ⟨tenv, inner, scope, n, n', modT, vars, typed⟩ := typed
  cases stmt with
  | resize owner size fill org =>
    cases fill <;> simp only [tyStmt] at typed
    all_goals collect_global_typing typed
    all_goals simp only [rpStmt]
    all_goals prove_global_effect modP contextOk moduleOk
  | ifS condition yes no org =>
    cases no <;> simp only [tyStmt] at typed
    all_goals collect_global_typing typed
    all_goals simp only [rpStmt]
    all_goals prove_global_effect modP contextOk moduleOk
  | ret value org =>
    cases value <;> simp only [tyStmt] at typed
    all_goals collect_global_typing typed
    all_goals simp only [rpStmt, checkResult]
    all_goals prove_global_effect modP contextOk moduleOk
  | assignWhole owner replacement org =>
    simp only [tyStmt] at typed
    obtain ⟨_, n1, _, tail⟩ := (st_bind_ok _ _ _ _).1 typed
    obtain ⟨_, n2, _, tail⟩ := (st_bind_ok _ _ _ _).1 tail
    obtain ⟨info, n3, hplace, tail⟩ := (st_bind_ok _ _ _ _).1 tail
    cases tyCase : info.ty <;> simp only [tyCase] at tail
    all_goals collect_global_typing tail
    all_goals simp only [rpStmt]
    all_goals prove_global_effect modP contextOk moduleOk
  | _ =>
    simp only [tyStmt] at typed
    collect_global_typing typed
    all_goals simp only [rpStmt, bindRoots, checkResult]
    all_goals prove_global_effect modP contextOk moduleOk
termination_by sizeOf stmt

private theorem exprsGlobalEffect {m : Module} {penv : PEnv} {exprs : List Expr}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : ExprsTyped penv exprs) : PGlobals m (rpExprs penv exprs) := by
  cases exprs with
  | nil => exact pGlobals_pure m ()
  | cons expr rest =>
    simp only [rpExprs]
    refine pGlobals_bind (exprGlobalEffect modP contextOk moduleOk
      (typed expr List.mem_cons_self)) (fun _ _ _ _ => ?_)
    exact exprsGlobalEffect modP contextOk moduleOk
      (fun found member => typed found (List.mem_cons_of_mem expr member))
termination_by sizeOf exprs

private theorem argsGlobalEffect {m : Module} {penv : PEnv} {args : List Arg}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : ArgsTyped penv args) : PGlobals m (rpArgs penv args) := by
  cases args with
  | nil => exact pGlobals_pure m []
  | cons arg rest =>
    have head := typed arg List.mem_cons_self
    have tail : ArgsTyped penv rest := fun found member =>
      typed found (List.mem_cons_of_mem arg member)
    cases arg with
    | byVal expr =>
      simp only [rpArgs]
      refine pGlobals_bind (exprGlobalEffect modP contextOk moduleOk head)
        (fun _ roots _ _ => ?_)
      exact pGlobals_bind (argsGlobalEffect modP contextOk moduleOk tail)
        (fun _ result _ _ => pGlobals_pure m (roots :: result))
    | byRef mode place =>
      simp only [rpArgs]
      refine pGlobals_bind (placeGlobalEffect modP contextOk moduleOk head)
        (fun _ roots _ _ => ?_)
      exact pGlobals_bind (argsGlobalEffect modP contextOk moduleOk tail)
        (fun _ result _ _ => pGlobals_pure m (roots :: result))
termination_by sizeOf args

private theorem stmtsGlobalEffect {m : Module} {penv : PEnv} {stmts : List Stmt}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : StmtsTyped penv stmts) : PGlobals m (rpStmts penv stmts) := by
  cases stmts with
  | nil => exact pGlobals_pure m ()
  | cons stmt rest =>
    simp only [rpStmts]
    refine pGlobals_bind (stmtGlobalEffect modP contextOk moduleOk
      (typed stmt List.mem_cons_self)) (fun _ _ _ _ => ?_)
    exact stmtsGlobalEffect modP contextOk moduleOk
      (fun found member => typed found (List.mem_cons_of_mem stmt member))
termination_by sizeOf stmts

private theorem printsGlobalEffect {m : Module} {penv : PEnv} {args : List PrintArg}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : PrintsTyped penv args) : PGlobals m (rpPrintArgs penv args) := by
  cases args with
  | nil => exact pGlobals_pure m ()
  | cons arg rest =>
    have head := typed arg List.mem_cons_self
    have tail : PrintsTyped penv rest := fun found member =>
      typed found (List.mem_cons_of_mem arg member)
    cases arg with
    | text text =>
      simp only [rpPrintArgs]
      exact printsGlobalEffect modP contextOk moduleOk tail
    | expr expr =>
      simp only [rpPrintArgs]
      exact pGlobals_bind (exprGlobalEffect modP contextOk moduleOk head)
        (fun _ _ _ _ => printsGlobalEffect modP contextOk moduleOk tail)
termination_by sizeOf args


end

/-- Every explicit global mutation target replayed for a checked context names a
module global, including targets charged to unknown calls' actual arguments. -/
theorem ContextEff.mutationGlobalIndex
    {m : Module} {impl : Impl} {ctx : Context} {effect : Eff}
    (contextEffect : ContextEff m impl ctx effect)
    (moduleOk : ModOk m) (implementationOk : ImplOk m impl) (contextOk : CtxOk m impl ctx)
    {global : GlobalId} (member : Target.global global ∈ effectMutationTargets effect) :
    global < m.globals.size := by
  obtain ⟨ty, next, typed, _⟩ := implementationOk.body
  obtain ⟨roots, range, after, replay, effectEq⟩ := contextEffect
  have emptyGlobals : EffectGlobals m ({} : Eff) := by
    repeat' constructor
    all_goals intro g member; simp at member
  have bounded := blockGlobalEffect (m := m) (penv := ⟨m, impl, ctx, []⟩)
    rfl contextOk moduleOk
    ⟨implEnv m impl, ty, impl.params.size, next, rfl, rfl, typed⟩
    ⟨impl.params.size, {}⟩ (roots, range) after replay emptyGlobals
  rw [effectEq] at bounded
  simp only [effectMutationTargets, List.mem_append] at member
  rcases member with ((writes | grows) | shrinks) | rebinds
  · exact bounded.2.1 global writes
  · exact bounded.2.2.1 global grows
  · exact bounded.2.2.2.1 global shrinks
  · exact bounded.2.2.2.2 global rebinds

end Goose.Core.Sound
