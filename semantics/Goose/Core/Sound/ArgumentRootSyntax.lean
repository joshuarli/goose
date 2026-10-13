import Goose.Core.Sound.ArgumentRoots
import Goose.Core.Sound.AccessTyping
import Goose.Core.Sound.TypingVisibility

namespace Goose.Core.Sound
open Goose.Core

private theorem resultShape_forInMember {α : Type} (xs : List α)
    (f : α → V (ForInStep PUnit.{1}))
    (yielded : ∀ a step, f a = .ok step → step = .yield ⟨⟩)
    (checked : forIn (m := V) xs (PUnit.unit : PUnit.{1}) (fun a _ => f a) = .ok PUnit.unit) :
    ∀ a, a ∈ xs → f a = .ok (.yield ⟨⟩) := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, head, tail⟩ := (ex_bind_ok _ _ _).1 checked
    have equal := yielded a step head
    subst step
    intro b member
    rcases List.mem_cons.1 member with rfl | member
    · exact head
    · exact ih tail b member

private theorem resultShape_zipRightMember {α β : Type} (left : List α) (right : List β)
    (lengths : left.length = right.length) {b : β} (member : b ∈ right) :
    ∃ a, (a, b) ∈ left.zip right := by
  induction left generalizing right with
  | nil =>
    have empty : right = [] := List.length_eq_zero_iff.1 lengths.symm
    simp [empty] at member
  | cons a left ih =>
    cases right with
    | nil => simp at lengths
    | cons c right =>
      rcases List.mem_cons.1 member with rfl | member
      · exact ⟨a, by simp⟩
      · obtain ⟨a', pair⟩ := ih right (by simpa using lengths) member
        exact ⟨a', by simp [pair]⟩

theorem checkResultShape_paramIndex {m : Module} {impl : Impl} {ctx : Context}
    (checked : checkResultShape m impl ctx = .ok ()) {i : Nat}
    (member : RootRef.param i ∈ ctx.resultRoots.flatten) :
    i < impl.params.size ∧ ∃ lv, impl.vars[i]? = some lv ∧ lv.ty.isRefLike = true := by
  unfold checkResultShape at checked
  inv at checked
  obtain ⟨lengths, loop⟩ := checked
  obtain ⟨rs, sets, rootMember⟩ := List.mem_flatten.1 member
  obtain ⟨ty, pair⟩ := resultShape_zipRightMember impl.results.toList ctx.resultRoots
    (by simpa using lengths.symm) sets
  have row := resultShape_forInMember (impl.results.toList.zip ctx.resultRoots) _ (by
    intro pair step success
    rcases pair with ⟨ty, rs⟩
    dsimp only at success
    split at success
    · inv at success
    · simp only [ex_bind_ok, ex_pure_ok] at success
      obtain ⟨_, _, equal⟩ := success
      exact equal) loop (ty, rs) pair
  dsimp only at row
  split at row
  · inv at row
  · simp only [ex_bind_ok, ex_pure_ok] at row
    obtain ⟨loopUnit, roots, rootLoop⟩ := row
    cases loopUnit
    have root := resultShape_forInMember rs _ (by
      intro root step success
      cases root with
      | «local» _ => dsimp only at success; inv at success
      | global g =>
        dsimp only at success
        split at success <;> inv at success
        exact success
      | param j =>
        dsimp only at success
        split at success
        · split at success <;> inv at success
          exact success
        · inv at success) roots (.param i) rootMember
    dsimp only at root
    cases hvar : impl.vars[i]? with
    | none =>
      exfalso
      rw [hvar] at root
      dsimp [reject] at root
      cases root
    | some lv =>
      by_cases hvalid : (decide (i < impl.params.size) && lv.ty.isRefLike) = true
      · simp only [hvar, hvalid, if_true, ex_pure_ok] at root
        have hvalid' : i < impl.params.size ∧ lv.ty.isRefLike = true := by
          simpa using hvalid
        exact ⟨hvalid'.1, lv, rfl, hvalid'.2⟩
      · simp only [hvar] at root
        split at root
        · contradiction
        · exfalso
          dsimp [reject] at root
          cases root

private def RootDeclaration (m : Module) (impl : Impl) (env : Env) (visible : List VarId) :
    RootRef → Prop
  | .global g => ∃ gl, m.globals[g]? = some gl
  | .local x => ∀ lv si, env.vars[x]? = some lv →
      env.scopes.lookup lv.scope = some si → lv.ty.isRefLike = true → x ∈ visible
  | .param j => j < impl.params.size

private def RootListDeclarations (m : Module) (impl : Impl) (env : Env) (visible : List VarId)
    (roots : List RootRef) : Prop :=
  ∀ q, q ∈ roots → RootDeclaration m impl env visible q

private structure SourceVisibility (source : TEnv) (env : Env) (current : TEnv) : Prop where
  currentMod : current.mod = source.mod
  sourceVars : source.vars = env.vars
  currentVars : current.vars = env.vars
  sourceScopes : source.scopes = env.scopes.map Prod.fst
  openScopes : ∀ sc, sc ∈ env.scopes.map Prod.fst → sc ∈ current.scopes
  visible : ∀ x lv si, env.vars[x]? = some lv → env.scopes.lookup lv.scope = some si →
    x ∈ current.visible → x ∈ source.visible

private theorem SourceVisibility.fromFrame {m : Module} {W : World} {tenv : TEnv}
    {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    (frame : Frame m W tenv penv env s future) : SourceVisibility tenv env tenv := by
  refine ⟨rfl, frame.vars_t, frame.vars_t, frame.scopes_t, ?_, ?_⟩
  · intro sc member
    simpa [frame.scopes_t] using member
  · intro x lv si _ _ visible
    exact visible

private theorem SourceVisibility.enterBlock {source : TEnv} {env : Env} {current inner : TEnv}
    (view : SourceVisibility source env current) {scope : Nat}
    (fresh : scope ∉ current.scopes)
    (modEq : inner.mod = current.mod) (varsEq : inner.vars = current.vars)
    (scopesEq : inner.scopes = scope :: current.scopes)
    (visible : ∀ x, x ∈ inner.visible → x ∈ current.visible ∨
      ∃ lv, current.vars[x]? = some lv ∧ lv.scope = scope) :
    SourceVisibility source env inner := by
  refine ⟨modEq.trans view.currentMod, view.sourceVars,
    varsEq.trans view.currentVars, ?_, ?_, ?_⟩
  · exact view.sourceScopes
  · intro sc member
    rw [scopesEq]
    exact List.mem_cons_of_mem _ (view.openScopes sc member)
  · intro x lv si hvar hscope hvisible
    rcases visible x hvisible with previous | ⟨localVar, localLookup, localScope⟩
    · exact view.visible x lv si hvar hscope previous
    · have hvarCurrent : current.vars[x]? = some lv := by
        simpa [view.currentVars] using hvar
      have sameVar : localVar = lv := Option.some.inj (localLookup.symm.trans hvarCurrent)
      subst localVar
      have hscopeCurrent : lv.scope ∈ current.scopes :=
        view.openScopes lv.scope (lookup_key hscope)
      have : scope ∈ current.scopes := by simpa [localScope] using hscopeCurrent
      exact False.elim (fresh this)

private theorem SourceVisibility.forExprEnv {source : TEnv} {env : Env} {current : TEnv}
    (view : SourceVisibility source env current) :
    SourceVisibility source env (exprEnv current) := by
  exact ⟨view.currentMod, view.sourceVars, view.currentVars, view.sourceScopes,
    view.openScopes, view.visible⟩

private theorem localRootDeclaration_ofVisible {m : Module} {impl : Impl} {source : TEnv}
    {env : Env} {current : TEnv} {x : VarId} {lv : LocalVar}
    (view : SourceVisibility source env current)
    (lookup : current.vars[x]? = some lv) (visible : x ∈ current.visible) :
    RootDeclaration m impl env source.visible (.local x) := by
  intro row scope rowLookup scopeLookup _
  have currentLookup : current.vars[x]? = some row := by
    simpa [view.currentVars] using rowLookup
  have sameRow : row = lv := Option.some.inj (currentLookup.symm.trans lookup)
  subst row
  exact view.visible x lv scope rowLookup scopeLookup visible

private theorem tyPlace_var_visible {tenv : TEnv} {x : VarId} {n n' : Nat}
    {info : PlaceInfo} (typed : tyPlace tenv (.var x) n = .ok (info, n')) :
    x ∈ tenv.visible ∧ ∃ lv, tenv.vars[x]? = some lv ∧ lv.ty = info.ty := by
  simp only [tyPlace] at typed
  rcases (st_bind_ok _ _ _ _).1 typed with ⟨lv, next, hvar, hpure⟩
  have hvarFacts := (varOf_ok tenv x n (lv, next)).1 hvar
  rcases hvarFacts with ⟨visible, lookup, _⟩
  have hinfo := (st_pure_ok _ _ _).1 hpure
  have typeEq : lv.ty = info.ty := by
    have h := congrArg Prod.fst hinfo
    cases h
    rfl
  exact ⟨visible, lv, lookup, typeEq⟩

private theorem placeVar_rootsDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {x : VarId} {n n' : Nat} {info : PlaceInfo}
    (view : SourceVisibility source env current)
    (typed : tyPlace current (.var x) n = .ok (info, n')) :
    ∃ roots, penv.access.placeRoots (.var x) = .ok roots ∧
      RootListDeclarations m penv.impl env source.visible roots := by
  obtain ⟨visible, lv, lookup, _⟩ := tyPlace_var_visible typed
  have currentLookup : current.vars[x]? = some lv := lookup
  refine ⟨[.local x], ?_, ?_⟩
  · simp only [AccessEnv.placeRoots]
    rfl
  · intro q member
    simp only [List.mem_singleton] at member
    subst q
    exact localRootDeclaration_ofVisible view currentLookup visible

private theorem placeGlobal_rootsDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {g : GlobalId} {n n' : Nat} {info : PlaceInfo}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (penvMod : penv.mod = m)
    (implVars : current.vars = penv.impl.vars)
    (typed : tyPlace current (.global g) n = .ok (info, n')) :
    ∃ roots, penv.access.placeRoots (.global g) = .ok roots ∧
      RootListDeclarations m penv.impl env source.visible roots := by
  have htype := tyPlace_accessType (tenv := current) (penv := penv)
    (view.currentMod.trans modP) implVars typed
  simp only [PEnv.access, AccessEnv.placeType?] at htype
  cases hglobal : penv.mod.globals[g]? with
  | none => simp [hglobal] at htype
  | some gl =>
    refine ⟨[.global g], ?_, ?_⟩
    · simp only [AccessEnv.placeRoots]
      rfl
    · intro q member
      simp only [List.mem_singleton] at member
      subst q
      exact ⟨gl, by simpa [penvMod] using hglobal⟩

private theorem readVar_accessRoots_ok {tenv : TEnv} {penv : PEnv} {x : VarId}
    {n n' : Nat} {ty : Ty} {state : RState} {roots : List RootRef} {state' : RState}
    (hmod : tenv.mod = penv.mod) (hvars : tenv.vars = penv.impl.vars)
    (typed : tyExpr tenv (.read (.var x)) n = .ok (ty, n'))
    (replayed : rpExpr penv (.read (.var x)) state = .ok (roots, state')) :
    ∃ lv, penv.impl.vars[x]? = some lv ∧ ∃ accessRoots,
      penv.access.exprRoots (.read (.var x)) = .ok accessRoots ∧
      ((lv.ty.isRefLike = true ∧ penv.ann x = some accessRoots) ∨
        (lv.ty.isRefLike = false ∧ accessRoots = [])) := by
  have htype := tyExpr_accessType hmod hvars typed
  simp only [PEnv.access, AccessEnv.exprType?, AccessEnv.placeType?] at htype
  cases hvar : penv.impl.vars[x]? with
  | none => simp [hvar] at htype
  | some lv =>
    simp only [rpExpr] at replayed
    rcases (st_bind_ok _ _ _ _).1 replayed with ⟨placeRoots, state1, hplace, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state2, _, hread⟩
    cases hlike : lv.ty.isRefLike with
    | false =>
      refine ⟨lv, rfl, [], ?_, Or.inr ⟨hlike, rfl⟩⟩
      · simp only [PEnv.access, AccessEnv.exprRoots, hvar, Option.map_some, hlike]
        rfl
    | true =>
      have hreadFacts := readRoots_ok penv (.var x) state2 (roots, state') hread
      rcases hreadFacts.2 with href | hderef | hvalue
      · rcases href with ⟨x', lv', hp, hvar', hlike', hann⟩
        cases hp
        have hann' : (penv.ctx.varRoots.find? (·.1 == x)).map (·.2) = some roots := by
          simpa [PEnv.ann] using hann
        refine ⟨lv, rfl, roots, ?_, Or.inl ⟨hlike, ?_⟩⟩
        · simp only [PEnv.access, AccessEnv.exprRoots, hvar, Option.map_some, hlike, if_pos,
            AccessEnv.variableRoots, hann']
          rfl
        · simpa [PEnv.ann] using hann'
      · rcases hderef with ⟨_, hp, _, _⟩
        cases hp
      · rcases hvalue with ⟨_, hfalse, _⟩
        have hnot : lv.ty.isRefLike = false := hfalse x lv rfl hvar
        simp [hlike] at hnot

private theorem readVar_rootsDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {x : VarId} {n n' : Nat} {ty : Ty}
    {state : RState} {actual : List RootRef} {state' : RState}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (implVars : penv.impl.vars = env.vars) (contextOk : CtxOk m penv.impl penv.ctx)
    (typed : tyExpr current (.read (.var x)) n = .ok (ty, n'))
    (replayed : rpExpr penv (.read (.var x)) state = .ok (actual, state')) :
    ∃ roots, penv.access.exprRoots (.read (.var x)) = .ok roots ∧
      RootListDeclarations m penv.impl env source.visible roots := by
  have hmod : current.mod = penv.mod := view.currentMod.trans modP
  have hvars : current.vars = penv.impl.vars := view.currentVars.trans implVars.symm
  obtain ⟨lv, hvar, roots, hroots, shape⟩ :=
    readVar_accessRoots_ok hmod hvars typed replayed
  refine ⟨roots, hroots, ?_⟩
  rcases shape with ⟨hlike, hann⟩ | ⟨hnotRef, hempty⟩
  · have hrow : (penv.ctx.varRoots.find? (·.1 == x)).map (·.2) = some roots := by
      simpa [PEnv.ann] using hann
    intro q member
    have shapeRoot := checkAnnotationShape_rootDeclaration contextOk.annotationShape hrow member
    cases q with
    | global g => exact shapeRoot
    | param j => exact shapeRoot
    | «local» y =>
      rcases shapeRoot with ⟨target, htarget, hnonref⟩
      intro row si hrowLookup hscope reference
      have envTarget : env.vars[y]? = some target := by
        simpa [implVars] using htarget
      have sameTarget : row = target := Option.some.inj (hrowLookup.symm.trans envTarget)
      subst row
      simp [hnonref] at reference
  · subst roots
    intro q member
    simp at member

private theorem readDerefRoots_declared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {x : VarId} {n n' : Nat} {ty : Ty}
    {state : RState} {actual : List RootRef} {state' : RState}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (implVars : penv.impl.vars = env.vars) (contextOk : CtxOk m penv.impl penv.ctx)
    (typed : tyExpr current (.read (.deref (.read (.var x)))) n = .ok (ty, n'))
    (replayed : rpExpr penv (.read (.deref (.read (.var x)))) state = .ok (actual, state')) :
    ∃ roots, penv.access.exprRoots (.read (.deref (.read (.var x)))) = .ok roots ∧
      RootListDeclarations m penv.impl env source.visible roots := by
  have hmod : current.mod = penv.mod := view.currentMod.trans modP
  have hvars : current.vars = penv.impl.vars := view.currentVars.trans implVars.symm
  have htype := tyExpr_accessType hmod hvars typed
  simp only [PEnv.access, AccessEnv.exprType?, AccessEnv.placeType?] at htype
  cases hvar : penv.impl.vars[x]? with
  | none => simp [hvar] at htype
  | some lv =>
    simp only [rpExpr] at replayed
    rcases (st_bind_ok _ _ _ _).1 replayed with ⟨placeRoots, state1, hplace, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state2, _, hread⟩
    have hreadFacts := readRoots_ok penv (.deref (.read (.var x))) state2
      (actual, state') hread
    rcases hreadFacts.2 with href | hcontent | hvalue
    · rcases href with ⟨_, _, hp, _, _, _⟩
      cases hp
    · rcases hcontent with ⟨x', hp, hslice, hcont⟩
      cases hp
      have htypeSlice : lv.ty.isRefSlice = true := by
        simpa [PEnv.isRefSliceVar, hvar] using hslice
      have hcont' : (penv.ctx.contentRoots.find? (·.1 == x)).map (·.2) = some actual := by
        simpa [PEnv.cont] using hcont
      refine ⟨actual, ?_, ?_⟩
      · simp only [PEnv.access, AccessEnv.exprRoots, hvar, Option.map_some, htypeSlice,
          if_pos, AccessEnv.contentRoots, hcont']
        rfl
      · intro q member
        have shapeRoot := checkContentShape_rootDeclaration contextOk.contentShape hcont' member
        cases q with
        | global g => exact shapeRoot
        | param j => exact shapeRoot
        | «local» _ => exact False.elim shapeRoot
    · rcases hvalue with ⟨hempty, _, hnotSlice⟩
      have htypeNotSlice : lv.ty.isRefSlice = false := by
        have hfalse := hnotSlice x rfl
        simpa [PEnv.isRefSliceVar, hvar] using hfalse
      refine ⟨[], ?_, ?_⟩
      · simp only [PEnv.access, AccessEnv.exprRoots, hvar, Option.map_some, htypeNotSlice]
        rfl
      · intro q member
        simp at member

private theorem readExpr_rootsDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {p : Place} {n n' : Nat} {ty : Ty}
    {state : RState} {actual : List RootRef} {state' : RState}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (implVars : penv.impl.vars = env.vars) (contextOk : CtxOk m penv.impl penv.ctx)
    (typed : tyExpr current (.read p) n = .ok (ty, n'))
    (replayed : rpExpr penv (.read p) state = .ok (actual, state')) :
    ∃ roots, penv.access.exprRoots (.read p) = .ok roots ∧
      RootListDeclarations m penv.impl env source.visible roots := by
  cases p with
  | var x =>
    exact readVar_rootsDeclared view modP implVars contextOk typed replayed
  | deref e =>
    cases e with
    | read p' =>
      cases p' with
      | var x =>
        exact readDerefRoots_declared view modP implVars contextOk typed replayed
      | _ =>
        refine ⟨[], ?_, ?_⟩
        · simp only [PEnv.access, AccessEnv.exprRoots]
          rfl
        · intro q member
          simp at member
    | _ =>
      refine ⟨[], ?_, ?_⟩
      · simp only [PEnv.access, AccessEnv.exprRoots]
        rfl
      · intro q member
        simp at member
  | global _ | field _ _ | elem _ _ _ =>
    refine ⟨[], ?_, ?_⟩
    · simp only [PEnv.access, AccessEnv.exprRoots]
      rfl
    · intro q member
      simp at member

private theorem RootListDeclarations.included {m : Module} {env : Env} {impl : Impl} {visible : List VarId}
    {actual expected : List RootRef}
    (declarations : RootListDeclarations m impl env visible expected)
    (included : RootsIncluded actual expected) :
    RootListDeclarations m impl env visible actual := by
  intro q member
  exact declarations q (included q member)

private theorem RootListDeclarations.union {m : Module} {env : Env} {impl : Impl} {visible : List VarId}
    {left right : List RootRef}
    (leftDeclarations : RootListDeclarations m impl env visible left)
    (rightDeclarations : RootListDeclarations m impl env visible right) :
    RootListDeclarations m impl env visible (unionRoots left right) := by
  intro q member
  rcases unionRoots_mem _ _ q member with inLeft | inRight
  · exact leftDeclarations q inLeft
  · exact rightDeclarations q inRight

private theorem RootListDeclarations.append {m : Module} {env : Env} {impl : Impl} {visible : List VarId}
    {left right : List RootRef}
    (leftDeclarations : RootListDeclarations m impl env visible left)
    (rightDeclarations : RootListDeclarations m impl env visible right) :
    RootListDeclarations m impl env visible (left ++ right) := by
  intro q member
  rcases List.mem_append.1 member with inLeft | inRight
  · exact leftDeclarations q inLeft
  · exact rightDeclarations q inRight

private theorem RootListDeclarations.ofIncludedEmpty {m : Module} {env : Env}
    {impl : Impl} {visible : List VarId} {actual : List RootRef}
    (included : RootsIncluded actual []) : RootListDeclarations m impl env visible actual := by
  intro q member
  have impossible := included q member
  simp at impossible

private theorem emptyExprReplayDeclared {m : Module} {source : TEnv} {env : Env}
    {penv : PEnv} {e : Expr} {state : RState} {actual : List RootRef} {state' : RState}
    (replayed : rpExpr penv e state = .ok (actual, state'))
    (empty : penv.access.exprRoots e = .ok []) :
    RootListDeclarations m penv.impl env source.visible actual :=
  RootListDeclarations.ofIncludedEmpty (rpExpr_accessRoots penv e state actual state' [] replayed empty)

private theorem ArgumentRootDeclarations.row {m : Module} {impl : Impl} {tenv : TEnv} {env : Env}
    {ars : List (List RootRef)} {i : Nat}
    (declarations : ArgumentRootDeclarations m impl tenv env ars) :
    RootListDeclarations m impl env tenv.visible (ars[i]?.getD []) := by
  intro q member
  exact declarations i q member

private theorem ArgumentRootDeclarations.cons {m : Module} {impl : Impl} {tenv : TEnv} {env : Env}
    {head : List RootRef} {tail : List (List RootRef)}
    (headDeclarations : RootListDeclarations m impl env tenv.visible head)
    (tailDeclarations : ArgumentRootDeclarations m impl tenv env tail) :
    ArgumentRootDeclarations m impl tenv env (head :: tail) := by
  intro i q member
  cases i with
  | zero => exact headDeclarations q (by simpa using member)
  | succ i => exact tailDeclarations i q (by simpa using member)

private theorem readVar_replayRootsDeclared {m : Module} {env : Env} {source : TEnv}
    {penv : PEnv} {x : VarId} {lv : LocalVar}
    {state : RState} {actual : List RootRef} {state' : RState}
    (contextOk : CtxOk m penv.impl penv.ctx) (implVars : penv.impl.vars = env.vars)
    (lookup : penv.impl.vars[x]? = some lv) (refLike : lv.ty.isRefLike = true)
    (replayed : rpExpr penv (.read (.var x)) state = .ok (actual, state')) :
    RootListDeclarations m penv.impl env source.visible actual := by
  simp only [rpExpr] at replayed
  rcases (st_bind_ok _ _ _ _).1 replayed with ⟨placeRoots, state1, hplace, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state2, _, hread⟩
  have readFacts := readRoots_ok penv (.var x) state2 (actual, state') hread
  rcases readFacts.2 with href | hderef | hvalue
  · rcases href with ⟨x', lv', hplaceVar, hvar, hlike, hann⟩
    cases hplaceVar
    have annotation : (penv.ctx.varRoots.find? (·.1 == x)).map (·.2) = some actual := by
      simpa [PEnv.ann] using hann
    intro q member
    have shapeRoot := checkAnnotationShape_rootDeclaration contextOk.annotationShape annotation member
    cases q with
    | global g => exact shapeRoot
    | param j => exact shapeRoot
    | «local» y =>
      rcases shapeRoot with ⟨target, targetLookup, targetNonRef⟩
      intro row si rowLookup scopeLookup reference
      have targetEnvLookup : env.vars[y]? = some target := by
        simpa [implVars] using targetLookup
      have sameTarget : row = target := Option.some.inj (rowLookup.symm.trans targetEnvLookup)
      subst row
      simp [targetNonRef] at reference
  · rcases hderef with ⟨_, placeEq, _, _⟩
    cases placeEq
  · rcases hvalue with ⟨_, hfalse, _⟩
    have notRefLike : lv.ty.isRefLike = false := hfalse x lv rfl lookup
    simp [refLike] at notRefLike

private theorem readVar_replayAccessRoots {penv : PEnv} {x : VarId} {lv : LocalVar}
    {state : RState} {actual : List RootRef} {state' : RState}
    (lookup : penv.impl.vars[x]? = some lv) (refLike : lv.ty.isRefLike = true)
    (replayed : rpExpr penv (.read (.var x)) state = .ok (actual, state')) :
    penv.access.exprRoots (.read (.var x)) = .ok actual := by
  simp only [rpExpr] at replayed
  rcases (st_bind_ok _ _ _ _).1 replayed with ⟨placeRoots, state1, _, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state2, _, hread⟩
  have readFacts := readRoots_ok penv (.var x) state2 (actual, state') hread
  rcases readFacts.2 with href | hderef | hvalue
  · rcases href with ⟨_, _, hp, _, _, hann⟩
    cases hp
    have annotation : (penv.ctx.varRoots.find? (·.1 == x)).map (·.2) = some actual := by
      simpa [PEnv.ann] using hann
    simp only [PEnv.access, AccessEnv.exprRoots, lookup, Option.map_some, refLike,
      if_pos, AccessEnv.variableRoots, annotation]
    rfl
  · rcases hderef with ⟨_, hp, _, _⟩
    cases hp
  · rcases hvalue with ⟨_, hfalse, _⟩
    have notRefLike : lv.ty.isRefLike = false := hfalse x lv rfl lookup
    simp [refLike] at notRefLike

private def ResultRootOrigin (args : List (List RootRef)) (q : RootRef) : RootRef → Prop
  | .global g => q = .global g
  | .param i => ∃ roots, args[i]? = some roots ∧ q ∈ roots
  | .local _ => False

private theorem mapResultRoots_origin (args : List (List RootRef)) :
    ∀ (targets acc out : List RootRef), mapResultRoots args acc targets = .ok out →
      ∀ q, q ∈ out → q ∈ acc ∨ ∃ target, target ∈ targets ∧ ResultRootOrigin args q target
  | [], acc, out, checked, q, member => by
    simp only [mapResultRoots, ex_pure_ok] at checked
    subst out
    exact Or.inl member
  | target :: rest, acc, out, checked, q, member => by
    simp only [mapResultRoots, ex_bind_ok] at checked
    obtain ⟨mapped, head, tail⟩ := checked
    rcases mapResultRoots_origin args rest (unionRoots acc mapped) out tail q member with
      inPrior | ⟨later, laterMember, origin⟩
    · rcases unionRoots_mem _ _ q inPrior with inAcc | inMapped
      · exact Or.inl inAcc
      · right
        refine ⟨target, List.mem_cons_self, ?_⟩
        cases target with
        | global g =>
          simp only [mapCalleeRoots, ex_pure_ok] at head
          subst mapped
          have equal : q = .global g := by simpa using inMapped
          exact equal
        | param i =>
          cases roots : args[i]? with
          | none => simp only [mapCalleeRoots, roots] at head; inv at head
          | some rs =>
            simp only [mapCalleeRoots, roots, ex_pure_ok] at head
            subst mapped
            exact ⟨rs, roots, inMapped⟩
        | «local» x =>
          simp only [mapCalleeRoots] at head
          cases head
    · exact Or.inr ⟨later, List.mem_cons_of_mem _ laterMember, origin⟩

private theorem replayBindPureOutput {α β : Type} (action : P α) (value : β)
    (state : RState) (out : β) (state' : RState)
    (checked : (do let _ ← action; pure value) state = .ok (out, state')) : out = value := by
  rcases (st_bind_ok _ _ _ _).1 checked with ⟨_, state1, _, final⟩
  exact congrArg Prod.fst ((st_pure_ok _ state1 _).1 final)

private theorem replayPushTailOutput (penv : PEnv) (owner : Place) (arg : Expr)
    (ownerRoots : List RootRef) (state : RState) (out : List RootRef) (state' : RState)
    (checked : (do
      let _ ← rpExpr penv arg
      addGrows ownerRoots
      if penv.mod.profile == .shrink then
        addWrites ownerRoots
        if (← liftV (penv.limitedOwner owner)) then noteAborts
      pure ownerRoots : P (List RootRef)) state = .ok (out, state')) :
    out = ownerRoots := by
  cases profile : penv.mod.profile with
  | pilot =>
    have checked' : (do
        let _ ← rpExpr penv arg
        addGrows ownerRoots
        pure ownerRoots : P (List RootRef)) state = .ok (out, state') := by
      simpa [profile] using checked
    exact replayBindPureOutput (do let _ ← rpExpr penv arg; addGrows ownerRoots)
      ownerRoots state out state' (by simpa [bind_assoc] using checked')
  | shrink =>
    simp only [profile] at checked
    rcases (st_bind_ok _ _ _ _).1 checked with ⟨_, state1, _, checked⟩
    rcases (st_bind_ok _ _ _ _).1 checked with ⟨_, state2, _, checked⟩
    rcases (st_bind_ok _ _ _ _).1 checked with ⟨_, state3, _, checked⟩
    rcases (st_bind_ok _ _ _ _).1 checked with ⟨limited, state4, _, checked⟩
    cases limited with
    | false => exact congrArg Prod.fst ((st_pure_ok _ state4 _).1 checked)
    | true => exact replayBindPureOutput noteAborts ownerRoots state4 out state' checked

private theorem sliceRefTy_replayFacts {current : TEnv} {e : Expr} {ty : Ty}
    (checked : sliceRefTy current e = some ty) :
    ∃ x lv mu0 mu el, e = .read (.var x) ∧ x ∈ current.visible ∧
      current.vars[x]? = some lv ∧ lv.ty = .ref mu0 (.slice mu el) ∧
      el.flat = true ∧ ty = lv.ty := by
  unfold sliceRefTy at checked
  split at checked
  · rename_i x
    by_cases visible : x ∈ current.visible
    · have contains : current.visible.contains x = true := by simpa using visible
      simp only [contains, if_true] at checked
      cases lookup : current.vars[x]? with
      | none => simp [lookup] at checked
      | some lv =>
        simp only [lookup] at checked
        by_cases refSlice : lv.ty.isRefSlice = true
        · simp only [refSlice, if_true, Option.some.injEq] at checked
          cases type : lv.ty <;> simp only [type, Ty.isRefSlice, reduceCtorEq] at refSlice
          rename_i mu0 target
          cases target <;> simp only [Ty.isRefSlice, reduceCtorEq] at refSlice
          rename_i mu el
          exact ⟨x, lv, mu0, mu, el, rfl, visible, lookup, type, refSlice,
            by rw [← checked, type]⟩
        · simp [refSlice] at checked
    · have contains : current.visible.contains x = false := by simpa using visible
      simp only [contains] at checked
      cases checked
  · cases checked

set_option maxHeartbeats 600000 in
mutual

private theorem placeRoots_replayDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {p : Place} {info : PlaceInfo} {n n' : Nat}
    {state : RState} {actual : List RootRef} {state' : RState}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (penvMod : penv.mod = m) (implVars : current.vars = penv.impl.vars)
    (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : tyPlace current p n = .ok (info, n'))
    (replayed : rpPlace penv p state = .ok (actual, state')) :
    RootListDeclarations m penv.impl env source.visible actual := by
  cases p with
  | var x =>
    obtain ⟨visible, lv, lookup, _⟩ := tyPlace_var_visible typed
    simp only [rpPlace] at replayed
    have actualEq : actual = [.local x] := by
      exact congrArg Prod.fst ((st_pure_ok _ state _).1 replayed)
    subst actual
    intro q member
    simp only [List.mem_singleton] at member
    subst q
    exact localRootDeclaration_ofVisible view lookup visible
  | global g =>
    have typedLookup := tyPlace_accessType (view.currentMod.trans modP) implVars typed
    simp only [PEnv.access, AccessEnv.placeType?] at typedLookup
    cases lookup : penv.mod.globals[g]? with
    | none => simp [lookup] at typedLookup
    | some gl =>
      have globalLookup : m.globals[g]? = some gl := by simpa [penvMod] using lookup
      simp only [rpPlace] at replayed
      have actualEq : actual = [.global g] := by
        exact congrArg Prod.fst ((st_pure_ok _ state _).1 replayed)
      subst actual
      intro q member
      simp only [List.mem_singleton] at member
      subst q
      exact ⟨gl, globalLookup⟩
  | deref e =>
    have hmod : current.mod = penv.mod := view.currentMod.trans modP
    simp only [tyPlace, st_bind_ok] at typed
    obtain ⟨src, next, hsrc, htail⟩ := typed
    cases src with
    | ref mu target =>
      cases slice : sliceRefTy current e with
      | none =>
        simp only [slice, st_bind_ok] at hsrc
        obtain ⟨exprTy, afterExpr, hExpr, hnotSlice⟩ := hsrc
        split at hnotSlice
        · inv at hnotSlice
        · simp only [st_pure_ok, Prod.mk.injEq] at hnotSlice
          obtain ⟨typeEq, stateEq⟩ := hnotSlice
          cases stateEq
          rw [typeEq.symm] at hExpr
          have exprTyped : tyExpr current e n = .ok (.ref mu target, next) := hExpr
          simp only [rpPlace] at replayed
          exact exprRoots_replayDeclared view modP penvMod implVars contextOk moduleOk
            exprTyped replayed
      | some sliceTy =>
        obtain ⟨x, lv, _, _, el, exprEq, _, lookup, typeEq, _, _⟩ :=
          sliceRefTy_replayFacts slice
        subst e
        have penvLookup : penv.impl.vars[x]? = some lv := by
          rw [← implVars]
          exact lookup
        have refLike : lv.ty.isRefLike = true := by simp [typeEq, Ty.isRefLike]
        simp only [rpPlace] at replayed
        have penvVars : penv.impl.vars = env.vars := by
          calc
            penv.impl.vars = current.vars := implVars.symm
            _ = env.vars := view.currentVars
        exact readVar_replayRootsDeclared contextOk penvVars penvLookup refLike replayed
    | _ =>
      simp only [tyPlace] at htail
      inv at htail
  | elem vw index org =>
    simp only [tyPlace, st_bind_ok] at typed
    obtain ⟨_, afterOrg, _, hrest⟩ := typed
    rcases hrest with ⟨viewTy, afterView, hview, _, _, _, _⟩
    simp only [rpPlace] at replayed
    obtain ⟨viewRoots, afterRoots, hviewReplay, hrestReplay⟩ :=
      (st_bind_ok _ _ _ _).1 replayed
    have output : actual = viewRoots := replayBindPureOutput
      (do let _ ← rpExpr penv index; noteAborts) viewRoots afterRoots actual state'
      (by simpa [rpPlace] using hrestReplay)
    subst actual
    exact viewRoots_replayDeclared view modP penvMod implVars contextOk moduleOk hview hviewReplay
  | field owner index =>
    simp only [tyPlace, st_bind_ok] at typed
    obtain ⟨ownerInfo, afterOwner, howner, _⟩ := typed
    simp only [rpPlace] at replayed
    exact placeRoots_replayDeclared view modP penvMod implVars contextOk moduleOk howner replayed
termination_by sizeOf p

private theorem viewRoots_replayDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {vw : View} {el : Ty} {mu : Bool} {n n' : Nat}
    {state : RState} {actual : List RootRef} {state' : RState}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (penvMod : penv.mod = m) (implVars : current.vars = penv.impl.vars)
    (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : tyView current vw n = .ok ((el, mu), n'))
    (replayed : rpView penv vw state = .ok (actual, state')) :
    RootListDeclarations m penv.impl env source.visible actual := by
  cases vw with
  | of p =>
    simp only [tyView, st_bind_ok] at typed
    obtain ⟨info, afterPlace, hplace, _⟩ := typed
    simp only [rpView] at replayed
    obtain ⟨placeRoots, afterRoots, hplaceReplay, hrestReplay⟩ :=
      (st_bind_ok _ _ _ _).1 replayed
    have output : actual = placeRoots := replayBindPureOutput (addReads placeRoots)
      placeRoots afterRoots actual state' (by simpa [rpView] using hrestReplay)
    subst actual
    exact placeRoots_replayDeclared view modP penvMod implVars contextOk moduleOk hplace hplaceReplay
  | val e =>
    simp only [tyView, st_bind_ok] at typed
    obtain ⟨ty, afterExpr, hexpr, _⟩ := typed
    exact exprRoots_replayDeclared view modP penvMod implVars contextOk moduleOk hexpr replayed
termination_by sizeOf vw

private theorem exprRoots_replayDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {e : Expr} {ty : Ty} {n n' : Nat}
    {state : RState} {actual : List RootRef} {state' : RState}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (penvMod : penv.mod = m) (implVars : current.vars = penv.impl.vars)
    (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : tyExpr current e n = .ok (ty, n'))
    (replayed : rpExpr penv e state = .ok (actual, state')) :
    RootListDeclarations m penv.impl env source.visible actual := by
  cases e with
  | lit _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | bool _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | len _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | un _ _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | bin _ _ _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | cmp _ _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | and _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | or _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | «not» _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | conv _ _ _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | pop _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | arrLit _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | fill _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | structLit _ _ =>
    exact emptyExprReplayDeclared replayed (by simp [PEnv.access, AccessEnv.exprRoots]; rfl)
  | read p =>
    obtain ⟨roots, accessRoots, declarations⟩ := readExpr_rootsDeclared view modP
      (by calc
        penv.impl.vars = env.vars := by rw [← implVars, view.currentVars]
        _ = env.vars := rfl) contextOk typed replayed
    exact declarations.included (rpExpr_accessRoots penv (.read p) state actual state' roots replayed accessRoots)
  | ref mode p =>
    simp only [tyExpr, st_bind_ok] at typed
    obtain ⟨info, afterPlace, hplace, _⟩ := typed
    simp only [rpExpr] at replayed
    exact placeRoots_replayDeclared view modP penvMod implVars contextOk moduleOk hplace replayed
  | slice mode vw lo hi org =>
    simp only [tyExpr, st_bind_ok] at typed
    obtain ⟨_, afterOrg, _, hrest⟩ := typed
    rcases hrest with ⟨viewTy, afterView, hview, _, _, _, _⟩
    simp only [rpExpr] at replayed
    obtain ⟨viewRoots, afterRoots, hviewReplay, hrestReplay⟩ := (st_bind_ok _ _ _ _).1 replayed
    have output : actual = viewRoots := replayBindPureOutput
      (do let _ ← rpBound penv lo; let _ ← rpBound penv hi; noteAborts)
      viewRoots afterRoots actual state' (by simpa [rpExpr] using hrestReplay)
    subst actual
    exact viewRoots_replayDeclared view modP penvMod implVars contextOk moduleOk hview hviewReplay
  | push owner value org =>
    have ownerTyped : ∃ afterOwner info, tyPlace current owner n = .ok (info, afterOwner) := by
      cases profile : current.mod.profile with
      | pilot =>
        cases org with
        | none =>
          simp only [tyExpr, profile, st_bind_ok] at typed
          rcases typed with ⟨info, afterOwner, howner, _⟩
          exact ⟨afterOwner, info, howner⟩
        | some origin =>
          simp only [tyExpr, profile] at typed
          obtain ⟨_, _, hreject, _⟩ := (st_bind_ok _ _ _ _).1 typed
          exact False.elim ((st_throw_ok _ _ _).1 hreject)
      | shrink =>
        cases org with
        | none =>
          simp only [tyExpr, profile] at typed
          obtain ⟨_, _, hreject, _⟩ := (st_bind_ok _ _ _ _).1 typed
          exact False.elim ((st_throw_ok _ _ _).1 hreject)
        | some origin =>
          simp only [tyExpr, profile, st_bind_ok] at typed
          rcases typed with ⟨_, afterOrg, horg, info, afterOwner, howner, _⟩
          have afterOrgEq : afterOrg = n := by
            unfold checkOrg at horg
            split at horg
            · simp only [st_pure_ok, Prod.mk.injEq] at horg
              exact horg.2
            · exact False.elim ((st_throw_ok _ _ _).1 horg)
          subst afterOrg
          exact ⟨afterOwner, info, howner⟩
    obtain ⟨afterOwner, info, howner⟩ := ownerTyped
    simp only [rpExpr] at replayed
    obtain ⟨ownerRoots, afterRoots, hownerReplay, hrestReplay⟩ := (st_bind_ok _ _ _ _).1 replayed
    have output : actual = ownerRoots := replayPushTailOutput penv owner value ownerRoots
      afterRoots actual state' (by simpa [rpExpr] using hrestReplay)
    subst actual
    exact placeRoots_replayDeclared view modP penvMod implVars contextOk moduleOk howner hownerReplay
  | ifE condition thenBlock elseBlock =>
    simp only [tyExpr, st_bind_ok] at typed
    obtain ⟨_, afterCondition, _, hrest⟩ := typed
    rcases hrest with ⟨_, _, _, afterThen, thenTy, hthen, afterElse, elseTy, helse, _⟩
    have exprView := view.forExprEnv
    simp only [rpExpr] at replayed
    obtain ⟨_, afterConditionRp, _, hrestRp⟩ := (st_bind_ok _ _ _ _).1 replayed
    obtain ⟨⟨thenRoots, thenRange⟩, afterThenRp, hthenRp, hrestRp⟩ :=
      (st_bind_ok _ _ _ _).1 hrestRp
    obtain ⟨⟨elseRoots, elseRange⟩, afterElseRp, helseRp, hrestElseRp⟩ :=
      (st_bind_ok _ _ _ _).1 hrestRp
    have thenDeclared := blockRoots_replayDeclared exprView modP penvMod implVars
      contextOk moduleOk hthen hthenRp
    have elseDeclared := blockRoots_replayDeclared exprView modP penvMod implVars
      contextOk moduleOk helse helseRp
    have actualEq : actual = unionRoots thenRoots elseRoots := by
      exact congrArg Prod.fst ((st_pure_ok _ afterElseRp (actual, state')).1 hrestElseRp)
    subst actual
    exact RootListDeclarations.union thenDeclared elseDeclared
  | blockE block =>
    simp only [tyExpr] at typed
    simp only [rpExpr] at replayed
    obtain ⟨⟨blockRoots, blockRange⟩, afterBlock, hblock, hfinal⟩ :=
      (st_bind_ok _ _ _ _).1 replayed
    have output : actual = blockRoots := by
      exact congrArg Prod.fst ((st_pure_ok _ afterBlock (actual, state')).1 hfinal)
    subst actual
    exact blockRoots_replayDeclared view.forExprEnv modP penvMod implVars
      contextOk moduleOk typed hblock
  | call c args origin =>
    have hmod : current.mod = penv.mod := view.currentMod.trans modP
    simp only [rpExpr] at replayed
    obtain ⟨argRoots, afterArgs, argsReplay, afterArgsReplay⟩ :=
      (st_bind_ok _ _ _ _).1 replayed
    obtain ⟨_, afterContents, _, callReplay⟩ :=
      (st_bind_ok _ _ _ _).1 afterArgsReplay
    obtain ⟨callContext, callee, contextLookup, calleeLookup, _, _, resultReplay⟩ :=
      rpCall_ok penv c argRoots afterContents actual state' callReplay
    have contextTypedLookup : current.mod.contexts[c]? = some callContext := by
      simpa [hmod] using contextLookup
    have calleeTypedLookup : current.mod.impls[callContext.impl]? = some callee := by
      simpa [hmod] using calleeLookup
    simp only [tyExpr, contextTypedLookup, calleeTypedLookup] at typed
    inv at typed
    obtain ⟨_, lengths, next, argsTyped, _⟩ := typed
    have argumentsDeclared := argsRoots_replayDeclared view modP penvMod implVars
      contextOk moduleOk (by simpa using lengths) argsTyped argsReplay
    have contextModuleLookup : m.contexts[c]? = some callContext := by
      simpa [penvMod] using contextLookup
    have calleeModuleLookup : m.impls[callContext.impl]? = some callee := by
      simpa [penvMod] using calleeLookup
    obtain ⟨checkedCallee, checkedLookup, checkedContext⟩ :=
      moduleOk.ctx c callContext contextModuleLookup
    have sameCallee : checkedCallee = callee :=
      Option.some.inj (checkedLookup.symm.trans calleeModuleLookup)
    subst checkedCallee
    unfold callResultRoots at resultReplay
    split at resultReplay
    · rename_i resultTy resultRoots resultTypes rootSets
      split at resultReplay
      · intro q member
        rcases mapResultRoots_origin argRoots resultRoots [] actual resultReplay q member with
          empty | ⟨target, targetMember, origin⟩
        · simp at empty
        · have targetDeclared := checkResultShape_rootDeclaration checkedContext.resultShape
            (q := target) (by simpa [rootSets] using targetMember)
          cases target with
          | global g =>
            change q = .global g at origin
            subst q
            exact targetDeclared
          | param i =>
            obtain ⟨roots, index, inRoots⟩ := origin
            exact argumentsDeclared i q (by simpa [index] using inRoots)
          | «local» _ => cases origin
      · simp only [ex_pure_ok] at resultReplay
        subst actual
        intro q member
        simp at member
    · simp only [ex_pure_ok] at resultReplay
      subst actual
      intro q member
      simp at member
termination_by sizeOf e

private theorem blockRoots_replayDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {block : Block} {ty : Ty} {n n' : Nat}
    {state : RState} {actual : List RootRef} {range : Nat × Nat} {state' : RState}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (penvMod : penv.mod = m) (implVars : current.vars = penv.impl.vars)
    (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : tyBlock (exprEnv current) [] block n = .ok (ty, n'))
    (replayed : rpBlockValue penv [] block state = .ok ((actual, range), state')) :
    RootListDeclarations m penv.impl env source.visible actual := by
  cases block with
  | mk scope stmts value =>
    cases value with
    | none =>
      obtain ⟨_, st2, _, valueRoots, _, _⟩ :=
        rpBlockValue_ok penv [] scope stmts none state actual range state' replayed
      have empty : actual = [] := valueRoots.1
      subst actual
      intro q member
      simp at member
    | some e =>
      obtain ⟨inner, next, fresh, hstmts, valueTyped, modEq, varsEq, scopesEq, visible⟩ :=
        tyBlock_innerVisible typed
      obtain ⟨_, st2, hstmtsReplay, valueReplay, _, _⟩ :=
        rpBlockValue_ok penv [] scope stmts (some e) state actual range state' replayed
      have valueReplay' : rpExpr { penv with scopes := scope :: penv.scopes } e st2 =
          .ok (actual, state') := by simpa using valueReplay
      have innerView := view.forExprEnv.enterBlock fresh modEq varsEq scopesEq visible
      have innerVars : inner.vars = penv.impl.vars := by
        calc
          inner.vars = (exprEnv current).vars := varsEq
          _ = current.vars := rfl
          _ = penv.impl.vars := implVars
      let blockPenv := { penv with scopes := scope :: penv.scopes }
      have blockMod : blockPenv.mod = m := by simpa [blockPenv] using penvMod
      have blockContext : CtxOk m blockPenv.impl blockPenv.ctx := by
        simpa [blockPenv] using contextOk
      have innerBlockVars : inner.vars = blockPenv.impl.vars := by
        simpa [blockPenv] using innerVars
      exact @exprRoots_replayDeclared m source inner env blockPenv e ty next n' st2
        actual state' innerView modP blockMod innerBlockVars blockContext moduleOk valueTyped
        valueReplay'
termination_by sizeOf block

private theorem argsRoots_replayDeclared {m : Module} {source current : TEnv} {env : Env}
    {penv : PEnv} {callee : Impl} {params : List Param} {args : List Arg}
    {tn tn' : Nat} {state : RState} {actual : List (List RootRef)} {state' : RState}
    (view : SourceVisibility source env current) (modP : source.mod = penv.mod)
    (penvMod : penv.mod = m) (implVars : current.vars = penv.impl.vars)
    (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (lengths : params.length = args.length)
    (typed : tyArgs current callee params args tn = .ok ((), tn'))
    (replayed : rpArgs penv args state = .ok (actual, state')) :
    ArgumentRootDeclarations m penv.impl source env actual := by
  cases params with
  | nil =>
    have argsEmpty : args = [] := List.length_eq_zero_iff.mp (by simpa using lengths.symm)
    subst args
    have empty : actual = [] := by
      simp only [rpArgs] at replayed
      exact congrArg Prod.fst ((st_pure_ok _ state _).1 replayed)
    subst actual
    intro i q member
    simp at member
  | cons param params =>
    cases args with
    | nil => simp at lengths
    | cons arg args =>
      have tailLength : params.length = args.length := by simpa using lengths
      cases varLookup : callee.vars[param.var]? with
      | none => cases arg <;> (simp only [tyArgs, varLookup] at typed; inv at typed)
      | some localVar =>
        cases arg with
        | byVal e =>
          simp only [tyArgs, varLookup] at typed
          inv at typed
          obtain ⟨_, exprTy, next, hExpr, _, tailTyped⟩ := typed
          simp only [rpArgs] at replayed
          obtain ⟨head, state1, hhead, hrest⟩ := (st_bind_ok _ _ _ _).1 replayed
          obtain ⟨tail, state2, htail, hpure⟩ := (st_bind_ok _ _ _ _).1 hrest
          have output : actual = head :: tail := congrArg Prod.fst ((st_pure_ok _ state2 _).1 hpure)
          have headDeclared := exprRoots_replayDeclared view modP penvMod implVars
            contextOk moduleOk hExpr hhead
          have tailDeclared := argsRoots_replayDeclared view modP penvMod implVars
            contextOk moduleOk tailLength tailTyped htail
          subst actual
          exact ArgumentRootDeclarations.cons headDeclared tailDeclared
        | byRef mode place =>
          simp only [tyArgs, varLookup] at typed
          inv at typed
          obtain ⟨_, _, _, _, next, hPlace, _, _, tailTyped⟩ := typed
          have tailTyped : tyArgs current callee params args next = .ok ((), tn') := by
            rcases tailTyped with ⟨_, _, _, htail⟩ | ⟨_, _, htail⟩ <;> exact htail
          simp only [rpArgs] at replayed
          obtain ⟨head, state1, hhead, hrest⟩ := (st_bind_ok _ _ _ _).1 replayed
          obtain ⟨tail, state2, htail, hpure⟩ := (st_bind_ok _ _ _ _).1 hrest
          have output : actual = head :: tail := congrArg Prod.fst ((st_pure_ok _ state2 _).1 hpure)
          have headDeclared := placeRoots_replayDeclared view modP penvMod implVars
            contextOk moduleOk hPlace hhead
          have tailDeclared := argsRoots_replayDeclared view modP penvMod implVars
            contextOk moduleOk tailLength tailTyped htail
          subst actual
          exact ArgumentRootDeclarations.cons headDeclared tailDeclared
termination_by sizeOf args

/-- Replayed call arguments name globals or visible reference holders in the
caller's declaration frame, with parameter indices bounded by its implementation. -/
theorem ArgumentRootDeclarations.ofCallArgs
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {callee : Impl} {args : List Arg} {ars : List (List RootRef)}
    {tn tn' : Nat} {rst rst' : RState}
    (frame : Frame m W tenv penv env s future)
    (moduleOk : ModOk m)
    (callerContextOk : CtxOk m penv.impl penv.ctx)
    (size : callee.params.size = args.length)
    (typed : tyArgs tenv callee callee.params.toList args tn = .ok ((), tn'))
    (replayed : rpArgs penv args rst = .ok (ars, rst')) :
    ArgumentRootDeclarations m penv.impl tenv env ars := by
  have view := SourceVisibility.fromFrame frame
  have modP : tenv.mod = penv.mod := frame.mod_t.trans frame.mod_p.symm
  have implVars : tenv.vars = penv.impl.vars := frame.vars_t.trans frame.vars_p.symm
  exact argsRoots_replayDeclared view modP frame.mod_p implVars callerContextOk moduleOk
    (by simpa using size) typed replayed

end

private def TargetGlobals (m : Module) (targets : List Target) : Prop :=
  ∀ g, Target.global g ∈ targets → g < m.globals.size

private def EffectGlobals (m : Module) (effect : Eff) : Prop :=
  TargetGlobals m effect.reads ∧ TargetGlobals m effect.writes ∧
  TargetGlobals m effect.grows ∧ TargetGlobals m effect.shrinks ∧ TargetGlobals m effect.rebinds

private def PGlobals (m : Module) (action : P α) : Prop :=
  ∀ before output after, action before = .ok (output, after) →
    EffectGlobals m before.eff → EffectGlobals m after.eff

private def declarationEnv (current : TEnv) : Env :=
  ⟨current.vars, 0, current.scopes.map (fun scope => (scope, 0)), 0⟩

private theorem declarationVisibility (current : TEnv) :
    SourceVisibility current (declarationEnv current) current := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [declarationEnv, List.map_map, Function.comp_def]
  · intro scope member
    simpa [declarationEnv, List.map_map, Function.comp_def] using member
  · intro x lv si _ _ visible
    exact visible

private theorem targetGlobals_ofDeclarations {m : Module} {impl : Impl} {env : Env}
    {visible : List VarId} {roots : List RootRef}
    (declared : RootListDeclarations m impl env visible roots) : TargetGlobals m (rootsTargets roots) := by
  intro g member
  obtain ⟨reference, referenceIn, targetEq⟩ := List.mem_filterMap.1 member
  cases reference with
  | «local» _ => simp [rootTarget] at targetEq
  | param _ => simp [rootTarget] at targetEq
  | global found =>
    have equal : found = g := by simpa [rootTarget] using targetEq
    subst found
    obtain ⟨global, lookup⟩ := declared (.global g) referenceIn
    exact (Array.getElem?_eq_some_iff.1 lookup).1

private theorem placeReplay_targetGlobals {m : Module} {current : TEnv} {penv : PEnv}
    {place : Place} {info : PlaceInfo} {n n' : Nat} {before after : RState}
    {roots : List RootRef}
    (modT : current.mod = penv.mod) (modP : penv.mod = m)
    (vars : current.vars = penv.impl.vars)
    (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : tyPlace current place n = .ok (info, n'))
    (replayed : rpPlace penv place before = .ok (roots, after)) :
    TargetGlobals m (rootsTargets roots) := by
  exact targetGlobals_ofDeclarations (placeRoots_replayDeclared
    (declarationVisibility current) modT modP vars contextOk moduleOk typed replayed)

private theorem viewReplay_targetGlobals {m : Module} {current : TEnv} {penv : PEnv}
    {view : View} {info : Ty × Bool} {n n' : Nat} {before after : RState}
    {roots : List RootRef}
    (modT : current.mod = penv.mod) (modP : penv.mod = m)
    (vars : current.vars = penv.impl.vars)
    (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : tyView current view n = .ok (info, n'))
    (replayed : rpView penv view before = .ok (roots, after)) :
    TargetGlobals m (rootsTargets roots) := by
  exact targetGlobals_ofDeclarations (viewRoots_replayDeclared
    (declarationVisibility current) modT modP vars contextOk moduleOk typed replayed)

private theorem argsReplay_globalDeclaration {m : Module} {current : TEnv} {penv : PEnv}
    {callee : Impl} {args : List Arg} {n n' : Nat} {before after : RState}
    {roots : List (List RootRef)}
    (modT : current.mod = penv.mod) (modP : penv.mod = m)
    (vars : current.vars = penv.impl.vars)
    (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (size : callee.params.size = args.length)
    (typed : tyArgs current callee callee.params.toList args n = .ok ((), n'))
    (replayed : rpArgs penv args before = .ok (roots, after)) :
    ∀ i : Nat, TargetGlobals m (rootsTargets (roots[i]?.getD [])) := by
  have declared := argsRoots_replayDeclared (declarationVisibility current)
    modT modP vars contextOk moduleOk (by simpa using size) typed replayed
  intro i g member
  obtain ⟨reference, referenceIn, targetEq⟩ := List.mem_filterMap.1 member
  cases reference with
  | «local» _ => simp [rootTarget] at targetEq
  | param _ => simp [rootTarget] at targetEq
  | global found =>
    have equal : found = g := by simpa [rootTarget] using targetEq
    subst found
    exact declared.globalIndex referenceIn


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
  exact placeReplay_targetGlobals modT modP vars contextOk moduleOk htyped replay

private theorem viewTyped_globals {m : Module} {penv : PEnv} {view : View}
    {before after : RState} {roots : List RootRef}
    (modP : penv.mod = m) (contextOk : CtxOk m penv.impl penv.ctx) (moduleOk : ModOk m)
    (typed : ViewTyped penv view)
    (replay : rpView penv view before = .ok (roots, after)) :
    TargetGlobals m (rootsTargets roots) := by
  obtain ⟨tenv, info, n, n', modT, vars, htyped⟩ := typed
  exact viewReplay_targetGlobals modT modP vars contextOk moduleOk htyped replay

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

-- Resolve the private traversal lemmas when the dispatcher runs inside their mutual group.
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
            (argsReplay_globalDeclaration modT modP vars contextOk moduleOk
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
