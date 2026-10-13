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

end Goose.Core.Sound
