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

private def RootDeclaration (m : Module) (env : Env) (visible : List VarId) :
    RootRef → Prop
  | .global g => ∃ gl, m.globals[g]? = some gl
  | .local x => ∀ lv si, env.vars[x]? = some lv →
      env.scopes.lookup lv.scope = some si → lv.ty.isRefLike = true → x ∈ visible
  | .param _ => True

private def RootListDeclarations (m : Module) (env : Env) (visible : List VarId)
    (roots : List RootRef) : Prop :=
  ∀ q, q ∈ roots → RootDeclaration m env visible q

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

private theorem localRootDeclaration_ofVisible {m : Module} {source : TEnv}
    {env : Env} {current : TEnv} {x : VarId} {lv : LocalVar}
    (view : SourceVisibility source env current)
    (lookup : current.vars[x]? = some lv) (visible : x ∈ current.visible) :
    RootDeclaration m env source.visible (.local x) := by
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
      RootListDeclarations m env source.visible roots := by
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
      RootListDeclarations m env source.visible roots := by
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
      RootListDeclarations m env source.visible roots := by
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
    | param _ => trivial
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
      RootListDeclarations m env source.visible roots := by
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
        | param _ => trivial
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
      RootListDeclarations m env source.visible roots := by
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

end Goose.Core.Sound
