import Goose.Core.Sound.Check

/-!
Successful typing and declaration lookups agree on operand types when they
share a module and local-variable table.
-/

namespace Goose.Core.Sound
open Goose.Core

private theorem tyStmt_static (env : TEnv) (scope : Nat) (stmt : Stmt)
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

private theorem tyStmts_static (env : TEnv) (scope : Nat) (stmts : List Stmt)
    (n n' : Nat) (env' : TEnv)
    (ht : tyStmts env scope stmts n = .ok (env', n')) :
    env'.mod = env.mod ∧ env'.vars = env.vars := by
  induction stmts generalizing env n n' env' with
  | nil =>
    simp only [tyStmts] at ht
    have hp := (st_pure_ok env n (env', n')).1 ht
    cases hp
    exact ⟨rfl, rfl⟩
  | cons stmt rest ih =>
    simp only [tyStmts, st_bind_ok] at ht
    rcases ht with ⟨middle, next, hstmt, hrest⟩
    have hmiddle := tyStmt_static env scope stmt n next middle hstmt
    have htail := ih middle next n' env' hrest
    exact ⟨htail.1.trans hmiddle.1, htail.2.trans hmiddle.2⟩

private theorem sliceRefTy_access {tenv : TEnv} {access : AccessEnv} {e : Expr} {ty : Ty}
    (hvars : tenv.vars = access.impl.vars) (h : sliceRefTy tenv e = some ty) :
    access.exprType? e = some ty := by
  cases e with
  | read p =>
    cases p with
    | var x =>
      by_cases hx : x ∈ tenv.visible
      · cases hvar : tenv.vars[x]? with
        | none => simp [sliceRefTy, hx, hvar] at h
        | some lv =>
          by_cases hs : lv.ty.isRefSlice = true
          · have heq : lv.ty = ty := by simpa [sliceRefTy, hx, hvar, hs] using h
            simp [AccessEnv.exprType?, AccessEnv.placeType?, ← hvars, hvar, heq]
          · simp [sliceRefTy, hx, hvar, hs] at h
      · simp [sliceRefTy, hx] at h
    | _ => simp [sliceRefTy] at h
  | _ => simp [sliceRefTy] at h

private theorem tyBlock_empty_ok {tenv : TEnv} {sc : Nat} {stmts : List Stmt}
    {value : Option Expr} {n n' : Nat} {ty : Ty}
    (ht : tyBlock tenv [] (.mk sc stmts value) n = .ok (ty, n')) :
    ∃ middle next, tyStmts {tenv with scopes := sc :: tenv.scopes} sc stmts n = .ok (middle, next) ∧
      (match value with | none => (pure Ty.unit : T Ty) | some e => tyExpr middle e) next = .ok (ty, n') := by
  unfold tyBlock at ht
  dsimp only at ht
  simp only [declarePre] at ht
  inv at ht
  exact ht.2

mutual

private theorem tyPlace_accessType_env (tenv : TEnv) (access : AccessEnv) (p : Place)
    (n n' : Nat) (info : PlaceInfo)
    (hmod : tenv.mod = access.mod) (hvars : tenv.vars = access.impl.vars)
    (ht : tyPlace tenv p n = .ok (info, n')) :
    access.placeType? p = some info.ty := by
  cases p with
  | var x =>
    simp only [tyPlace] at ht
    inv at ht
    obtain ⟨_, lv, hvar, rfl, rfl⟩ := ht
    simp [AccessEnv.placeType?, ← hvars, hvar]
  | global g =>
    by_cases hlimit : g < tenv.globalLimit
    · cases hglobal : tenv.mod.globals[g]? with
      | none => simp only [tyPlace, if_pos hlimit, hglobal] at ht; inv at ht
      | some gl =>
        simp only [tyPlace, if_pos hlimit, hglobal] at ht
        inv at ht
        obtain ⟨rfl, rfl⟩ := ht
        simp [AccessEnv.placeType?, ← hmod, hglobal]
    · simp only [tyPlace, if_neg hlimit] at ht; inv at ht
  | deref e =>
    simp only [tyPlace, st_bind_ok] at ht
    obtain ⟨src, next, hsrc, htail⟩ := ht
    cases src <;> try (inv at htail)
    rename_i mu target
    obtain ⟨rfl, rfl⟩ := htail
    have hlookup : access.exprType? e = some (.ref mu target) := by
      cases href : sliceRefTy tenv e with
      | some ty =>
        try simp only [href] at hsrc
        have heq := (st_pure_ok ty n ((.ref mu target), _)).1 hsrc
        obtain ⟨rfl, rfl⟩ := heq
        exact sliceRefTy_access hvars href
      | none =>
        try simp only [href, st_bind_ok] at hsrc
        obtain ⟨ty, middle, hexpr, hrest⟩ := hsrc
        inv at hrest
        obtain ⟨_, rfl, rfl⟩ := hrest
        exact tyExpr_accessType_env tenv access e n _ (.ref mu target) hmod hvars hexpr
    simp [AccessEnv.placeType?, hlookup]
  | elem view index org =>
    simp only [tyPlace] at ht
    inv at ht
    obtain ⟨_, el, mu, next, hview, ti, last, hti, intTag, rfl, rfl, rfl⟩ := ht
    exact tyView_accessElement_env tenv access view n next el mu hmod hvars hview
  | field owner index =>
    simp only [tyPlace, st_bind_ok] at ht
    obtain ⟨ownerInfo, next, howner, field, last, hfield, hpure⟩ := ht
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).1 hpure
    have hownerType := tyPlace_accessType_env tenv access owner n next ownerInfo hmod hvars howner
    unfold structField at hfield
    rw [st_bind_ok] at hfield
    obtain ⟨descriptor, middle, hdescriptor, hlookup⟩ := hfield
    cases hty : ownerInfo.ty <;> simp only [structDef, hty] at hdescriptor <;> inv at hdescriptor
    rename_i sid fields
    obtain ⟨_, _, _, hdescriptor⟩ := hdescriptor
    cases hd : tenv.mod.structs[sid]? with
    | none => simp only [hd] at hdescriptor; inv at hdescriptor
    | some d =>
      simp only [hd] at hdescriptor
      obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).1 hdescriptor
      cases hf : descriptor.fields[index]? with
      | none => simp only [hf] at hlookup; inv at hlookup
      | some f =>
        simp only [hf] at hlookup
        obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).1 hlookup
        simp [AccessEnv.placeType?, hownerType, hty, ← hmod, hd, hf]
termination_by sizeOf p

private theorem tyView_accessElement_env (tenv : TEnv) (access : AccessEnv) (view : View)
    (n n' : Nat) (el : Ty) (mu : Bool)
    (hmod : tenv.mod = access.mod) (hvars : tenv.vars = access.impl.vars)
    (ht : tyView tenv view n = .ok ((el, mu), n')) :
    access.viewElement? view = some el := by
  cases view with
  | of p =>
    simp only [tyView, st_bind_ok] at ht
    obtain ⟨info, next, hplace, htail⟩ := ht
    have hlookup := tyPlace_accessType_env tenv access p n next info hmod hvars hplace
    cases info with
    | mk ty binding contents =>
      cases ty <;> inv at htail
      all_goals obtain ⟨rfl, rfl, rfl⟩ := htail
      all_goals simp [AccessEnv.viewElement?, hlookup]
  | val e =>
    simp only [tyView, st_bind_ok] at ht
    obtain ⟨ty, next, hexpr, htail⟩ := ht
    have hlookup := tyExpr_accessType_env tenv access e n next ty hmod hvars hexpr
    cases ty <;> inv at htail
    obtain ⟨rfl, rfl, rfl⟩ := htail
    simp [AccessEnv.viewElement?, hlookup]
termination_by sizeOf view

private theorem tyExpr_accessType_env (tenv : TEnv) (access : AccessEnv) (expr : Expr)
    (n n' : Nat) (ty : Ty)
    (hmod : tenv.mod = access.mod) (hvars : tenv.vars = access.impl.vars)
    (ht : tyExpr tenv expr n = .ok (ty, n')) :
    access.exprType? expr = some ty := by
  cases expr with
  | lit t v =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, rfl, rfl⟩ := ht
    rfl
  | bool value =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨rfl, rfl⟩ := ht
    rfl
  | read p =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨t, binding, contents, next, hplace, _, rfl, rfl⟩ := ht
    exact tyPlace_accessType_env tenv access p n _ _ hmod hvars hplace
  | ref mu p =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨t, binding, contents, next, hplace, _, _, htail⟩ := ht
    have htype : ty = .ref mu t := by
      rcases htail with ⟨_, _, equal, _⟩ | ⟨_, equal, _⟩ <;> exact equal
    subst ty
    have hlookup := tyPlace_accessType_env tenv access p n next ⟨t, binding, contents⟩ hmod hvars hplace
    simp [AccessEnv.exprType?, hlookup]
  | slice mu view lo hi origin =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, el, writable, next, hview, _, _, _, _, htail⟩ := ht
    have htype : ty = .slice mu el := by
      rcases htail with ⟨_, _, equal, _⟩ | ⟨_, equal, _⟩ <;> exact equal
    subst ty
    have hlookup := tyView_accessElement_env tenv access view n next el writable hmod hvars hview
    simp [AccessEnv.exprType?, hlookup]
  | len view =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, _, _, _, rfl, rfl⟩ := ht
    rfl
  | un op a origin =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, ta, next, ha, t, rfl, htail⟩ := ht
    have htype : ty = .int t := by
      cases op <;> inv at htail
      · exact htail.2.1
      · exact htail.1
    subst ty
    exact tyExpr_accessType_env tenv access a n next (.int t) hmod hvars ha
  | bin op a b origin =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, ta, next, ha, t, rfl, tb, last, hb, u, rfl, rfl, rfl, rfl⟩ := ht
    exact tyExpr_accessType_env tenv access a n next (.int t) hmod hvars ha
  | cmp op a b =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨ta, next, ha, tb, last, hb, htail⟩ := ht
    cases ta <;> cases tb <;> inv at htail
    · obtain ⟨_, rfl, rfl⟩ := htail
      rfl
    · cases op <;> inv at htail <;> obtain ⟨rfl, rfl⟩ := htail <;> rfl
  | and a b =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩ := ht
    rfl
  | or a b =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩ := ht
    rfl
  | not a =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, _, _, _, rfl, rfl⟩ := ht
    rfl
  | conv kind target a origin =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, _, _, _, _, _, htail⟩ := ht
    cases target <;> inv at htail
    rename_i tag
    have htype : ty = .int tag := by
      cases kind <;> inv at htail <;> first | exact htail.1 | exact htail.2.2.1
    subst ty
    rfl
  | call context args origin =>
    cases hc : tenv.mod.contexts[context]? with
    | none => simp only [tyExpr, hc] at ht; inv at ht
    | some ctx =>
      cases hi : tenv.mod.impls[ctx.impl]? with
      | none => simp only [tyExpr, hc, hi] at ht; inv at ht
      | some callee =>
        simp only [tyExpr, hc, hi] at ht; inv at ht
        obtain ⟨_, _, next, _, last, _, hresult⟩ := ht
        cases hr : callee.results.toList with
        | nil =>
          simp only [callResultTy, hr] at hresult
          obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).1 hresult
          simp [AccessEnv.exprType?, ← hmod, hc, hi, hr]
        | cons result rest =>
          cases rest with
          | nil =>
            simp only [callResultTy, hr] at hresult
            obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).1 hresult
            simp [AccessEnv.exprType?, ← hmod, hc, hi, hr]
          | cons other rest =>
            simp only [callResultTy, hr] at hresult
            inv at hresult
  | push owner a origin =>
    cases hp : tenv.mod.profile <;> cases origin <;>
      simp only [tyExpr, hp] at ht <;> inv at ht
    case pilot.none =>
      obtain ⟨t, binding, contents, next, hplace, el, last, helement,
        _, _, _, _, _, rfl, rfl⟩ := ht
      have hlookup := tyPlace_accessType_env tenv access owner n next ⟨t, binding, contents⟩ hmod hvars hplace
      have hel := (ownerElement_ok tenv t el next last helement).2.1
      simp [AccessEnv.exprType?, hlookup, hel]
    case shrink.some =>
      obtain ⟨_, t, binding, contents, next, hplace, el, last, helement,
        _, _, _, _, _, rfl, rfl⟩ := ht
      have hlookup := tyPlace_accessType_env tenv access owner n next ⟨t, binding, contents⟩ hmod hvars hplace
      have hel := (ownerElement_ok tenv t el next last helement).2.1
      simp [AccessEnv.exprType?, hlookup, hel]
  | pop owner origin =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨pre, _, _, t, binding, contents, next, hplace, el, last, helement,
      _, rfl, rfl⟩ := ht
    have hlookup := tyPlace_accessType_env tenv access owner pre next ⟨t, binding, contents⟩ hmod hvars hplace
    have hel := (ownerElement_ok tenv t ty next n' helement).2.1
    simp [AccessEnv.exprType?, hlookup, hel]
  | ifE condition yes no =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, next, _, _, tt, middle, hyes, _, _, _, _, rfl, rfl⟩ := ht
    exact tyBlock_accessType_env (exprEnv tenv) access yes next middle ty hmod hvars hyes
  | blockE block =>
    exact tyBlock_accessType_env (exprEnv tenv) access block n n' ty hmod hvars ht
  | arrLit t elements =>
    simp only [tyExpr] at ht; inv at ht
    cases t <;> inv at ht
    all_goals
      first
      | obtain ⟨_, _, _, _, _, rfl, rfl⟩ := ht
      | obtain ⟨_, _, _, _, rfl, rfl⟩ := ht
    all_goals simp_all [AccessEnv.exprType?]
  | fill t value =>
    simp only [tyExpr] at ht; inv at ht
    cases t <;> inv at ht
    obtain ⟨_, _, _, _, _, _, rfl, rfl⟩ := ht
    rfl
  | structLit t fields =>
    simp only [tyExpr] at ht; inv at ht
    obtain ⟨_, _, _, _, _, _, rfl, rfl⟩ := ht
    rfl
termination_by sizeOf expr

private theorem tyBlock_accessType_env (tenv : TEnv) (access : AccessEnv) (block : Block)
    (n n' : Nat) (ty : Ty)
    (hmod : tenv.mod = access.mod) (hvars : tenv.vars = access.impl.vars)
    (ht : tyBlock tenv [] block n = .ok (ty, n')) :
    access.blockType? block = some ty := by
  cases block with
  | mk sc stmts value =>
    obtain ⟨middle, next, hstmts, hvalue⟩ := tyBlock_empty_ok ht
    have hstatic := tyStmts_static {tenv with scopes := sc :: tenv.scopes} sc stmts n next middle hstmts
    cases value with
    | none =>
      obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).1 hvalue
      rfl
    | some e =>
      exact tyExpr_accessType_env middle access e next n' ty
        (hstatic.1.trans hmod) (hstatic.2.trans hvars) hvalue
termination_by sizeOf block

end

/-- Successful place typing agrees with static declaration lookup. -/
theorem tyPlace_accessType {tenv : TEnv} {penv : PEnv} {p : Place}
    {n n' : Nat} {info : PlaceInfo}
    (hmod : tenv.mod = penv.mod) (hvars : tenv.vars = penv.impl.vars)
    (ht : tyPlace tenv p n = .ok (info, n')) :
    penv.access.placeType? p = some info.ty :=
  tyPlace_accessType_env tenv penv.access p n n' info hmod hvars ht

/-- Successful view typing agrees with static element-type lookup. -/
theorem tyView_accessElement {tenv : TEnv} {penv : PEnv} {view : View}
    {n n' : Nat} {el : Ty} {mu : Bool}
    (hmod : tenv.mod = penv.mod) (hvars : tenv.vars = penv.impl.vars)
    (ht : tyView tenv view n = .ok ((el, mu), n')) :
    penv.access.viewElement? view = some el :=
  tyView_accessElement_env tenv penv.access view n n' el mu hmod hvars ht

end Goose.Core.Sound
