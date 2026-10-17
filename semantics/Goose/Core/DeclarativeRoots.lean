import Goose.Core.Sound.Module

namespace Goose.Core.Declarative
open Goose.Core Goose.Core.Sound

abbrev RootRelation (α : Type) := RState → α → RState → Prop

instance : Monad RootRelation where
  pure a := fun before value after => value = a ∧ after = before
  bind x f := fun before value after => ∃ middle intermediate,
    x before intermediate middle ∧ f intermediate middle value after

instance : MonadStateOf RState RootRelation where
  get := fun before value after => value = before ∧ after = before
  set value := fun _ result after => result = () ∧ after = value
  modifyGet f := fun before value after => (value, after) = f before

def requireRoot (condition : Prop) : RootRelation Unit :=
  fun before value after => condition ∧ value = () ∧ after = before

def BindRoots (env : PEnv) (chain : List Nat) (x : VarId) (rho : List RootRef) : Prop :=
  ∃ lv ann, env.impl.vars[x]? = some lv ∧ env.ann x = some ann ∧
    (∀ q, q ∈ rho → q ∈ ann) ∧
    ∀ y, RootRef.local y ∈ rho → ∃ ly, env.impl.vars[y]? = some ly ∧
      ly.scope ∈ chain ∧ chain.idxOf lv.scope ≤ chain.idxOf ly.scope

def ResultRoots (env : PEnv) (rho : List RootRef) : Prop :=
  (∀ y, RootRef.local y ∉ rho) ∧
    ∃ declared, env.ctx.resultRoots = [declared] ∧ ∀ q, q ∈ rho → q ∈ declared

def BlockRoots (n0 n1 : Nat) (rho : List RootRef) : Prop :=
  ∀ y, RootRef.local y ∈ rho → ¬ (n0 ≤ y ∧ y < n1)

def StoreRoots (env : PEnv) (p : Place) (rho : List RootRef) : Prop :=
  ∀ x, p.derefVar? = some x → env.isRefSliceVar x = true →
    ∃ cont, env.cont x = some cont ∧ ∀ q, q ∈ rho → q ∈ cont

def ReadRoots (env : PEnv) (p : Place) (rho : List RootRef) : Prop :=
  (∃ x lv, p = .var x ∧ env.impl.vars[x]? = some lv ∧ lv.ty.isRefLike = true ∧
    env.ann x = some rho) ∨
  (∃ x, p = .deref (.read (.var x)) ∧ env.isRefSliceVar x = true ∧ env.cont x = some rho) ∨
  (rho = [] ∧ (∀ x lv, p = .var x → env.impl.vars[x]? = some lv → lv.ty.isRefLike = false) ∧
    ∀ x, p = .deref (.read (.var x)) → env.isRefSliceVar x = false)

def rootRead (env : PEnv) (p : Place) : RootRelation (List RootRef) :=
  fun before rho after => ReadRoots env p rho ∧ after = before

def rootLimitedOwner (env : PEnv) (p : Place) : RootRelation Bool :=
  fun before limited after => after = before ∧
    ∃ ty, env.access.placeType? p = some ty ∧ limited = (match ty with | .limited .. => true | _ => false)

def rootReads (rs : List RootRef) : RootRelation Unit :=
  modify fun s => { s with eff := { s.eff with reads := addTargets s.eff.reads (rootsTargets rs) } }
def rootWrites (rs : List RootRef) : RootRelation Unit :=
  modify fun s => { s with eff := { s.eff with writes := addTargets s.eff.writes (rootsTargets rs) } }
def rootGrows (rs : List RootRef) : RootRelation Unit :=
  modify fun s => { s with eff := { s.eff with grows := addTargets s.eff.grows (rootsTargets rs) } }
def rootShrinks (rs : List RootRef) : RootRelation Unit :=
  modify fun s => { s with eff := { s.eff with shrinks := addTargets s.eff.shrinks (rootsTargets rs) } }
def rootAborts : RootRelation Unit := modify fun s => { s with eff := { s.eff with aborts := true } }
def rootOutputs : RootRelation Unit := modify fun s => { s with eff := { s.eff with outputs := true } }

def MappedRoots (ar : List (List RootRef)) (declared out : List RootRef) : Prop :=
  (∀ r, r ∈ declared → MappedRoot ar out r) ∧
  ∀ q, q ∈ out → ∃ r, r ∈ declared ∧ FromRoot ar q r

def ArgumentRoots (callee : Impl) (ctx : Context) (ar : List (List RootRef)) : Prop :=
  ∀ i p, callee.params[i]? = some p → ∃ pv, callee.vars[p.var]? = some pv ∧
    (pv.ty.isRefLike = true → ∃ ann,
      (ctx.varRoots.find? (·.1 == p.var)).map (·.2) = some ann ∧
      (ann = [.param i] ∨ ∀ q, q ∈ ar[i]?.getD [] → q ∈ ann))

def ContentRoots (env : PEnv) (ctx : Context) (args : List Arg) (ar : List (List RootRef)) : Prop :=
  ∀ i cont, i < args.length → (ctx.contentRoots.find? (·.1 == i)).map (·.2) = some cont →
    ∃ inst, MappedRoots ar cont inst ∧
      ((∃ mu s ann, args[i]? = some (.byRef mu (.var s)) ∧ env.ann s = some ann ∧
        (∀ q, q ∈ ann → q ∈ inst) ∧ BindRoots env env.scopes s inst) ∨
       (∃ mu q cq, args[i]? = some (.byRef mu (.deref (.read (.var q)))) ∧ env.cont q = some cq ∧
        (∀ r, r ∈ inst → r ∈ cq) ∧ (∀ r, r ∈ cq → r ∈ inst)))

def rootContents (env : PEnv) (c : ContextId) (args : List Arg) (ar : List (List RootRef)) : RootRelation Unit :=
  requireRoot (∀ ctx, env.mod.contexts[c]? = some ctx → ContentRoots env ctx args ar)

def rootCall (env : PEnv) (c : ContextId) (ar : List (List RootRef)) : RootRelation (List RootRef) :=
  fun before rho after => ∃ ctx callee,
    env.mod.contexts[c]? = some ctx ∧ env.mod.impls[ctx.impl]? = some callee ∧
    ArgumentRoots callee ctx ar ∧ after = { before with eff := callEffects callee ctx ar before.eff } ∧
    (match callee.results.toList, ctx.resultRoots with
      | [t], [rs] => if t.isRefLike then MappedRoots ar rs rho else rho = []
      | _, _ => rho = [])

mutual

def RootPlace (env : PEnv) : Place → RootRelation (List RootRef)
  | .var x => pure [.local x]
  | .global g => pure [.global g]
  | .deref e => RootExpr env e
  | .field owner _ => RootPlace env owner
  | .elem v i _ => do
    let rho ← RootView env v
    let _ ← RootExpr env i
    rootAborts
    pure rho


def RootView (env : PEnv) : View → RootRelation (List RootRef)
  | .of p => do
    let rho ← RootPlace env p
    rootReads rho
    pure rho
  | .val e => RootExpr env e

def RootBound (env : PEnv) : Bound → RootRelation Unit
  | .omitted => pure ()
  | .expr e => do let _ ← RootExpr env e
  | .fromEnd e => do let _ ← RootExpr env e

def RootExpr (env : PEnv) : Expr → RootRelation (List RootRef)
  | .lit _ _ => pure []
  | .bool _ => pure []
  | .read p => do
    let rho ← RootPlace env p
    rootReads rho
    rootRead env p
  | .ref _ p => RootPlace env p
  | .slice _ v lo hi _ => do
    let rho ← RootView env v
    RootBound env lo
    RootBound env hi
    rootAborts
    pure rho
  | .len v => do
    let _ ← RootView env v
    pure []
  | .un op a _ => do
    let _ ← RootExpr env a
    match op with
    | .neg => rootAborts
    | .bitnot => pure ()
    pure []
  | .bin op a b _ => do
    let _ ← RootExpr env a
    let _ ← RootExpr env b
    if op.mayAbort then rootAborts
    pure []
  | .cmp _ a b => do
    let _ ← RootExpr env a
    let _ ← RootExpr env b
    pure []
  | .and a b => do
    let _ ← RootExpr env a
    let _ ← RootExpr env b
    pure []
  | .or a b => do
    let _ ← RootExpr env a
    let _ ← RootExpr env b
    pure []
  | .not a => do
    let _ ← RootExpr env a
    pure []
  | .conv k _ a _ => do
    let _ ← RootExpr env a
    match k with
    | .as => rootAborts
    | _ => pure ()
    pure []
  | .call c args _ => do
    let argRoots ← RootArgs env args
    rootContents env c args argRoots
    rootCall env c argRoots
  | .push owner a _ => do
    let rho ← RootPlace env owner
    let _ ← RootExpr env a
    rootGrows rho
    if env.mod.profile == .shrink then
      rootWrites rho
      if (← rootLimitedOwner env owner) then rootAborts
    pure rho
  | .pop owner _ => do
    let rho ← RootPlace env owner
    rootReads rho
    rootShrinks rho
    rootAborts
    pure []
  | .ifE c t f => do
    let _ ← RootExpr env c
    let (rt, lt) ← RootBlockValue env [] t
    let (rf, lf) ← RootBlockValue env [] f
    let _ := (lt, lf)
    pure (unionRoots rt rf)
  | .blockE b => do
    let (rho, _) ← RootBlockValue env [] b
    pure rho
  | .arrLit _ es => do
    RootExprs env es
    pure []
  | .structLit _ es => do
    RootExprs env es
    pure []
  | .fill _ a => do
    let _ ← RootExpr env a
    pure []

def RootExprs (env : PEnv) : List Expr → RootRelation Unit
  | [] => pure ()
  | e :: rest => do
    let _ ← RootExpr env e
    RootExprs env rest


def RootArgs (env : PEnv) : List Arg → RootRelation (List (List RootRef))
  | [] => pure []
  | .byVal e :: rest => do
    let rho ← RootExpr env e
    pure (rho :: (← RootArgs env rest))
  | .byRef _ p :: rest => do
    let rho ← RootPlace env p
    pure (rho :: (← RootArgs env rest))


def RootBlockValue (env : PEnv) (pre : List VarId) : Block → RootRelation (List RootRef × (Nat × Nat))
  | .mk sc stmts value => do
    let st0 ← get

    (if pre.all (fun x => st0.nextVar ≤ x && x < st0.nextVar + pre.length) then pure () else requireRoot False : RootRelation Unit)
    modify fun s => { s with nextVar := s.nextVar + pre.length }
    RootStmts { env with scopes := sc :: env.scopes } stmts
    let rho ← (match value with
      | none => pure []
      | some e => RootExpr { env with scopes := sc :: env.scopes } e)
    let st1 ← get
    requireRoot (BlockRoots st0.nextVar st1.nextVar rho)
    pure (rho, (st0.nextVar, st1.nextVar))

def RootStmts (env : PEnv) : List Stmt → RootRelation Unit
  | [] => pure ()
  | s :: rest => do
    RootStmt env s
    RootStmts env rest

def RootPrintArgs (env : PEnv) : List PrintArg → RootRelation Unit
  | [] => pure ()
  | .text _ :: rest => RootPrintArgs env rest
  | .expr e :: rest => do
    let _ ← RootExpr env e
    RootPrintArgs env rest

def RootStmt (env : PEnv) : Stmt → RootRelation Unit
  | .letS x e _ => do

    unless x = (← get).nextVar do requireRoot False
    modify fun s => { s with nextVar := s.nextVar + 1 }
    let rho ← RootExpr env e
    match env.impl.vars[x]? with
    | some lv =>
      if lv.ty.isRefLike then requireRoot (BindRoots env env.scopes x rho)
    | none => requireRoot False
  | .assign p e _ => do
    let rho ← RootPlace env p
    let stored ← RootExpr env e
    requireRoot (StoreRoots env p stored)
    rootWrites rho

    modify fun s => { s with eff := { s.eff with rebinds := addTargets s.eff.rebinds (storeRebinds env p) } }
  | .assignOp op p e _ => do
    let rho ← RootPlace env p
    let _ ← RootExpr env e
    rootReads rho
    rootWrites rho
    if op.mayAbort then rootAborts
  | .rebind x e _ => do
    let rho ← RootExpr env e
    requireRoot (BindRoots env env.scopes x rho)
    if x < env.impl.params.size then
      modify fun s => { s with eff := { s.eff with rebinds := addTargets s.eff.rebinds [.param x] } }
  | .expr e _ => do
    let _ ← RootExpr env e
  | .append owner src _ => do
    let rho ← RootPlace env owner

    let run ← RootView env src
    rootReads run
    rootGrows rho
    if env.mod.profile == .shrink then
      rootWrites rho
      if (← rootLimitedOwner env owner) then rootAborts
  | .popN owner count _ => do
    let rho ← RootPlace env owner
    let _ ← RootExpr env count
    rootReads rho
    rootShrinks rho
    rootAborts
  | .resize owner size fill _ => do
    let rho ← RootPlace env owner
    let _ ← RootExpr env size
    match fill with
    | none => pure ()
    | some e =>
      let _ ← RootExpr env e
      rootWrites rho
      rootGrows rho
    rootReads rho
    rootShrinks rho
    rootAborts
  | .clear owner _ => do
    let rho ← RootPlace env owner
    rootReads rho
    rootShrinks rho
  | .assignWhole owner replacement _ => do
    let rho ← RootPlace env owner
    rootReads rho
    rootShrinks rho
    let _ ← RootExpr env replacement
    rootWrites rho
    rootGrows rho
  | .ifS c t f _ => do
    let _ ← RootExpr env c
    let _ ← RootBlockValue env [] t
    match f with
    | some b => do let _ ← RootBlockValue env [] b
    | none => pure ()
  | .while c b _ => do
    let _ ← RootExpr env c
    let _ ← RootBlockValue env [] b
  | .forRange x lo hi b _ => do

    
    let st0 ← get
    (if x = st0.nextVar then pure () else requireRoot False : RootRelation Unit)
    modify fun s => { s with nextVar := s.nextVar + 1 }
    let _ ← RootExpr env lo
    let _ ← RootExpr env hi
    let body ← RootBlockValue env [] b

    requireRoot (BlockRoots st0.nextVar body.2.1 body.1)
  | .forEach x idx v byRef b _ => do
    let st0 ← get
    (if x = st0.nextVar && idx.all (· == st0.nextVar + 1) then pure () else requireRoot False : RootRelation Unit)
    modify fun s => { s with nextVar := s.nextVar + 1 + idx.toList.length }
    let rho ← RootView env v

    if byRef then requireRoot (BindRoots env (b.scope :: env.scopes) x rho) else rootReads rho
    let body ← RootBlockValue env [] b
    requireRoot (BlockRoots st0.nextVar body.2.1 body.1)
  | .ret e _ => do
    match e with
    | none => pure ()
    | some e => do
      let rho ← RootExpr env e
      requireRoot (ResultRoots env rho)
  | .brk _ => pure ()
  | .cont _ => pure ()
  | .print args _ => do
    RootPrintArgs env args
    rootOutputs
  | .assertS e _ => do
    let _ ← RootExpr env e
    rootAborts
  | .abort _ _ => rootAborts
  | .exit e _ => do
    let _ ← RootExpr env e
    rootAborts

end


def RefinesRoot (checked : P α) (logical : RootRelation α) : Prop :=
  ∀ before value after, checked before = .ok (value, after) → logical before value after

theorem refineRoot_pure (a : α) : RefinesRoot (pure a) (pure a) := by
  intro before value after h
  exact Prod.mk.inj ((st_pure_ok _ _ _).1 h)

theorem refineRoot_bind {x : P α} {y : RootRelation α} {f : α → P β} {g : α → RootRelation β}
    (hx : RefinesRoot x y) (hf : ∀ a, RefinesRoot (f a) (g a)) :
    RefinesRoot (x >>= f) (y >>= g) := by
  intro before value after h
  obtain ⟨a, middle, h1, h2⟩ := (st_bind_ok _ _ _ _).1 h
  exact ⟨middle, a, hx _ _ _ h1, hf a _ _ _ h2⟩

theorem refineRoot_get : RefinesRoot get get := by
  intro before value after h
  exact Prod.mk.inj ((st_get_ok _ _).1 h)

theorem refineRoot_modify (f : RState → RState) : RefinesRoot (modify f) (modify f) := by
  intro before value after h
  have hpair := (st_modify_ok _ _ _).1 h
  cases value
  have ha := congrArg Prod.snd hpair
  change after = f before at ha
  subst after
  rfl

theorem refineRoot_reject (rule : Rule) (message : String) (condition : Prop) :
    RefinesRoot (rejP rule message) (requireRoot condition) := by
  intro before value after h
  inv at h

theorem refineRoot_lift (checked : V Unit) (condition : Prop)
    (hcondition : checked = .ok () → condition) :
    RefinesRoot (liftV checked) (requireRoot condition) := by
  intro before value after h
  cases value
  obtain ⟨hc, rfl⟩ := (liftV_ok _ _ _).1 h
  exact ⟨hcondition hc, rfl, rfl⟩

theorem refineRoot_bindRoots (env : PEnv) (chain : List Nat) (x : VarId) (rho : List RootRef) :
    RefinesRoot (bindRoots env chain x rho) (requireRoot (BindRoots env chain x rho)) :=
  refineRoot_lift _ _ (bindRootsV_ok env chain x rho)

theorem refineRoot_result (env : PEnv) (rho : List RootRef) :
    RefinesRoot (checkResult env rho) (requireRoot (ResultRoots env rho)) :=
  refineRoot_lift _ _ (checkResultV_ok env rho)

theorem refineRoot_block (n0 n1 : Nat) (rho : List RootRef) :
    RefinesRoot (liftV (checkBlockValue n0 n1 rho)) (requireRoot (BlockRoots n0 n1 rho)) :=
  refineRoot_lift _ _ (checkBlockValue_ok n0 n1 rho)

theorem refineRoot_store (env : PEnv) (p : Place) (rho : List RootRef) :
    RefinesRoot (liftV (checkStore env p rho)) (requireRoot (StoreRoots env p rho)) :=
  refineRoot_lift _ _ (fun h x hx hs => checkStore_ok env p rho h x hx hs)

theorem refineRoot_read (env : PEnv) (p : Place) :
    RefinesRoot (readRoots env p) (rootRead env p) := by
  intro before value after h
  have hr := readRoots_ok env p before (value, after) h
  exact ⟨hr.2, hr.1⟩

theorem mappedRoots_sound (ar : List (List RootRef)) (rs rho : List RootRef)
    (h : mapResultRoots ar [] rs = .ok rho) : MappedRoots ar rs rho := by
  refine ⟨(mapResultRoots_ok ar rs [] rho h).2, ?_⟩
  intro q hq
  rcases mapResultRoots_sub ar rs [] rho h q hq with hn | hm
  · cases hn
  · exact hm

theorem refineRoot_contents (env : PEnv) (c : ContextId) (args : List Arg) (ar : List (List RootRef)) :
    RefinesRoot (liftV (checkContents env c args ar)) (rootContents env c args ar) := by
  apply refineRoot_lift
  intro h ctx hc i cont hi hcont
  obtain ⟨inst, hmap, hcase⟩ := checkContent_ok env ctx args ar i cont
    (checkContents_ok env c args ar ctx h hc i hi) hcont
  refine ⟨inst, mappedRoots_sound ar cont inst hmap, ?_⟩
  rcases hcase with ⟨mu, s, ann, ha, hann, hsub, hb⟩ | other
  · exact Or.inl ⟨mu, s, ann, ha, hann, hsub, bindRootsV_ok env env.scopes s inst hb⟩
  · exact Or.inr other

theorem refineRoot_call (env : PEnv) (c : ContextId) (ar : List (List RootRef)) :
    RefinesRoot (rpCall env c ar) (rootCall env c ar) := by
  intro before rho after h
  obtain ⟨ctx, callee, hc, hi, hargs, heff, hresult⟩ := rpCall_ok env c ar before rho after h
  refine ⟨ctx, callee, hc, hi, ?_, heff, ?_⟩
  · intro i p hp
    exact checkArgRoots_ok callee ctx ar i p
      (hargs i (Array.getElem?_eq_some_iff.1 hp).1) hp
  · unfold callResultRoots at hresult
    split
    · rename_i t rs ht hr
      simp only [ht, hr] at hresult
      split
      · rename_i hty
        simp only [hty, ite_true] at hresult
        exact mappedRoots_sound _ _ _ hresult
      · rename_i hty
        simp only [hty] at hresult
        exact (ex_pure_ok _ _).1 hresult
    · rename_i hother
      split at hresult
      · rename_i t rs ht hr
        exact False.elim (hother t rs ht hr)
      · exact (ex_pure_ok _ _).1 hresult

theorem refineRoot_limited (env : PEnv) (owner : Place) :
    RefinesRoot (liftV (env.limitedOwner owner)) (rootLimitedOwner env owner) := by
  intro before limited after h
  obtain ⟨hc, rfl⟩ := (liftV_ok _ _ _).1 h
  unfold PEnv.limitedOwner at hc
  cases ht : env.access.placeType? owner with
  | none => simp only [ht] at hc; inv at hc
  | some ty =>
    refine ⟨rfl, ty, ht, ?_⟩
    cases ty <;> simp only [ht] at hc <;> exact (ex_pure_ok _ _).1 hc

theorem refineRoot_reads (rs : List RootRef) : RefinesRoot (addReads rs) (rootReads rs) :=
  refineRoot_modify _
theorem refineRoot_writes (rs : List RootRef) : RefinesRoot (addWrites rs) (rootWrites rs) :=
  refineRoot_modify _
theorem refineRoot_grows (rs : List RootRef) : RefinesRoot (addGrows rs) (rootGrows rs) :=
  refineRoot_modify _
theorem refineRoot_shrinks (rs : List RootRef) : RefinesRoot (addShrinks rs) (rootShrinks rs) :=
  refineRoot_modify _
theorem refineRoot_aborts : RefinesRoot noteAborts rootAborts := refineRoot_modify _
theorem refineRoot_outputs : RefinesRoot noteOutputs rootOutputs := refineRoot_modify _

theorem refineRoot_ite {condition : Prop} [Decidable condition]
    {yes no : P α} {logicalYes logicalNo : RootRelation α}
    (hy : RefinesRoot yes logicalYes) (hn : RefinesRoot no logicalNo) :
    RefinesRoot (if condition then yes else no) (if condition then logicalYes else logicalNo) := by
  split <;> assumption

open Lean Elab Tactic in
elab "root_bind" : tactic => do
  let target ← getMainTarget
  let args := target.getAppArgs
  unless target.isAppOf ``RefinesRoot && args.size ≥ 2 &&
      args[args.size - 2]!.isAppOf ``Bind.bind do
    throwError "expected a root sequencing judgment"
  evalTactic (← `(tactic| refine refineRoot_bind ?_ (fun _ => ?_)))

open Lean Elab Tactic in
elab "root_primitive" : tactic => do
  let target ← getMainTarget
  let args := target.getAppArgs
  unless target.isAppOf ``RefinesRoot && args.size ≥ 2 do
    throwError "expected a root judgment"
  let checked := args[args.size - 2]!
  let name := checked.getAppFn.constName?
  let tactic ← match name with
    | some ``ite => `(tactic| refine refineRoot_ite ?_ ?_)
    | some ``Pure.pure => `(tactic| exact refineRoot_pure _)
    | some ``get => `(tactic| exact refineRoot_get)
    | some ``modify => `(tactic| exact refineRoot_modify _)
    | some ``addReads => `(tactic| exact refineRoot_reads _)
    | some ``addWrites => `(tactic| exact refineRoot_writes _)
    | some ``addGrows => `(tactic| exact refineRoot_grows _)
    | some ``addShrinks => `(tactic| exact refineRoot_shrinks _)
    | some ``noteAborts => `(tactic| exact refineRoot_aborts)
    | some ``noteOutputs => `(tactic| exact refineRoot_outputs)
    | some ``bindRoots => `(tactic| exact refineRoot_bindRoots _ _ _ _)
    | some ``checkResult => `(tactic| exact refineRoot_result _ _)
    | some ``readRoots => `(tactic| exact refineRoot_read _ _)
    | some ``rpCall => `(tactic| exact refineRoot_call _ _ _)
    | some ``rejP => `(tactic| exact refineRoot_reject _ _ _)
    | some ``liftV => `(tactic| first
        | exact refineRoot_block _ _ _ | exact refineRoot_store _ _ _
        | exact refineRoot_contents _ _ _ _ | exact refineRoot_limited _ _)
    | _ => throwError "unknown root primitive {name}"
  evalTactic tactic

macro "root_refine" : tactic => `(tactic| repeat' (first
  | assumption
  | root_bind
  | root_primitive
  | (split <;> simp_all only [ite_true, ite_false, Bool.false_eq_true])))

set_option maxHeartbeats 100000 in
theorem root_syntax_sound :
    (∀ env p, RefinesRoot (rpPlace env p) (RootPlace env p)) ∧
    (∀ env v, RefinesRoot (rpView env v) (RootView env v)) ∧
    (∀ env e, RefinesRoot (rpExpr env e) (RootExpr env e)) ∧
    (∀ env es, RefinesRoot (rpExprs env es) (RootExprs env es)) ∧
    (∀ env pre b, RefinesRoot (rpBlockValue env pre b) (RootBlockValue env pre b)) ∧
    (∀ env ss, RefinesRoot (rpStmts env ss) (RootStmts env ss)) ∧
    (∀ env s, RefinesRoot (rpStmt env s) (RootStmt env s)) ∧
    (∀ env args, RefinesRoot (rpPrintArgs env args) (RootPrintArgs env args)) ∧
    (∀ env args, RefinesRoot (rpArgs env args) (RootArgs env args)) ∧
    (∀ env b, RefinesRoot (rpBound env b) (RootBound env b)) := by
  apply rpPlace.mutual_induct
    (motive_1 := fun env p => RefinesRoot (rpPlace env p) (RootPlace env p))
    (motive_2 := fun env v => RefinesRoot (rpView env v) (RootView env v))
    (motive_3 := fun env e => RefinesRoot (rpExpr env e) (RootExpr env e))
    (motive_4 := fun env es => RefinesRoot (rpExprs env es) (RootExprs env es))
    (motive_5 := fun env pre b => RefinesRoot (rpBlockValue env pre b) (RootBlockValue env pre b))
    (motive_6 := fun env ss => RefinesRoot (rpStmts env ss) (RootStmts env ss))
    (motive_7 := fun env s => RefinesRoot (rpStmt env s) (RootStmt env s))
    (motive_8 := fun env args => RefinesRoot (rpPrintArgs env args) (RootPrintArgs env args))
    (motive_9 := fun env args => RefinesRoot (rpArgs env args) (RootArgs env args))
    (motive_10 := fun env b => RefinesRoot (rpBound env b) (RootBound env b))
  case case17 =>
    intro env op a org h
    cases op <;> simp only [rpExpr, RootExpr] <;> root_refine
  case case23 =>
    intro env k target a org h
    cases k <;> simp only [rpExpr, RootExpr] <;> root_refine
  all_goals (intros; (try cases ‹Option Expr›) <;> (try cases ‹Option Block›) <;> simp_all only [rpPlace, rpView, rpExpr, rpExprs, rpBlockValue, rpStmts, rpStmt, rpPrintArgs, rpArgs, rpBound, RootPlace, RootView, RootExpr, RootExprs, RootBlockValue, RootStmts, RootStmt, RootPrintArgs, RootArgs, RootBound] <;> root_refine)

def RootDeclared (m : Module) (impl : Impl) : RootRef → Prop
  | .local y => ∃ lv, impl.vars[y]? = some lv ∧ lv.ty.isRefLike = false
  | .global g => g < m.globals.size
  | .param i => i < impl.params.size

def AnnotationRoots (m : Module) (impl : Impl) (ctx : Context) : Prop :=
  (∀ x rs, (x, rs) ∈ ctx.varRoots → ∃ lv, impl.vars[x]? = some lv ∧
    lv.ty.isRefLike = true ∧ ∀ r, r ∈ rs → RootDeclared m impl r) ∧
  (∀ x lv, impl.vars[x]? = some lv → lv.ty.isRefLike = true →
    (ctx.varRoots.filter (·.1 == x)).length = 1) ∧
  ∀ i rs, i < impl.params.size → (ctx.varRoots.find? (·.1 == i)).map (·.2) = some rs →
    ∀ q, q ∈ rs → q = .param i ∨ ∃ g, q = .global g

def DeclaredContents (m : Module) (impl : Impl) (ctx : Context) : Prop :=
  ∀ x cont, (x, cont) ∈ ctx.contentRoots → x < impl.params.size ∧
    ∃ lv, impl.vars[x]? = some lv ∧ lv.ty.isRefSlice = true ∧
      (ctx.varRoots.find? (·.1 == x)).map (·.2) = some [.param x] ∧
      ∀ r, r ∈ cont → match r with
        | .local _ => False
        | .global g => g < m.globals.size
        | .param i => i < impl.params.size

def DeclaredResults (m : Module) (impl : Impl) (ctx : Context) : Prop :=
  ctx.resultRoots.length = impl.results.size ∧
    ∀ t rs, (t, rs) ∈ impl.results.toList.zip ctx.resultRoots →
      (t.isRefLike = false → rs = []) ∧
      ∀ r, r ∈ rs → match r with
        | .local _ => False
        | .global g => g < m.globals.size
        | .param i => i < impl.params.size ∧ ∃ lv, impl.vars[i]? = some lv ∧ lv.ty.isRefLike = true

def TargetDeclared (m : Module) (impl : Impl) : Target → Prop
  | .param i => i < impl.params.size
  | .global g => g < m.globals.size

def SummaryContains (m : Module) (impl : Impl) (ctx : Context) (eff : Eff) : Prop :=
  ∀ sm, impl.summary = .known sm →
    (∀ t, t ∈ sm.reads ++ sm.writes ++ sm.grows ++ sm.shrinks ++ sm.rebinds → TargetDeclared m impl t) ∧
    eff.unknown = false ∧
    (∀ t, t ∈ eff.reads → t ∈ expandTargets impl ctx sm.reads) ∧
    (∀ t, t ∈ eff.writes → t ∈ expandTargets impl ctx sm.writes) ∧
    (∀ t, t ∈ eff.grows → t ∈ expandTargets impl ctx sm.grows) ∧
    (∀ t, t ∈ eff.shrinks → t ∈ expandTargets impl ctx sm.shrinks) ∧
    (∀ t, t ∈ eff.rebinds → t ∈ sm.rebinds) ∧
    (eff.aborts = true → sm.aborts = true) ∧
    (eff.outputs = true → sm.outputs = true)

private theorem forInRoot_member {α : Type} (xs : List α)
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

private theorem summaryTargets_sound (m : Module) (impl : Impl) (what : String) (ts : List Target)
    (h : checkSummaryTargets m impl what ts = .ok ()) :
    ∀ t, t ∈ ts → TargetDeclared m impl t := by
  intro t ht
  have hrow := (forAll_ok _ _).1 h t ht
  cases t <;> simp only [checkSummaryTargets] at h
  all_goals dsimp only at hrow; inv at hrow; exact hrow

theorem summary_sound (m : Module) (impl : Impl) (ctx : Context) (eff : Eff)
    (h : checkSummary m impl ctx eff = .ok ()) : SummaryContains m impl ctx eff := by
  intro sm hs
  unfold checkSummary at h
  simp only [hs] at h
  inv at h
  obtain ⟨hr, hw, hg, hsh, hre, hu, er, ew, eg, esh, ere, ha, ho⟩ := h
  refine ⟨?_, by simpa using hu, effWithin_ok _ _ _ _ er, effWithin_ok _ _ _ _ ew,
    effWithin_ok _ _ _ _ eg, effWithin_ok _ _ _ _ esh, effWithin_ok _ _ _ _ ere, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_append] at ht
    rcases ht with (((ht | ht) | ht) | ht) | ht
    · exact summaryTargets_sound m impl "reads" _ hr t ht
    · exact summaryTargets_sound m impl "writes" _ hw t ht
    · exact summaryTargets_sound m impl "grows" _ hg t ht
    · exact summaryTargets_sound m impl "shrinks" _ hsh t ht
    · exact summaryTargets_sound m impl "rebinds" _ hre t ht
  · intro habort
    simpa [habort] using ha
  · intro houtput
    simpa [houtput] using ho

theorem declaredContents_sound (m : Module) (impl : Impl) (ctx : Context)
    (checked : checkContentShape m impl ctx = .ok ()) : DeclaredContents m impl ctx := by
  intro x cont member
  have row := (forAll_ok _ _).1 checked (x, cont) member
  dsimp only at row
  inv at row
  obtain ⟨hp, row⟩ := row
  cases hv : impl.vars[x]? with
  | none => simp only [hv] at row; inv at row
  | some lv =>
    simp only [hv] at row
    inv at row
    obtain ⟨hs, ha, roots⟩ := row
    refine ⟨hp, lv, rfl, hs, by simpa using ha, ?_⟩
    intro r hr
    have root := (forAll_ok _ _).1 roots r hr
    cases r <;> dsimp only at root <;> inv at root <;> assumption

theorem declaredResults_sound (m : Module) (impl : Impl) (ctx : Context)
    (checked : checkResultShape m impl ctx = .ok ()) : DeclaredResults m impl ctx := by
  unfold checkResultShape at checked
  inv at checked
  obtain ⟨lengths, loop⟩ := checked
  refine ⟨lengths, ?_⟩
  intro t rs member
  have row := forInRoot_member (impl.results.toList.zip ctx.resultRoots) _ (by
    intro pair step success
    rcases pair with ⟨t, rs⟩
    dsimp only at success
    split at success
    · inv at success
    · simp only [ex_bind_ok, ex_pure_ok] at success
      obtain ⟨_, _, equal⟩ := success
      exact equal) loop (t, rs) member
  dsimp only at row
  split at row
  · inv at row
  · rename_i flat
    simp only [ex_bind_ok, ex_pure_ok] at row
    obtain ⟨loopUnit, roots, _⟩ := row
    cases loopUnit
    refine ⟨?_, ?_⟩
    · intro ht
      have hempty : rs.isEmpty = true := by simpa [ht] using flat
      exact List.isEmpty_iff.1 hempty
    · intro r hr
      have root := forInRoot_member rs _ (by
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
          · inv at success) roots r hr
      cases r with
      | «local» y => dsimp only at root; inv at root
      | global g => dsimp only at root; inv at root; exact root
      | param j =>
        dsimp only at root
        cases hv : impl.vars[j]? with
        | none => simp only [hv] at root; inv at root
        | some lv =>
          simp only [hv] at root
          inv at root
          have hvalid : j < impl.params.size ∧ lv.ty.isRefLike = true := by simpa using root
          exact ⟨hvalid.1, lv, hv, hvalid.2⟩

theorem annotationRows_sound (m : Module) (impl : Impl) (ctx : Context)
    (checked : checkAnnotationShape m impl ctx = .ok ()) :
    ∀ x rs, (x, rs) ∈ ctx.varRoots → ∃ lv, impl.vars[x]? = some lv ∧
      lv.ty.isRefLike = true ∧ ∀ r, r ∈ rs → RootDeclared m impl r := by
  unfold checkAnnotationShape at checked
  simp only [ex_bind_ok] at checked
  obtain ⟨loopUnit, firstLoop, _⟩ := checked
  cases loopUnit
  intro x rs member
  have row := forInRoot_member ctx.varRoots _ (by
    intro pair step success
    rcases pair with ⟨y, roots⟩
    dsimp only at success
    split at success
    · inv at success
    · split at success
      · simp only [ex_bind_ok, ex_pure_ok] at success
        obtain ⟨_, _, equal⟩ := success
        exact equal
      · inv at success) firstLoop (x, rs) member
  dsimp only at row
  cases hv : impl.vars[x]? with
  | none => simp only [hv] at row; inv at row
  | some lv =>
    simp only [hv] at row
    split at row
    · rename_i hr
      simp only [ex_bind_ok, ex_pure_ok] at row
      obtain ⟨loopUnit, loop, _⟩ := row
      cases loopUnit
      refine ⟨lv, rfl, hr, ?_⟩
      intro r member
      have root := forInRoot_member rs _ (by
        intro root step success
        cases root with
        | «local» y =>
          dsimp only at success
          split at success
          · inv at success
          · split at success <;> inv at success
            exact success
        | global g =>
          dsimp only at success
          split at success <;> inv at success
          exact success
        | param i =>
          dsimp only at success
          split at success <;> inv at success
          exact success) loop r member
      cases r with
      | «local» y =>
        dsimp only at root
        cases hy : impl.vars[y]? with
        | none => simp only [hy] at root; inv at root
        | some ly =>
          simp only [hy] at root
          split at root
          · inv at root
          · rename_i hr
            exact ⟨ly, hy, by simpa using hr⟩
      | global g => dsimp only at root; inv at root; exact root
      | param i => dsimp only at root; inv at root; exact root
    · inv at row

private theorem forInRootDependent_member {α : Type} (xs : List α)
    (f : (a : α) → a ∈ xs → V (ForInStep PUnit.{1}))
    (yielded : ∀ a ha step, f a ha = .ok step → step = .yield ⟨⟩)
    (checked : forIn' (m := V) xs (PUnit.unit : PUnit.{1}) (fun a ha _ => f a ha) = .ok PUnit.unit) :
    ∀ a (ha : a ∈ xs), f a ha = .ok (.yield ⟨⟩) := by
  induction xs with
  | nil => intro a ha; cases ha
  | cons a rest ih =>
    rw [List.forIn'_cons] at checked
    obtain ⟨step, head, tail⟩ := (ex_bind_ok _ _ _).1 checked
    have equal := yielded a (by simp) step head
    subst step
    intro b member
    rcases List.mem_cons.1 member with rfl | member
    · exact head
    · exact ih (fun b hb => f b (List.mem_cons_of_mem a hb))
        (fun b hb step h => yielded b _ step h) tail b member

theorem annotations_sound (m : Module) (impl : Impl) (ctx : Context)
    (checked : checkAnnotationShape m impl ctx = .ok ()) : AnnotationRoots m impl ctx := by
  refine ⟨annotationRows_sound m impl ctx checked, ?_, ?_⟩
  · intro x lv hv href
    unfold checkAnnotationShape at checked
    simp only [ex_bind_ok] at checked
    obtain ⟨firstUnit, _, secondUnit, complete, _⟩ := checked
    cases firstUnit
    cases secondUnit
    have hlt : x < impl.vars.size := (Array.getElem?_eq_some_iff.1 hv).1
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at complete
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at complete
    have row := forInRootDependent_member (List.range' 0 impl.vars.size) _ (by
      intro y hy step h
      try dsimp only at h
      split at h
      · inv at h
        exact h.2
      · exact (ex_pure_ok _ _).1 h) complete x (by simpa using hlt)
    try dsimp only at row
    have hrow : impl.vars[x] = lv := by
      exact Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans hv)
    simp only [hrow, href, ite_true] at row
    inv at row
    exact row
  · intro i rs hi hf q hq
    unfold checkAnnotationShape at checked
    simp only [ex_bind_ok] at checked
    obtain ⟨_, _, _, _, last⟩ := checked
    have row := (forAll_ok _ _).1 last i (List.mem_range.2 hi)
    cases found : ctx.varRoots.find? (·.1 == i) with
    | none => simp [found] at hf
    | some pair =>
      obtain ⟨x, roots⟩ := pair
      have heq : roots = rs := by simpa [found] using hf
      subst roots
      simp only [found] at row
      have root := (forAll_ok _ _).1 row q hq
      cases q with
      | «local» y => dsimp only at root; inv at root
      | global g => exact Or.inr ⟨g, rfl⟩
      | param j => dsimp only at root; inv at root; exact Or.inl (by rw [root])

structure ContextRoots (m : Module) (impl : Impl) (ctx : Context) : Prop where
  annotations : AnnotationRoots m impl ctx
  results : DeclaredResults m impl ctx
  contents : DeclaredContents m impl ctx
  body : ∃ rho range after,
    RootBlockValue ⟨m, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ (rho, range) after ∧
    (impl.body.value.isSome = true → ResultRoots ⟨m, impl, ctx, []⟩ rho) ∧
    SummaryContains m impl ctx after.eff

structure GlobalRoots (m : Module) (g : GlobalId) (gl : Global) : Prop where
  initializer : ∃ rho after,
    RootExpr ⟨m, initImpl, initContext, []⟩ gl.init ⟨0, {}⟩ rho after ∧
    after.eff.unknown = false ∧
    ∀ h, Target.global h ∈ after.eff.reads ++ after.eff.writes ++ after.eff.grows ++ after.eff.shrinks → h < g

theorem contextRoots_sound (m : Module) (ctx : Context) (h : checkContext m ctx = .ok ()) :
    ∃ impl, m.impls[ctx.impl]? = some impl ∧ ContextRoots m impl ctx := by
  unfold checkContext at h
  cases hi : m.impls[ctx.impl]? with
  | none => simp only [hi] at h; inv at h
  | some impl =>
    simp only [hi] at h
    inv at h
    obtain ⟨hann, hrs, hcont, st, ⟨rho, a, b, s1, hrb, hck⟩, hcs⟩ := h
    refine ⟨impl, rfl, annotations_sound m impl ctx hann, declaredResults_sound m impl ctx hrs,
      declaredContents_sound m impl ctx hcont, rho, (a, b), st, ?_, ?_, summary_sound m impl ctx st.eff hcs⟩
    · have hbody : rpBlockValue ⟨m, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
          .ok ((rho, (a, b)), st) := by
        rcases hck with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact hrb
      exact root_syntax_sound.2.2.2.2.1 _ _ _ _ _ _ hbody
    · intro hs
      rcases hck with ⟨_, hresult, _⟩ | ⟨hn, _⟩
      · exact checkResultV_ok _ _ hresult
      · exact False.elim (hn hs)

theorem globalRoots_sound (m : Module) (g : GlobalId) (gl : Global)
    (hg : m.globals[g]? = some gl) (h : checkInitRoots m g = .ok ()) : GlobalRoots m g gl := by
  obtain ⟨rho, after, hexpr, hu, htargets⟩ := checkInitRoots_ok m g gl hg h
  refine ⟨rho, after, root_syntax_sound.2.2.1 _ _ _ _ _ hexpr, hu, ?_⟩
  intro k hk
  simp only [List.mem_append] at hk
  rcases hk with ((hk | hk) | hk) | hk
  · exact htargets _ (Or.inl hk) k rfl
  · exact htargets _ (Or.inr (Or.inl hk)) k rfl
  · exact htargets _ (Or.inr (Or.inr (Or.inl hk))) k rfl
  · exact htargets _ (Or.inr (Or.inr (Or.inr hk))) k rfl

theorem accepted_contextRoots (m : Module) (h : validate m = .ok ()) :
    ∀ (c : ContextId) ctx, m.contexts[c]? = some ctx → ∃ impl,
      m.impls[ctx.impl]? = some impl ∧ ContextRoots m impl ctx := by
  unfold validate at h
  inv at h
  obtain ⟨_, _, _, _, _, contexts, _, _, _⟩ := h
  intro c ctx hc
  exact contextRoots_sound m ctx ((forAll_ok _ _).1 contexts ctx
    (Array.mem_toList_iff.2 (Array.mem_of_getElem? hc)))

theorem accepted_globalRoots (m : Module) (h : validate m = .ok ()) :
    ∀ (g : GlobalId) gl, m.globals[g]? = some gl → GlobalRoots m g gl := by
  unfold validate at h
  inv at h
  obtain ⟨_, _, _, _, _, _, initializers, _, _⟩ := h
  intro g gl hg
  exact globalRoots_sound m g gl hg ((forAll_ok _ _).1 initializers g
    (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hg).1))

end Goose.Core.Declarative
