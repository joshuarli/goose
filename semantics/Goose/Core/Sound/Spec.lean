import Goose.Core.Sound.Scope
import Goose.Core.Sound.Invert

/-!
What each evaluation function is shown to do on code the validator accepted,
as one statement per function. The statements are proved together by
induction on fuel.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-- What a `return` must hand to the caller: a value of the result type that
points only into the caller's roots the context declares. -/
def RetOk (m : Module) (W : World) (tenv : TEnv) (penv : PEnv) (s : St) (v : Val) : Prop :=
  ∃ impl, tenv.impl = some impl ∧
    ((impl.results.toList = [] ∧ v = .unit) ∨
      ∃ t, impl.results.toList = [t] ∧ HasTy m W.G s.store v t) ∧
    ∀ r, Targets v r → ∃ declared, penv.ctx.resultRoots = [declared] ∧ Gam noEnv W.P declared r

/-- How control may leave code that is not a whole block. -/
def FlowOk (m : Module) (W : World) (tenv : TEnv) (penv : PEnv) (s : St) : Flow → Prop
  | .normal _ => True
  | .brk => tenv.loops ≠ 0
  | .cont => tenv.loops ≠ 0
  | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s v

/-- How control may leave a loop: it absorbs `break` and `continue`. -/
def LoopFlow (m : Module) (W : World) (tenv : TEnv) (penv : PEnv) (s : St) : Flow → Prop
  | .normal _ => True
  | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s v
  | _ => False

/-- A place denotes a typed location, or is a variable that holds a reference. -/
def PlaceOk (m : Module) (G : Nat) (env : Env) (s : Store) (p : Place) (l : Loc) (t : Ty) : Prop :=
  (t.refTarget = true ∧ LocOk m G s l t) ∨
  (∃ x lv si v, p = .var x ∧ env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
    l = ⟨.local env.act si x, []⟩ ∧ lv.ty = t ∧ t.isRefLike = true ∧
    s.roots[RootInst.local env.act si x]? = some v ∧ HasTy m G s v t)

/-- A sampled run lies inside a typed array, and a run of a resizable owner
starts at its first element. -/
def ViewOk (s : Store) (vw : ViewVal) (el : Ty) : Prop :=
  el.flat = true ∧ SliceTy s vw.loc vw.start vw.len el ∧
  (vw.resizable = true → vw.start = 0 ∧ LocTy s vw.loc (.grow el))

theorem ViewOk.mono {s s' : Store} {vw : ViewVal} {el : Ty} (hle : StoreLe s s')
    (h : ViewOk s vw el) : ViewOk s' vw el :=
  ⟨h.1, h.2.1.mono hle, fun hr => ⟨(h.2.2 hr).1, LocTy.mono hle (h.2.2 hr).2⟩⟩

/-- The values a construct binds in its block: distinct variables of the block,
numbered in `[lo, hi)`, each with a value of its type that points into its
annotation. -/
def PreOk (m : Module) (W : World) (penv : PEnv) (env1 : Env) (sc lo hi : Nat) (st : Store)
    (pre : List (VarId × Val)) : Prop :=
  (pre.map Prod.fst).Nodup ∧
  ∀ x v, (x, v) ∈ pre → lo ≤ x ∧ x < hi ∧ ∃ lv, env1.vars[x]? = some lv ∧ lv.scope = sc ∧
    lv.ty.storable = true ∧ HasTy m W.G st v lv.ty ∧
    ∀ r, Targets v r → ∃ ann, penv.ann x = some ann ∧ Gam env1 W.P ann r

/-- The declared effects of an implementation touch only initialized globals. -/
def SumOk (G : Nat) (P : Nat → RootInst → Prop) (impl : Impl) (ctx : Context) : Prop :=
  ∃ sm, impl.summary = .known sm ∧
    ∀ t, (t ∈ expandTargets impl ctx sm.reads ∨ t ∈ expandTargets impl ctx sm.writes ∨
      t ∈ expandTargets impl ctx sm.grows) → TargetOk G P t

section Specs
variable (m : Module) (prof : NumProfile)

def ExprSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (e : Expr) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef),
    Perm m W → Frame m W tenv penv env s →
    tyExpr tenv e tn = .ok (ty, tn') → rpExpr penv e rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalExpr n ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r)

def BlockValueSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (b : Block) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef) (rng : Nat × Nat),
    Perm m W → Frame m W tenv penv env s →
    tyBlock (exprEnv tenv) [] b tn = .ok (ty, tn') →
    rpBlockValue penv [] b rst = .ok ((rho, rng), rst') → EffLe rst'.eff W.E →
    Sat (blockValue n ⟨prof, m⟩ env b) s (fun v s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r)

/-- An argument is typed as the validator types it at a call. -/
def ArgTy (tenv : TEnv) (a : Arg) (tn : Nat) (ty : Ty) (tn' : Nat) : Prop :=
  match a with
  | .byVal e => tyExpr tenv e tn = .ok (ty, tn')
  | .byRef mu p => ∃ t mu', tyPlace tenv p tn = .ok ((t, mu'), tn') ∧ t.refTarget = true ∧ ty = .ref mu t

def ArgRp (penv : PEnv) (a : Arg) (rst : RState) (rho : List RootRef) (rst' : RState) : Prop :=
  match a with
  | .byVal e => rpExpr penv e rst = .ok (rho, rst')
  | .byRef _ p => rpPlace penv p rst = .ok (rho, rst')

def ArgSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (a : Arg) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef),
    Perm m W → Frame m W tenv penv env s →
    ArgTy tenv a tn ty tn' → ArgRp penv a rst rho rst' → EffLe rst'.eff W.E →
    Sat (evalArg n ⟨prof, m⟩ env a) s (fun v s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r)

def BoundSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (b : Bound) (len : Nat) (d : Int)
    (tn tn' : Nat) (rst rst' : RState),
    Perm m W → Frame m W tenv penv env s →
    tyBound tenv b tn = .ok ((), tn') → rpBound penv b rst = .ok ((), rst') → EffLe rst'.eff W.E →
    Sat (evalBound n ⟨prof, m⟩ env len d b) s (fun _ s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s')

def PlaceSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (p : Place) (tn tn' : Nat) (t : Ty)
    (mu : Bool) (rst rst' : RState) (rho : List RootRef),
    Perm m W → Frame m W tenv penv env s →
    tyPlace tenv p tn = .ok ((t, mu), tn') → rpPlace penv p rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalPlace n ⟨prof, m⟩ env p) s (fun l s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ PlaceOk m W.G env s'.store p l t ∧
      Gam env W.P rho l.root)

def ViewSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (v : View) (tn tn' : Nat) (el : Ty)
    (mu : Bool) (rst rst' : RState) (rho : List RootRef),
    Perm m W → Frame m W tenv penv env s →
    tyView tenv v tn = .ok ((el, mu), tn') → rpView penv v rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalView n ⟨prof, m⟩ env v) s (fun vw s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ ViewOk s'.store vw el ∧
      Gam env W.P rho vw.loc.root)

def CallSpec (n : Nat) : Prop :=
  ∀ (G : Nat) (P : Nat → RootInst → Prop) (depth : Nat) (c : ContextId) (vals : List Val) (s : St)
    (ctx : Context) (impl : Impl),
    m.contexts[c]? = some ctx → m.impls[ctx.impl]? = some impl →
    StoreInv m G s → vals.length = impl.params.size →
    (∀ i v, vals[i]? = some v → ∃ lv, impl.vars[i]? = some lv ∧ HasTy m G s.store v lv.ty ∧
      ∀ r, Targets v r → ∃ ann, (ctx.varRoots.find? (·.1 == i)).map (·.2) = some ann ∧
        Gam noEnv P ann r) →
    (∀ i a si x, P i (.local a si x) → si < s.nextScope) →
    (m.globals.size ≤ G ∨ SumOk G P impl ctx) →
    Sat (enterCall n ⟨prof, m⟩ depth c vals) s (fun v s' =>
      StoreInv m G s' ∧ Ext [] s s' ∧
      ((impl.results.toList = [] ∧ v = .unit) ∨
        ∃ t, impl.results.toList = [t] ∧ HasTy m G s'.store v t) ∧
      ∀ r, Targets v r → ∃ declared, ctx.resultRoots = [declared] ∧ Gam noEnv P declared r)

def BlockSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv tenv1 tenv2 : TEnv) (penv : PEnv) (env : Env) (s : St)
    (pre : List (VarId × Val)) (sc : Nat) (stmts : List Stmt) (value : Option Expr)
    (tn1 tn2 tn3 : Nat) (ty : Ty) (rst1 rst2 rst3 : RState) (rho : List RootRef) (lo : Nat),
    Perm m W → Frame m W tenv penv env s → sc ∉ tenv.scopes →
    TSame { tenv with scopes := sc :: tenv.scopes } tenv1 →
    (∀ y, y ∈ tenv1.visible ↔ y ∈ pre.map Prod.fst ∨ y ∈ tenv.visible) →
    PreOk m W penv { env with scopes := (sc, s.nextScope) :: env.scopes } sc lo rst1.nextVar s.store pre →
    tyStmts tenv1 sc stmts tn1 = .ok (tenv2, tn2) →
    (match value with
      | none => ty = .unit
      | some e => tyExpr tenv2 e tn2 = .ok (ty, tn3)) →
    rpStmts { penv with scopes := sc :: penv.scopes } stmts rst1 = .ok ((), rst2) →
    (match value with
      | none => rho = [] ∧ rst3 = rst2
      | some e => rpExpr { penv with scopes := sc :: penv.scopes } e rst2 = .ok (rho, rst3)) →
    EffLe rst3.eff W.E →
    (∀ y, RootRef.local y ∈ rho → ¬ (lo ≤ y ∧ y < rst3.nextVar)) →
    Sat (execBlock n ⟨prof, m⟩ env pre (.mk sc stmts value)) s (fun fl s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧
      match fl with
      | .normal v => HasTy m W.G s'.store v ty ∧ (∀ r, Targets v r → Gam env W.P rho r) ∧
          stmtsDiverge stmts = false
      | .brk => tenv.loops ≠ 0 ∧ stmtsHaveBreak stmts = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v)

def StmtsSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat) (ss : List Stmt)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    Perm m W → Frame m W tenv penv env s → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    tyStmts tenv sc ss tn = .ok (tenv', tn') → rpStmts penv ss rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmts n ⟨prof, m⟩ env ss) s (fun fl s' =>
      (∃ tenv'', TSame tenv tenv'' ∧ Frame m W tenv'' penv env s' ∧
        (∀ v, fl = .normal v → tenv'' = tenv')) ∧
      ExtS env s s' ∧ TopB env lo rst'.nextVar s' ∧
      match fl with
      | .normal v => v = .unit ∧ stmtsDiverge ss = false
      | .brk => tenv.loops ≠ 0 ∧ stmtsHaveBreak ss = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v)

def StmtSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat) (st : Stmt)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    Perm m W → Frame m W tenv penv env s → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    tyStmt tenv sc st tn = .ok (tenv', tn') → rpStmt penv st rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmt n ⟨prof, m⟩ env st) s (fun fl s' =>
      Frame m W tenv' penv env s' ∧ TSame tenv tenv' ∧ ExtS env s s' ∧ TopB env lo rst'.nextVar s' ∧
      match fl with
      | .normal _ => st.diverges = false
      | .brk => tenv.loops ≠ 0 ∧ st.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v)

/-- A printed argument is an integer or a boolean. -/
def PrintTy (tenv : TEnv) (a : PrintArg) (tn tn' : Nat) : Prop :=
  match a with
  | .text _ => tn' = tn
  | .expr e => ∃ ty, tyExpr tenv e tn = .ok (ty, tn') ∧ ((∃ t, ty = .int t) ∨ ty = .bool)

def PrintRp (penv : PEnv) (a : PrintArg) (rst rst' : RState) : Prop :=
  match a with
  | .text _ => rst' = rst
  | .expr e => ∃ rho, rpExpr penv e rst = .ok (rho, rst')

def PrintArgSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (a : PrintArg) (tn tn' : Nat)
    (rst rst' : RState),
    Perm m W → Frame m W tenv penv env s →
    PrintTy tenv a tn tn' → PrintRp penv a rst rst' → EffLe rst'.eff W.E →
    Sat (execPrintArg n ⟨prof, m⟩ env a) s (fun _ s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s')

def WhileSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (c : Expr) (body : Block)
    (tn tn1 tn2 : Nat) (bty : Ty) (rst rst1 rst2 : RState) (rhoc rb : List RootRef) (rng : Nat × Nat),
    Perm m W → Frame m W tenv penv env s →
    tyExpr tenv c tn = .ok (.bool, tn1) →
    tyBlock { tenv with loops := tenv.loops + 1 } [] body tn1 = .ok (bty, tn2) →
    rpExpr penv c rst = .ok (rhoc, rst1) → rpBlockValue penv [] body rst1 = .ok ((rb, rng), rst2) →
    EffLe rst2.eff W.E →
    Sat (execWhile n ⟨prof, m⟩ env c body) s (fun fl s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ LoopFlow m W tenv penv s' fl ∧
      (∀ v, fl = .normal v → c = .bool true → body.hasBreak = true))

def RangeSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (x : VarId) (t : IntTy) (i hi : Int)
    (body : Block) (tn1 tn2 : Nat) (bty : Ty) (rst1 rst2 : RState) (rb : List RootRef) (rng : Nat × Nat),
    Perm m W → Frame m W tenv penv env s →
    tyBlock { tenv with loops := tenv.loops + 1 } [(x, .int t)] body tn1 = .ok (bty, tn2) →
    rpBlockValue penv [x] body rst1 = .ok ((rb, rng), rst2) → EffLe rst2.eff W.E →
    Sat (execRange n ⟨prof, m⟩ env x t i hi body) s (fun fl s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ LoopFlow m W tenv penv s' fl)

def EachSpec (n : Nat) : Prop :=
  ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (body : Block) (vw : ViewVal) (i : Nat) (el xty : Ty) (rho : List RootRef)
    (tn1 tn2 : Nat) (bty : Ty) (rst1 rst2 : RState) (rb : List RootRef) (rng : Nat × Nat),
    Perm m W → Frame m W tenv penv env s →
    ViewOk s.store vw el → Gam env W.P rho vw.loc.root →
    (if byRef = true then (∃ mx, xty = .ref mx el) ∧
        bindRootsV penv (body.scope :: penv.scopes) x rho = .ok ()
      else xty = el) →
    tyBlock { tenv with loops := tenv.loops + 1 }
      ((x, xty) :: (match idx with | some j => [(j, Ty.int .i64)] | none => [])) body tn1 = .ok (bty, tn2) →
    rpBlockValue penv (x :: idx.toList) body rst1 = .ok ((rb, rng), rst2) → EffLe rst2.eff W.E →
    Sat (execEach n ⟨prof, m⟩ env x idx byRef body vw i) s (fun fl s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ LoopFlow m W tenv penv s' fl)

/-- Every evaluation function at fuel `n` meets its statement. -/
structure Specs (n : Nat) : Prop where
  expr : ExprSpec m prof n
  blockValue : BlockValueSpec m prof n
  arg : ArgSpec m prof n
  bound : BoundSpec m prof n
  place : PlaceSpec m prof n
  view : ViewSpec m prof n
  call : CallSpec m prof n
  block : BlockSpec m prof n
  stmts : StmtsSpec m prof n
  stmt : StmtSpec m prof n
  printArg : PrintArgSpec m prof n
  while_ : WhileSpec m prof n
  range : RangeSpec m prof n
  each : EachSpec m prof n

end Specs

end Goose.Core.Sound
