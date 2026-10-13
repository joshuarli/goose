import Goose.Core.Sound.Scope
import Goose.Core.Sound.Invert
import Goose.Core.Sound.Context
import Goose.Core.Sound.Retain
import Goose.Core.Sound.CallPreservation

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
def PlaceOk (m : Module) (G : Nat) (P : Nat → RootInst → Prop) (penv : PEnv) (env : Env) (s : Store)
    (p : Place) (l : Loc) (t : Ty) : Prop :=
  (t.refTarget = true ∧ LocOk m G s l t ∧ HeaderLoc l t) ∨
  (∃ x lv si v, p = .var x ∧ env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
    l = ⟨.local env.act si x, []⟩ ∧ lv.ty = t ∧ t.isRefLike = true ∧
    s.roots[RootInst.local env.act si x]? = some v ∧ HasTy m G s v t) ∨
  -- The slice variable a reference parameter points at.
  (∃ x lv mu0 mu E ann, p = .deref (.read (.var x)) ∧ env.vars[x]? = some lv ∧
    lv.ty = .ref mu0 (.slice mu E) ∧ t = .slice mu E ∧ E.flat = true ∧ l.path = [] ∧
    penv.ann x = some ann ∧ Gam env P ann l.root ∧ s.roots[l.root]? ≠ none)

theorem PlaceOk.ownerHeader {m : Module} {G : Nat} {P : Nat → RootInst → Prop} {penv : PEnv}
    {env : Env} {s : Store} {p : Place} {l : Loc} {t : Ty}
    (h : PlaceOk m G P penv env s p l t) (howner : t.ownerElem?.isSome = true) : l.path = [] := by
  rcases h with ⟨_, _, hheader⟩ |
    ⟨x, lv, si, v, _, _, _, _, ht, hrl, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, ht, _, _, _, _, _⟩
  · exact hheader howner
  · cases t <;> simp [Ty.ownerElem?, Ty.isRefLike] at howner hrl
  · rw [ht] at howner
    simp [Ty.ownerElem?] at howner

/-- A typed place of owner type cannot denote a nonempty path. -/
theorem PlaceOk.ownerHeader_excludes_nonempty {m : Module} {G : Nat} {P : Nat → RootInst → Prop}
    {penv : PEnv} {env : Env} {s : Store} {p : Place} {l : Loc} {t : Ty}
    (h : PlaceOk m G P penv env s p l t) (howner : t.ownerElem?.isSome = true)
    (hnonempty : l.path ≠ []) : False := by
  exact hnonempty (h.ownerHeader howner)

/-- A sampled run lies inside a typed array, and a run of a resizable owner
starts at its first element. -/
def ViewOk (s : Store) (vw : ViewVal) (el : Ty) : Prop :=
  el.flat = true ∧ SliceTy s vw.loc vw.start vw.len el ∧
  (vw.resizable = true → vw.start = 0 ∧
    (LocTy s vw.loc (.grow el) ∨ LocTy s vw.loc (.growshrink el)))

/-- A resizable iteration rechecks the owner's current length rather than
requiring the run sampled before the loop to remain within that length. -/
def EachViewOk (s : Store) (vw : ViewVal) (el : Ty) : Prop :=
  el.flat = true ∧
  (vw.resizable = false → SliceTy s vw.loc vw.start vw.len el) ∧
  (vw.resizable = true → vw.start = 0 ∧
    (LocTy s vw.loc (.grow el) ∨ LocTy s vw.loc (.growshrink el)))

theorem ViewOk.eachView {s : Store} {vw : ViewVal} {el : Ty}
    (h : ViewOk s vw el) : EachViewOk s vw el :=
  ⟨h.1, fun _ => h.2.1, h.2.2⟩

theorem ViewOk.mono {s s' : Store} {vw : ViewVal} {el : Ty} (hle : StoreLe s s')
    (h : ViewOk s vw el) : ViewOk s' vw el :=
  ⟨h.1, h.2.1.mono hle, fun hr =>
    ⟨(h.2.2 hr).1, (h.2.2 hr).2.elim
      (fun h => Or.inl (LocTy.mono hle h))
      (fun h => Or.inr (LocTy.mono hle h))⟩⟩

/-- A sampled view realizes the alias chosen from its checked source. Fixed
runs retain their sampled bounds; resizable runs retain the owner header.
The bound-location fact makes a retained owner usable after each body. -/
inductive ViewAliases (m : Module) (W : World) (penv : PEnv) (env : Env) (s : Store)
    (source : View) (vw : ViewVal) (el : Ty) : Prop
  | fixed (resizable : vw.resizable = false)
      (realized : ∀ path alias, penv.access.aliasView path source = .ok [alias] →
        alias.ty = .slice .readOnly el ∧
          AliasAt m W env s alias (.slice vw.loc vw.start vw.len))
  | owner (resizable : vw.resizable = true) (place : Place) (owner : Ty)
      (sourceEq : source = .of place)
      (ownerType : owner = .grow el ∨ owner = .growshrink el)
      (typeLookup : penv.access.placeType? place = some owner)
      (bound : ¬ Unbound m W.G vw.loc owner)
      (realized : ∀ path alias, penv.access.aliasPlace path place = .ok [alias] →
        alias.ty = .ref .mutable owner ∧ AliasAt m W env s alias (.ref vw.loc))

/-- The values a construct binds in its block: distinct variables of the block,
numbered in `[lo, hi)`, each with a value of its type that points into its
annotation. -/
def PreOk (m : Module) (W : World) (penv : PEnv) (env1 : Env) (sc lo hi : Nat) (st : Store)
    (pre : List (VarId × Val)) : Prop :=
  (pre.map Prod.fst).Nodup ∧
  ∀ x v, (x, v) ∈ pre → lo ≤ x ∧ x < hi ∧ ∃ lv, env1.vars[x]? = some lv ∧ lv.scope = sc ∧
    lv.ty.paramOk = true ∧ HasTy m W.G st v lv.ty ∧
    ∀ r, Targets v r → ∃ ann, penv.ann x = some ann ∧ Gam env1 W.P ann r

/-- The declared effects of an implementation touch only initialized globals. -/
def SumOk (G : Nat) (P : Nat → RootInst → Prop) (impl : Impl) (ctx : Context) : Prop :=
  ∃ sm, impl.summary = .known sm ∧
    ∀ t, (t ∈ expandTargets impl ctx sm.reads ∨ t ∈ expandTargets impl ctx sm.writes ∨
      t ∈ expandTargets impl ctx sm.grows ∨ t ∈ expandTargets impl ctx sm.shrinks) → TargetOk G P t

/-- Each slice variable of a caller that was passed by reference holds a slice
of its element type rooted within what the variable allows. -/
def OuterOk (m : Module) (G : Nat) (D : RootInst → Ty → Prop) (A : RootInst → RootInst → Prop)
    (s : St) : Prop :=
  ∀ r E, D r E → ∃ v, s.store.roots[r]? = some v ∧
    HasTy m G s.store v (.slice .mutable E) ∧ ∀ t, Targets v t → A r t

/-- Argument evaluation follows the checked expression or place occurrence. -/
inductive ArgContext (m : Module) (plans : Array (Array DemandPoint)) (path : List Nat) : Arg → Type
  | byVal {e : Expr}
      (context : EvaluationContext m plans path (.expression e) .expression) :
      ArgContext m plans path (.byVal e)
  | byRef {mu : Mutability} {p : Place}
      (context : EvaluationContext m plans path (.place p) .place) :
      ArgContext m plans path (.byRef mu p)

def ArgContext.inputFuture {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : Arg}
    (context : ArgContext m plans path a) : List VarId :=
  match context with
  | .byVal context => context.inputFuture
  | .byRef context => context.inputFuture

def ArgContext.outputFuture {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : Arg}
    (context : ArgContext m plans path a) : List VarId :=
  match context with
  | .byVal context => context.outputFuture
  | .byRef context => context.outputFuture

def ArgContext.retained {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : Arg}
    (context : ArgContext m plans path a) : List RetainedAlias :=
  match context with
  | .byVal context => context.retained
  | .byRef context => context.retained

def ArgContext.ActiveMatches {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : Arg}
    (context : ArgContext m plans path a) (tenv : TEnv) : Prop :=
  match context with
  | .byVal context => context.ActiveMatches tenv
  | .byRef context => context.ActiveMatches tenv

def ArgContext.AccessMatches {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : Arg}
    (context : ArgContext m plans path a) (tenv : TEnv) (penv : PEnv) : Prop :=
  match context with
  | .byVal context => context.AccessMatches tenv penv
  | .byRef context => context.AccessMatches tenv penv

/-- Text keeps the surrounding demand and protection function because it has no child occurrence. -/
inductive PrintArgContext (m : Module) (plans : Array (Array DemandPoint)) (path : List Nat) : PrintArg → Type
  | text {text : String} (future : List VarId) (retained : List RetainedAlias)
      (shrinking : (Nat → RootInst → Prop) → Observation → RootInst → Prop) :
      PrintArgContext m plans path (.text text)
  | expr {e : Expr}
      (context : EvaluationContext m plans path (.expression e) .expression) :
      PrintArgContext m plans path (.expr e)

def PrintArgContext.inputFuture {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : PrintArg}
    (context : PrintArgContext m plans path a) : List VarId :=
  match context with
  | .text future _ _ => future
  | .expr context => context.inputFuture

def PrintArgContext.outputFuture {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : PrintArg}
    (context : PrintArgContext m plans path a) : List VarId :=
  match context with
  | .text future _ _ => future
  | .expr context => context.outputFuture

def PrintArgContext.retained {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : PrintArg}
    (context : PrintArgContext m plans path a) : List RetainedAlias :=
  match context with
  | .text _ retained _ => retained
  | .expr context => context.retained

def PrintArgContext.ActiveMatches {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : PrintArg}
    (context : PrintArgContext m plans path a) (tenv : TEnv) : Prop :=
  match context with
  | .text _ _ _ => True
  | .expr context => context.ActiveMatches tenv

def PrintArgContext.AccessMatches {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : PrintArg}
    (context : PrintArgContext m plans path a) (tenv : TEnv) (penv : PEnv) : Prop :=
  match context with
  | .text _ _ _ => True
  | .expr context => context.AccessMatches tenv penv

def ArgContext.mayShrink {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : Arg} (context : ArgContext m plans path a)
    (P : Nat → RootInst → Prop) (observation : Observation) : RootInst → Prop :=
  match context with
  | .byVal context => context.mayShrink P observation
  | .byRef context => context.mayShrink P observation

def PrintArgContext.mayShrink {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {a : PrintArg} (context : PrintArgContext m plans path a)
    (P : Nat → RootInst → Prop) (observation : Observation) : RootInst → Prop :=
  match context with
  | .text _ _ shrinking => shrinking P observation
  | .expr context => context.mayShrink P observation

/-- A statement suffix advances lexical activity without allocating a new path. -/
def blockSuffixActive {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {sc : Nat} {all : List Stmt} {value : Option Expr}
    (context : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (offset : Nat) : List VarId :=
  let active := match context with
    | .pilot _ active => active
    | .shrink _ context => context.expected.frame.active
  (DemandNode.block (.mk sc all value)).visibleForChild active offset

/-- Pilot keeps every binding active at the suffix; shrink keeps variables
used by the remaining statements, the block value and its enclosing future. -/
def blockSuffixFuture {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {sc : Nat} {all : List Stmt} {value : Option Expr}
    (context : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (offset : Nat) : List VarId :=
  match context with
  | .pilot _ _ => blockSuffixActive context offset
  | .shrink _ _ => (all.drop offset).flatMap Stmt.variables ++
      value.toList.flatMap Expr.variables ++ context.outputFuture

/-- Replay supplies the exact effects checked for the implementation body. -/
def ContextEff (m : Module) (impl : Impl) (ctx : Context) (E : Eff) : Prop :=
  ∃ rho rng rst,
    rpBlockValue ⟨m, impl, ctx, []⟩ [] impl.body
      ⟨impl.params.size, {}⟩ = .ok ((rho, rng), rst) ∧ rst.eff = E

/-! Shrink evaluation carries parameter classification across store changes so
checked root requests remain tied to their observed owner capabilities. -/
section Specs
variable (m : Module) (prof : NumProfile) (plans : Array (Array DemandPoint))

def ExprSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (e : Expr)
    (ec : EvaluationContext m plans path (.expression e) .expression)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyExpr tenv e tn = .ok (ty, tn') → rpExpr penv e rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalExpr n ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

def BlockValueSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (b : Block)
    (ec : EvaluationContext m plans path (.block b) .block)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef) (rng : Nat × Nat),
    ec.ActiveMatches (exprEnv tenv) → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyBlock (exprEnv tenv) [] b tn = .ok (ty, tn') →
    rpBlockValue penv [] b rst = .ok ((rho, rng), rst') → EffLe rst'.eff W.E →
    Sat (blockValue n ⟨prof, m⟩ env b) s (fun v s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

/-- An argument is typed as the validator types it at a call. -/
def ArgTy (tenv : TEnv) (a : Arg) (tn : Nat) (ty : Ty) (tn' : Nat) : Prop :=
  match a with
  | .byVal e => tyExpr tenv e tn = .ok (ty, tn')
  | .byRef mu p => ∃ t, ∃ caps : Bool × Bool, tyPlace tenv p tn = .ok (⟨t, caps.1, caps.2⟩, tn') ∧
      (t.refTarget = true ∨ (t.isSlice = true ∧ caps.1 = true ∧ p.sliceArg = true)) ∧ ty = .ref mu t

def ArgRp (penv : PEnv) (a : Arg) (rst : RState) (rho : List RootRef) (rst' : RState) : Prop :=
  match a with
  | .byVal e => rpExpr penv e rst = .ok (rho, rst')
  | .byRef _ p => rpPlace penv p rst = .ok (rho, rst')

def ArgSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (a : Arg) (ac : ArgContext m plans path a)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef),
    ac.ActiveMatches tenv → ac.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ac.mayShrink W.P observation) →
    ObservedSafe m W (ac.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ac.inputFuture →
    ArgTy tenv a tn ty tn' → ArgRp penv a rst rho rst' → EffLe rst'.eff W.E →
    Sat (evalArg n ⟨prof, m⟩ env a) s (fun v s' =>
      Frame m W tenv penv env s' ac.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ac.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ac.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

def BoundSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (b : Bound)
    (ec : EvaluationContext m plans path (.bound b) .bound)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (len : Nat) (d : Int)
    (tn tn' : Nat) (rst rst' : RState),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyBound tenv b tn = .ok ((), tn') → rpBound penv b rst = .ok ((), rst') → EffLe rst'.eff W.E →
    Sat (evalBound n ⟨prof, m⟩ env len d b) s (fun _ s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

def PlaceSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (p : Place)
    (ec : EvaluationContext m plans path (.place p) .place)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (tn tn' : Nat) (t : Ty)
    (mu contents : Bool) (rst rst' : RState) (rho : List RootRef),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyPlace tenv p tn = .ok (⟨t, mu, contents⟩, tn') → rpPlace penv p rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalPlace n ⟨prof, m⟩ env p) s (fun l s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧
      PlaceOk m W.G W.P penv env s'.store p l t ∧
      Gam env W.P rho l.root ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

def ViewSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (v : View)
    (ec : EvaluationContext m plans path (.view v) .view)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (tn tn' : Nat) (el : Ty)
    (mu : Bool) (rst rst' : RState) (rho : List RootRef),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyView tenv v tn = .ok ((el, mu), tn') → rpView penv v rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalView n ⟨prof, m⟩ env v) s (fun vw s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ ViewOk s'.store vw el ∧
      Gam env W.P rho vw.loc.root ∧ ViewAliases m W penv env s'.store v vw el ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

def CallSpec (n : Nat) : Prop :=
  ∀ (G : Nat) (P : Nat → RootInst → Prop) (D : RootInst → Ty → Prop)
    (A : RootInst → RootInst → Prop) (depth : Nat) (c : ContextId) (vals : List Val) (s : St)
    (ctx : Context) (impl : Impl) (E : Eff) (observation : Observation)
    (root : EvaluationContext m plans [] (.block impl.body) .block),
    root.OwnerMatches c → ContextEff m impl ctx E →
    m.contexts[c]? = some ctx → m.impls[ctx.impl]? = some impl →
    StoreInv m G s (ObservationDemand observation) →
    ObservedSafe m ⟨G, P, E, s.nextScope, D, A⟩ (root.mayShrink P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m P D observation s.store) →
    ShrinkProtected D A (root.mayShrink P observation) → vals.length = impl.params.size →
    (∀ i v, vals[i]? = some v → ∃ lv, impl.vars[i]? = some lv ∧ HasTy m G s.store v lv.ty ∧
      ∀ r, Targets v r → ∃ ann, (ctx.varRoots.find? (·.1 == i)).map (·.2) = some ann ∧
        Gam noEnv P ann r) →
    (∀ i a si x, P i (.local a si x) → si < s.nextScope) →
    (∀ r t, A r t → Older t r) →
    (∀ r E, D r E → ∃ a si x, r = RootInst.local a si x ∧ si < s.nextScope) →
    (∀ r E E', D r E → D r E' → E = E') →
    OuterOk m G D A s →
    (∀ x cont, (ctx.contentRoots.find? (·.1 == x)).map (·.2) = some cont →
      PRef P D A ⟨m, impl, ctx, []⟩ impl.vars x cont) →
    (m.globals.size ≤ G ∨ SumOk G P impl ctx) →
    Sat (enterCall n ⟨prof, m⟩ depth c vals) s (fun v s' =>
      StoreInv m G s' (ObservationDemand observation) ∧
      CallTransition m G observation.roots observation.values
        (fun r => ∃ element, D r element) s s' ∧
      ObservedSafe m ⟨G, P, E, s.nextScope, D, A⟩ (root.mayShrink P observation) observation s'.store ∧
      PilotStoreLe m s s' ∧
      OuterOk m G D A s' ∧
      ((impl.results.toList = [] ∧ v = .unit) ∨
        ∃ t, impl.results.toList = [t] ∧ HasTy m G s'.store v t) ∧
      (∀ r, Targets v r → ∃ declared, ctx.resultRoots = [declared] ∧ Gam noEnv P declared r) ∧
      (m.profile = .shrink → ClassifiedParameters m P D observation s'.store))

def BlockSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (sc : Nat) (stmts : List Stmt) (value : Option Expr)
    (ec : EvaluationContext m plans path (.block (.mk sc stmts value)) .block)
    (observation : Observation) (W : World) (tenv tenv1 tenv2 : TEnv) (penv : PEnv) (env : Env) (s : St)
    (pre : List (VarId × Val)) (tn1 tn2 tn3 : Nat) (ty : Ty) (rst1 rst2 rst3 : RState) (rho : List RootRef) (lo : Nat),
    ec.ActiveMatches tenv1 → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture → sc ∉ tenv.scopes →
    TSame { tenv with scopes := sc :: tenv.scopes } tenv1 →
    (∀ y, y ∈ tenv1.visible ↔ y ∈ pre.map Prod.fst ∨ y ∈ tenv.visible) →
    PreOk m W penv { env with scopes := (sc, s.nextScope) :: env.scopes } sc lo rst1.nextVar s.store pre →
    lo ≤ rst1.nextVar →
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
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧
      (match fl with
      | .normal v => HasTy m W.G s'.store v ty ∧ (∀ r, Targets v r → Gam env W.P rho r) ∧
          stmtsDiverge m.noReturn stmts = false
      | .brk => tenv.loops ≠ 0 ∧ stmtsHaveBreak stmts = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

def StmtsSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (sc : Nat) (all : List Stmt) (value : Option Expr)
    (bc : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (offset : Nat) (ss : List Stmt)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    offset ≤ all.length → ss = all.drop offset →
    (∀ x, x ∈ blockSuffixActive bc offset ↔ x ∈ tenv.visible) →
    bc.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (bc.mayShrink W.P observation) →
    ObservedSafe m W (bc.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s (blockSuffixFuture bc offset) → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    lo ≤ rst.nextVar →
    tyStmts tenv sc ss tn = .ok (tenv', tn') → rpStmts penv ss rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmts n ⟨prof, m⟩ env ss) s (fun fl s' =>
      (∃ tenv'', TSame tenv tenv'' ∧ Frame m W tenv'' penv env s' (blockSuffixFuture bc all.length) ∧
        (∀ v, fl = .normal v → tenv'' = tenv')) ∧
      FootprintS env (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (bc.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store bc.retained ∧
      PilotStoreLe m s s' ∧ TopB env lo rst'.nextVar s' ∧
      (match fl with
      | .normal v => v = .unit ∧ stmtsDiverge m.noReturn ss = false
      | .brk => tenv.loops ≠ 0 ∧ stmtsHaveBreak ss = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

def StmtSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (st : Stmt)
    (ec : EvaluationContext m plans path (.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    lo ≤ rst.nextVar →
    tyStmt tenv sc st tn = .ok (tenv', tn') → rpStmt penv st rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmt n ⟨prof, m⟩ env st) s (fun fl s' =>
      Frame m W tenv' penv env s' ec.outputFuture ∧ FootprintS env (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ TSame tenv tenv' ∧ TopB env lo rst'.nextVar s' ∧
      (match fl with
      | .normal _ => st.diverges m.noReturn = false
      | .brk => tenv.loops ≠ 0 ∧ st.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

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
  ∀ (path : List Nat) (a : PrintArg) (ac : PrintArgContext m plans path a)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (tn tn' : Nat)
    (rst rst' : RState),
    ac.ActiveMatches tenv → ac.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ac.mayShrink W.P observation) →
    ObservedSafe m W (ac.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ac.inputFuture →
    PrintTy tenv a tn tn' → PrintRp penv a rst rst' → EffLe rst'.eff W.E →
    Sat (execPrintArg n ⟨prof, m⟩ env a) s (fun _ s' =>
      Frame m W tenv penv env s' ac.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ac.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ac.retained ∧
      PilotStoreLe m s s' ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

def WhileSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (c : Expr) (body : Block) (origin : OriginId)
    (ec : EvaluationContext m plans path (.statement (.while c body origin)) .statement)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (tn tn1 tn2 : Nat) (bty : Ty) (rst rst1 rst2 : RState) (rhoc rb : List RootRef) (rng : Nat × Nat),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyExpr tenv c tn = .ok (.bool, tn1) →
    tyBlock { tenv with loops := tenv.loops + 1 } [] body tn1 = .ok (bty, tn2) →
    rpExpr penv c rst = .ok (rhoc, rst1) → rpBlockValue penv [] body rst1 = .ok ((rb, rng), rst2) →
    EffLe rst2.eff W.E →
    Sat (execWhile n ⟨prof, m⟩ env c body) s (fun fl s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ LoopFlow m W tenv penv s' fl ∧
      (∀ v, fl = .normal v → c = .bool true → body.hasBreak = true) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

/-- Iteration consumes sampled bounds and retains the body and enclosing continuation. -/
def RangeSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (x : VarId) (lower upper : Expr) (body : Block) (origin : OriginId)
    (ec : EvaluationContext m plans path (.statement (.forRange x lower upper body origin)) .statement)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (t : IntTy) (i hi : Int)
    (tn1 tn2 : Nat) (bty : Ty) (rst1 rst2 : RState) (rb : List RootRef) (rng : Nat × Nat),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s (body.variables ++ ec.outputFuture) →
    (∃ lv, env.vars[x]? = some lv ∧ lv.scope = body.scope ∧ lv.ty = .int t) → x < rst1.nextVar →
    tyBlock { tenv with loops := tenv.loops + 1, visible := x :: tenv.visible } [] body tn1 =
      .ok (bty, tn2) →
    rpBlockValue penv [] body rst1 = .ok ((rb, rng), rst2) → EffLe rst2.eff W.E →
    (∀ y, RootRef.local y ∈ rb → ¬ (x ≤ y ∧ y < rst1.nextVar)) →
    Sat (execRange n ⟨prof, m⟩ env x t i hi body) s (fun fl s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ LoopFlow m W tenv penv s' fl ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

/-- The source view identifies the checked loop occurrence; the runtime view
carries its iteration cursor and the owner's current typing. -/
def EachSpec (n : Nat) : Prop :=
  ∀ (path : List Nat) (x : VarId) (idx : Option VarId) (sourceView : View)
    (byRef : Bool) (body : Block) (origin : OriginId)
    (ec : EvaluationContext m plans path (.statement (.forEach x idx sourceView byRef body origin)) .statement)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (vw : ViewVal) (i : Nat) (el : Ty) (rho : List RootRef)
    (tn1 tn2 : Nat) (bty : Ty) (rst1 rst2 : RState) (rb : List RootRef) (rng : Nat × Nat),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s (body.variables ++ ec.outputFuture) →
    EachViewOk s.store vw el → ViewAliases m W penv env s.store sourceView vw el →
    Gam env W.P rho vw.loc.root →
    (∃ lv, env.vars[x]? = some lv ∧ lv.scope = body.scope ∧ lv.ty.storable = true ∧
      (if byRef = true then (∃ mx, lv.ty = .ref mx el) ∧
          bindRootsV penv (body.scope :: penv.scopes) x rho = .ok ()
        else lv.ty = el)) →
    (∀ j, idx = some j → j = x + 1 ∧ ∃ lj, env.vars[j]? = some lj ∧ lj.scope = body.scope ∧
      lj.ty = .int .i64) →
    x + idx.toList.length < rst1.nextVar →
    tyBlock { tenv with loops := tenv.loops + 1, visible := x :: idx.toList ++ tenv.visible } [] body
      tn1 = .ok (bty, tn2) →
    rpBlockValue penv [] body rst1 = .ok ((rb, rng), rst2) → EffLe rst2.eff W.E →
    (∀ y, RootRef.local y ∈ rb → ¬ (x ≤ y ∧ y < rst1.nextVar)) →
    Sat (execEach n ⟨prof, m⟩ env x idx byRef body vw i) s (fun fl s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ LoopFlow m W tenv penv s' fl ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store))

/-- Every evaluation function at fuel `n` meets its statement. -/
structure Specs (n : Nat) : Prop where
  expr : ExprSpec m prof plans n
  blockValue : BlockValueSpec m prof plans n
  arg : ArgSpec m prof plans n
  bound : BoundSpec m prof plans n
  place : PlaceSpec m prof plans n
  view : ViewSpec m prof plans n
  call : CallSpec m prof plans n
  block : BlockSpec m prof plans n
  stmts : StmtsSpec m prof plans n
  stmt : StmtSpec m prof plans n
  printArg : PrintArgSpec m prof plans n
  while_ : WhileSpec m prof plans n
  range : RangeSpec m prof plans n
  each : EachSpec m prof plans n

end Specs

/-! ### What acceptance gives, per item of the module -/

/-- The typing environment an implementation's body is checked in. -/
def implEnv (m : Module) (impl : Impl) : TEnv :=
  { mod := m, impl := some impl, vars := impl.vars, visible := List.range impl.params.size
    loops := 0, inExpr := false, scopes := [], globalLimit := m.globals.size, initializing := none }

/-- The typing environment a global's initializer is checked in. -/
def initEnv (m : Module) (g : GlobalId) : TEnv :=
  { mod := m, impl := none, vars := #[], visible := [], loops := 0, inExpr := true, scopes := []
    globalLimit := g, initializing := some g }

structure ImplOk (m : Module) (impl : Impl) : Prop where
  params : ∀ (i : Nat) (p : Param), impl.params[i]? = some p → p.var = i ∧
    ∃ lv : LocalVar, impl.vars[i]? = some lv ∧ lv.scope = 0 ∧ lv.ty.paramOk = true
  bodyScope : impl.body.scope = 0
  body : ∃ bodyTy tn, tyBlock (implEnv m impl) [] impl.body impl.params.size = .ok (bodyTy, tn) ∧
    ((impl.results.toList = [] ∧ bodyTy = .unit) ∨
      ∃ t, impl.results.toList = [t] ∧ (impl.body.value.isSome = true → bodyTy = t) ∧
        (impl.body.value.isSome = false → impl.body.diverges m.noReturn = true))

/-- Accepted contexts retain the exact annotation check needed to classify call roots. -/
structure CtxOk (m : Module) (impl : Impl) (ctx : Context) : Prop where
  annotationShape : checkAnnotationShape m impl ctx = .ok ()
  paramAnn : ∀ (i : Nat) (ann : List RootRef), i < impl.params.size →
    (ctx.varRoots.find? (·.1 == i)).map (·.2) = some ann →
    ∀ q, q ∈ ann → q = .param i ∨ ∃ g, q = .global g
  resultLen : ctx.resultRoots.length = impl.results.size
  content : ∀ (x : Nat) (cont : List RootRef),
    (ctx.contentRoots.find? (·.1 == x)).map (·.2) = some cont →
    x < impl.params.size ∧ (ctx.varRoots.find? (·.1 == x)).map (·.2) = some [.param x] ∧
      ∀ y, RootRef.local y ∉ cont
  body : ∃ rho rng st, rpBlockValue ⟨m, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
      .ok ((rho, rng), st) ∧
    (impl.body.value.isSome = true → checkResultV ⟨m, impl, ctx, []⟩ rho = .ok ()) ∧
    checkSummary m impl ctx st.eff = .ok ()

structure GlobOk (m : Module) (g : GlobalId) (gl : Global) : Prop where
  ty : gl.ty.storable = true ∧ gl.ty.isRefLike = false
  init : ∃ tn, tyExpr (initEnv m g) gl.init 0 = .ok (gl.ty, tn)
  roots : ∃ rho st, rpExpr ⟨m, initImpl, initContext, []⟩ gl.init ⟨0, {}⟩ = .ok (rho, st) ∧
    st.eff.unknown = false ∧
    ∀ t : Target,
      (t ∈ st.eff.reads ∨ t ∈ st.eff.writes ∨ t ∈ st.eff.grows ∨ t ∈ st.eff.shrinks) →
      ∀ h, t = .global h → h < g

/-- The facts the proof uses about an accepted module. -/
structure ModOk (m : Module) : Prop where
  structTables : checkStructTables m = .ok ()
  impl : ∀ (i : Nat) (impl : Impl), m.impls[i]? = some impl → ImplOk m impl
  ctx : ∀ (c : Nat) (ctx : Context), m.contexts[c]? = some ctx → ∃ impl, m.impls[ctx.impl]? = some impl ∧ CtxOk m impl ctx
  glob : ∀ (g : Nat) (gl : Global), m.globals[g]? = some gl → GlobOk m g gl
  entry : ∃ ctx impl, m.contexts[m.entry]? = some ctx ∧ m.impls[ctx.impl]? = some impl ∧
    impl.params.size = 0 ∧ impl.results.toList = []
  demand : checkModuleDemand m = .ok ()
  demandPlans : ∃ plans, deriveModuleDemand m = .ok plans ∧ PlansWellFormed m plans

end Goose.Core.Sound
