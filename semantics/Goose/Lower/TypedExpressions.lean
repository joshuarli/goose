import Goose.Lower.RuntimeSim
import Goose.Lower.Leaf
import Goose.Lower.Coerce
import Goose.Core.Sound.All

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Memory
open Goose.Core.Sound (World EvaluationContext Observation Frame ShrinkProtected ObservedSafe
  ClassifiedParameters Perm EffLe HasTy RetainsAliases Footprint Dset PreservesRootTypes
  PreservesValues PilotStoreLe Gam OwnerRooted PreservesForbiddenOwnerRoots MutationFootprint
  effectMutationRoots PlaceOk Targets)

structure ExprSource (cfg : Cfg) (env : Env) (expr : Expr) (state : St) where
  accepted : Core.validate cfg.mod = .ok ()
  plans : Array (Array DemandPoint)
  path : List Nat
  context : EvaluationContext cfg.mod plans path (.expression expr) .expression
  observation : Observation
  world : World
  typingEnv : TEnv
  rootsEnv : PEnv
  typingStart : Nat
  typingEnd : Nat
  ty : Ty
  rootsStart : RState
  rootsEnd : RState
  roots : List RootRef
  active : context.ActiveMatches typingEnv
  access : context.AccessMatches typingEnv rootsEnv
  protection : ShrinkProtected world.D world.A (context.mayShrink world.ownerP observation)
  observed : ObservedSafe cfg.mod world (context.mayShrink world.ownerP observation) observation state.store
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod world.P world.D observation state.store
  permission : Perm cfg.mod world
  frame : Core.Sound.Frame cfg.mod world typingEnv rootsEnv env state context.inputFuture
  typed : tyExpr typingEnv expr typingStart = .ok (ty, typingEnd)
  rooted : rpExpr rootsEnv expr rootsStart = .ok (roots, rootsEnd)
  effects : EffLe rootsEnd.eff world.E

structure ExprResult {cfg : Cfg} {env : Env} {expr : Expr} {state : St}
    (source : ExprSource cfg env expr state) (value : Val) (after : St) : Prop where
  frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
    source.context.outputFuture
  footprint : Footprint (Core.Sound.insts env) (Dset source.world) state after
  rootTypes : PreservesRootTypes cfg.mod source.world.G source.observation.roots state.store after.store
  values : PreservesValues cfg.mod source.world.G source.observation.values state.store after.store
  observed : ObservedSafe cfg.mod source.world
    (source.context.mayShrink source.world.ownerP source.observation) source.observation after.store
  aliases : RetainsAliases cfg.mod source.world env state.store after.store source.context.retained
  pilotStore : PilotStoreLe cfg.mod state after
  typed : HasTy cfg.mod source.world.G after.store value source.ty
  rooted : ∀ root, Targets value root → Gam env source.world.P source.roots root
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store
  ownerRooted : OwnerRooted env source.world.ownerP source.roots value source.ty
  forbidden : PreservesForbiddenOwnerRoots (m := cfg.mod) (G := source.world.G)
    (env := env) (P := source.world.P) source.context.forbiddenOwners state after
  mutations : MutationFootprint env source.world.P source.world.base
    (effectMutationRoots cfg.mod source.rootsEnv.impl source.rootsEnd.eff) state after

theorem ExprSource.result {cfg : Cfg} {env : Env} {expr : Expr} {state after : St}
    (source : ExprSource cfg env expr state) (n : Nat) (value : Val)
    (h : evalExpr n cfg env expr state = .ok value after) : ExprResult source value after := by
  have hs := (Core.Sound.specs_all (Core.Sound.validate_modOk cfg.mod source.accepted)
    cfg.profile source.plans n).expr source.path expr source.context source.observation
    source.world source.typingEnv source.rootsEnv env state source.typingStart source.typingEnd
    source.ty source.rootsStart source.rootsEnd source.roots source.active source.access
    source.protection source.observed source.classified source.permission source.frame source.typed
    source.rooted source.effects
  unfold Core.Sound.Sat at hs
  rw [h] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hs
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem ExprResult.value_passable {cfg : Cfg} {env : Env} {expr : Expr} {state after : St}
    {source : ExprSource cfg env expr state} {value : Val} (result : ExprResult source value after)
    {target : Ty} (h : source.ty.passableTo target = true) :
    HasTy cfg.mod source.world.G after.store value target :=
  Core.Sound.hasTy_passable result.typed h

theorem ExprResult.coercionValue {cfg : Cfg} {env : Env} {expr : Expr} {state after : St}
    {source : ExprSource cfg env expr state} {value : Val} (result : ExprResult source value after)
    {target : Ty} (h : source.ty.passableTo target = true) : CoercionValue target value :=
  CoercionValue.of_hasTy (result.value_passable h)

structure PlaceSource (cfg : Cfg) (env : Env) (place : Place) (state : St) where
  accepted : Core.validate cfg.mod = .ok ()
  plans : Array (Array DemandPoint)
  path : List Nat
  context : EvaluationContext cfg.mod plans path (.place place) .place
  observation : Observation
  world : World
  typingEnv : TEnv
  rootsEnv : PEnv
  typingStart : Nat
  typingEnd : Nat
  ty : Ty
  mutable : Bool
  contents : Bool
  rootsStart : RState
  rootsEnd : RState
  roots : List RootRef
  active : context.ActiveMatches typingEnv
  access : context.AccessMatches typingEnv rootsEnv
  protection : ShrinkProtected world.D world.A (context.mayShrink world.ownerP observation)
  observed : ObservedSafe cfg.mod world (context.mayShrink world.ownerP observation) observation state.store
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod world.P world.D observation state.store
  permission : Perm cfg.mod world
  frame : Core.Sound.Frame cfg.mod world typingEnv rootsEnv env state context.inputFuture
  typed : tyPlace typingEnv place typingStart = .ok (⟨ty, mutable, contents⟩, typingEnd)
  rooted : rpPlace rootsEnv place rootsStart = .ok (roots, rootsEnd)
  effects : EffLe rootsEnd.eff world.E

structure PlaceResult {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : PlaceSource cfg env place state) (location : Loc) (after : St) : Prop where
  frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
    source.context.outputFuture
  footprint : Footprint (Core.Sound.insts env) (Dset source.world) state after
  rootTypes : PreservesRootTypes cfg.mod source.world.G source.observation.roots state.store after.store
  values : PreservesValues cfg.mod source.world.G source.observation.values state.store after.store
  observed : ObservedSafe cfg.mod source.world
    (source.context.mayShrink source.world.ownerP source.observation) source.observation after.store
  aliases : RetainsAliases cfg.mod source.world env state.store after.store source.context.retained
  pilotStore : PilotStoreLe cfg.mod state after
  typed : PlaceOk cfg.mod source.world.G source.world.P source.rootsEnv env after.store place location source.ty
  rooted : Gam env source.world.P source.roots location.root
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store
  ownerRooted : (∃ element, source.ty = .grow element ∨ source.ty = .growshrink element) →
    Gam env source.world.ownerP source.roots location.root
  forbidden : PreservesForbiddenOwnerRoots (m := cfg.mod) (G := source.world.G)
    (env := env) (P := source.world.P) source.context.forbiddenOwners state after
  mutations : MutationFootprint env source.world.P source.world.base
    (effectMutationRoots cfg.mod source.rootsEnv.impl source.rootsEnd.eff) state after

theorem PlaceSource.result {cfg : Cfg} {env : Env} {place : Place} {state after : St}
    (source : PlaceSource cfg env place state) (n : Nat) (location : Loc)
    (h : evalPlace n cfg env place state = .ok location after) : PlaceResult source location after := by
  have hs := (Core.Sound.specs_all (Core.Sound.validate_modOk cfg.mod source.accepted)
    cfg.profile source.plans n).place source.path place source.context source.observation
    source.world source.typingEnv source.rootsEnv env state source.typingStart source.typingEnd
    source.ty source.mutable source.contents source.rootsStart source.rootsEnd source.roots
    source.active source.access source.protection source.observed source.classified source.permission
    source.frame source.typed source.rooted source.effects
  unfold Core.Sound.Sat at hs
  rw [h] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hs
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

def SourceResults (typingEnv : TEnv) (rootsEnv : PEnv) (results : List Ty) : Prop :=
  ∀ impl, typingEnv.impl = some impl → rootsEnv.impl = impl ∧ results = impl.results.toList

def TypedExprClaim (n : Nat) (cfg : Cfg) (results : List Ty) (expr : Expr) : Prop :=
  ∀ (env : Env) (state : St) (source : ExprSource cfg env expr state),
    SourceResults source.typingEnv source.rootsEnv results → ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerExpr expr (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results →
    SimEAt cx pt fr (evalExpr n cfg env expr)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state

def TypedPlaceClaim (n : Nat) (cfg : Cfg) (results : List Ty) (place : Place) : Prop :=
  ∀ (env : Env) (state : St) (source : PlaceSource cfg env place state),
    SourceResults source.typingEnv source.rootsEnv results → ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerPlace place (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results →
    SimEAt cx pt fr (evalPlace n cfg env place)
      (fun location pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val (.ref location))]) state

theorem ExprSource.notChild {cfg : Cfg} {env : Env} {expr : Expr} {state : St}
    (source : ExprSource cfg env (.not expr) state) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = .bool := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨ty, finish, ht, rfl, hresult, _⟩ := ht
  obtain ⟨roots, rootsFinish, hr, _, hrootsEnd⟩ := hr
  let ec := source.context
  let child := ec.child rfl 0 (.expression expr) .expression rfl (by trivial)
  have hshrink : child.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.expression expr) .expression rfl
      (by trivial) source.world.ownerP source.observation root)
  have hfuture : child.outputFuture = ec.outputFuture := by
    dsimp only [child]
    cases ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 0 (.expression expr) .expression rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hinputFormula : child.inputFuture = expr.variables ++ child.outputFuture := by
    dsimp only [child]
    cases ec <;> rfl
  have hinput : child.inputFuture = ec.inputFuture := by
    rw [hinputFormula, hfuture]
    cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
      Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
      DemandNode.variables, DemandNode.visibleAfter, Expr.variables]
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
    context := child, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
    typingEnd := finish, ty := .bool, rootsStart := source.rootsStart, rootsEnd := rootsFinish,
    roots := roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, rfl⟩
  · exact ec.child_activeMatches rfl 0 (.expression expr) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.expression expr) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · simpa [hrootsEnd] using source.effects

theorem ExprSource.readChild {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : ExprSource cfg env (.read place) state) :
    ∃ child : PlaceSource cfg env place state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨ty, mutable, contents, finish, ht, hread, _, _⟩ := ht
  obtain ⟨roots, rootsFinish, hr, next, hadd, hreadRoots⟩ := hr
  obtain ⟨hnext, _⟩ := Core.Sound.readRoots_ok _ _ _ _ hreadRoots
  simp only at hnext
  subst hnext
  let ec := source.context
  let child := ec.child rfl 0 (.place place) .place rfl (by trivial)
  have hshrink : child.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.place place) .place rfl
      (by trivial) source.world.ownerP source.observation root)
  have hfuture : child.outputFuture = ec.outputFuture := by
    dsimp only [child]
    cases ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 0 (.place place) .place rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hinputFormula : child.inputFuture = place.variables ++ child.outputFuture := by
    dsimp only [child]
    cases ec <;> rfl
  have hinput : child.inputFuture = ec.inputFuture := by
    rw [hinputFormula, hfuture]
    cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
      Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
      DemandNode.variables, DemandNode.visibleAfter, Expr.variables]
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
    context := child, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
    typingEnd := finish, ty := ty, mutable := mutable, contents := contents, rootsStart := source.rootsStart, rootsEnd := rootsFinish,
    roots := roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl⟩
  · exact ec.child_activeMatches rfl 0 (.place place) .place rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.place place) .place rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact (Core.Sound.PMono.addReads _ _ _ _ hadd).2.trans source.effects

theorem typedExprClaim_zero (cfg : Cfg) (results : List Ty) (expr : Expr) :
    TypedExprClaim 0 cfg results expr := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  simp only [evalExpr]
  exact SimEAt.of_timeout state

theorem typedPlaceClaim_zero (cfg : Cfg) (results : List Ty) (place : Place) :
    TypedPlaceClaim 0 cfg results place := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  simp only [evalPlace]
  exact SimEAt.of_timeout state

theorem typedExprClaim_lit (n : Nat) (cfg : Cfg) (results : List Ty) (ty : IntTy) (value : Int) :
    TypedExprClaim n cfg results (.lit ty value) := by
  cases n with
  | zero => exact typedExprClaim_zero _ _ _
  | succ n =>
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
    simp only [lowerExpr] at hlow
    simp only [evalExpr]
    exact SimEAt.of_simG (leaf_def (Post.init hrel hpp) hlow hext (by simp) RVal.val
      (by simp [execPure])) state

theorem typedExprClaim_bool (n : Nat) (cfg : Cfg) (results : List Ty) (value : Bool) :
    TypedExprClaim n cfg results (.bool value) := by
  cases n with
  | zero => exact typedExprClaim_zero _ _ _
  | succ n =>
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
    simp only [lowerExpr] at hlow
    simp only [evalExpr]
    exact SimEAt.of_simG (leaf_def (Post.init hrel hpp) hlow hext (by simp) RVal.val
      (by simp [execPure])) state

theorem typedExprClaim_not {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedExprClaim (n + 1) cfg results (.not expr) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  obtain ⟨child, htyping, hroots, hbool⟩ := source.notChild
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, middle, hchild, hdef⟩ := hlow
  have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimEAt.bind (he env state child hchildMetadata ls middle x pt cx fr hchild hpp
    hextMiddle hrel hgir hresults) fun value after pt1 fr1 hdone P => ?_
  have hvalue := (child.result n value hdone).typed
  rw [hbool] at hvalue
  obtain ⟨boolean, rfl⟩ := Core.Sound.hasTy_bool hvalue
  simp only [Goose.Core.expectBool, pure_bind]
  have hx := P.has (x, .val (.bool boolean)) (by simp)
  apply SimEAt.of_simG
  exact leaf_def P hdef hext (by simp) RVal.val
    (by simp only [execPure, getVal_of hx, Goose.Core.expectBool, pure_bind])

theorem typedExprClaim_read {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) : TypedExprClaim (n + 1) cfg results (.read place) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  obtain ⟨child, htyping, hroots⟩ := source.readChild
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨id, middle, hchild, hdef⟩ := hlow
  have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimEAt.bind (hp env state child hchildMetadata ls middle id pt cx fr hchild hpp
    hextMiddle hrel hgir hresults) fun location after pt1 fr1 hdone P => ?_
  have hx := P.has (id, .val (.ref location)) (by simp)
  apply SimEAt.of_simG
  exact leaf_def P hdef hext (by simp) RVal.val
    (by simp only [execPure, getVal_of hx, Goose.Core.expectRef, pure_bind])

theorem typedPlaceClaim_var (n : Nat) (cfg : Cfg) (results : List Ty) (id : VarId) :
    TypedPlaceClaim n cfg results (.var id) := by
  cases n with
  | zero => exact typedPlaceClaim_zero _ _ _
  | succ n =>
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
    simp only [lowerPlace] at hlow
    simp only [evalPlace]
    exact SimEAt.of_simG (leaf_def (Post.init hrel hpp) hlow hext (by simp)
      (fun location => RVal.val (.ref location))
      (by simp only [execPure, slotRoot_eq hrel id, bind_assoc, pure_bind])) state

theorem typedPlaceClaim_global (n : Nat) (cfg : Cfg) (results : List Ty) (id : GlobalId) :
    TypedPlaceClaim n cfg results (.global id) := by
  cases n with
  | zero => exact typedPlaceClaim_zero _ _ _
  | succ n =>
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
    simp only [lowerPlace] at hlow
    simp only [evalPlace]
    exact SimEAt.of_simG (leaf_def (Post.init hrel hpp) hlow hext (by simp)
      (fun location => RVal.val (.ref location)) (by simp [execPure])) state

inductive ArgSource (cfg : Cfg) (env : Env) (state : St) : Arg → Type
  | byVal {expr : Expr} (source : ExprSource cfg env expr state) :
      ArgSource cfg env state (.byVal expr)
  | byRef {place : Place} (mutability : Mutability) (source : PlaceSource cfg env place state)
      (target : source.ty.refTarget = true ∨
        (source.ty.isSlice = true ∧ source.mutable = true ∧ place.sliceArg = true)) :
      ArgSource cfg env state (.byRef mutability place)

def ArgSource.resultsMatch {cfg : Cfg} {env : Env} {state : St} {arg : Arg}
    (source : ArgSource cfg env state arg) (results : List Ty) : Prop :=
  match source with
  | .byVal source => SourceResults source.typingEnv source.rootsEnv results
  | .byRef _ source _ => SourceResults source.typingEnv source.rootsEnv results

def TypedArgClaim (n : Nat) (cfg : Cfg) (results : List Ty) (arg : Arg) : Prop :=
  ∀ (env : Env) (state : St) (source : ArgSource cfg env state arg), source.resultsMatch results →
    ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerArg arg (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results →
    SimEAt cx pt fr (evalArg n cfg env arg)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state

theorem typedArgClaim_zero (cfg : Cfg) (results : List Ty) (arg : Arg) :
    TypedArgClaim 0 cfg results arg := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  simp only [evalArg]
  exact SimEAt.of_timeout state

theorem typedArgClaim_byVal {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedArgClaim (n + 1) cfg results (.byVal expr) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  cases source with
  | byVal source =>
    simp only [lowerArg] at hlow
    simp only [evalArg]
    exact he env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults

theorem typedArgClaim_byRef {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) (mutability : Mutability) :
    TypedArgClaim (n + 1) cfg results (.byRef mutability place) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  cases source with
  | byRef _ source target =>
    simp only [lowerArg, bind_eq] at hlow
    obtain ⟨id, middle, hplace, hfreeze⟩ := hlow
    rcases freezeTo_cases hfreeze with ⟨rfl, rfl⟩ | hfreeze
    · simp only [evalArg]
      refine SimEAt.bind (hp env state source hmetadata ls ls' r pt cx fr hplace hpp hext hrel hgir hresults)
        fun location after pt' fr' hdone P => ?_
      exact SimEAt.ret P
    · have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hfreeze)
      simp only [evalArg]
      refine SimEAt.bind (hp env state source hmetadata ls middle id pt cx fr hplace hpp hextMiddle hrel hgir hresults)
        fun location after pt' fr' hdone P => ?_
      have hcell : fr'.vals[id]? = some (.val (.ref location)) := P.has (id, _) (by simp)
      apply SimEAt.of_simG
      exact leaf_def P hfreeze hext (by simp) RVal.val
        (by simp only [execPure, getVal_of hcell, Goose.Core.expectRef, pure_bind])

inductive ArgsSource (n : Nat) (cfg : Cfg) (env : Env) : List Arg → St → Type
  | nil (state : St) : ArgsSource n cfg env [] state
  | cons {arg : Arg} {args : List Arg} {state : St} (source : ArgSource cfg env state arg)
      (rest : ∀ value after, evalArg n cfg env arg state = .ok value after →
        ArgsSource n cfg env args after) : ArgsSource n cfg env (arg :: args) state

def ArgsSource.resultsMatch {n : Nat} {cfg : Cfg} {env : Env} :
    {args : List Arg} → {state : St} → ArgsSource n cfg env args state → List Ty → Prop
  | [], _, .nil _, _ => True
  | _ :: _, _, .cons source rest, results => source.resultsMatch results ∧
      ∀ value after hdone, (rest value after hdone).resultsMatch results

def TypedArgsClaim (n : Nat) (cfg : Cfg) (results : List Ty) (args : List Arg) : Prop :=
  ∀ (env : Env) (state : St) (source : ArgsSource n cfg env args state), source.resultsMatch results →
    ∀ (ls ls' : LS) (ids : List ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerArgs args (lowerEnv cfg.mod env.vars results) ls = (ids, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results →
    SimEAt cx pt fr (mapList (evalArg n cfg env) args)
      (fun values pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr ls' fr' pt' (cellsOf ids values)) state

theorem typedArgsClaim {n : Nat} {cfg : Cfg} {results : List Ty} : ∀ (args : List Arg),
    (∀ arg ∈ args, TypedArgClaim n cfg results arg) → TypedArgsClaim n cfg results args
  | [], _ => by
    intro env state source hmetadata ls ls' ids pt cx fr hlow hpp hext hrel hgir hresults
    simp only [lowerArgs, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    exact SimEAt.ret ⟨rfl, by simpa [cellsOf] using Post.init hrel hpp⟩
  | arg :: args, ha => by
    intro env state source hmetadata ls ls' ids pt cx fr hlow hpp hext hrel hgir hresults
    cases source with
    | cons source rest =>
      simp only [lowerArgs, bind_eq] at hlow
      obtain ⟨id, middle, harg, restIds, after, hargs, hret⟩ := hlow
      rw [pure_run] at hret
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hret
      have hextMiddle : ExtT middle cx.fn.blocks :=
        hext.of_adv (advB_lowerArgs args _ _ _ _ hargs)
      simp only [mapList]
      refine SimEAt.bind (ha arg (by simp) env state source hmetadata.1 ls middle id pt cx fr
        harg hpp hextMiddle hrel hgir hresults) fun value state1 pt1 fr1 hdone P => ?_
      refine SimEAt.bind (typedArgsClaim args (fun arg harg => ha arg (by simp [harg]))
        env state1 (rest value state1 hdone) (hmetadata.2 value state1 hdone) middle after restIds pt1 cx fr1 hargs P.pp hext P.rel hgir hresults)
        fun values state2 pt2 fr2 hdoneRest ⟨hlen, Q⟩ => ?_
      exact SimEAt.ret ⟨by simp [hlen], by simpa [cellsOf] using P.comp Q⟩

theorem SimEAt.call_step {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {r : ValueId} {f : FnId}
    {args : List ValueId} {values : List Val} {org : Option OriginId} {c : M Val} {state : St}
    (hi : instAt cx.fn pt = some (.def r (.call f args org)))
    (ha : mapList (getVal fr) args = pure values)
    (hc : EventualM c (fun fuel => callFn fuel cx.cfg fr.depth f values) state) :
    SimEAt cx pt fr c
      (fun value pt' fr' => pt' = (pt.1, pt.2 + 1) ∧ fr' = fr.set r (.val value)) state := by
  refine SimEAt.def_step RVal.val hi ?_
  have hm := EventualM.bind (c2 := fun value => pure (RVal.val value))
    (g2 := fun value _ => pure (RVal.val value)) hc
    (fun value after _ => EventualM.refl (pure (RVal.val value) : M RVal) after)
  refine EventualM.shift 1 hm fun fuel => ?_
  simp only [execOp, ha, pure_bind]

theorem typed_call_sim {n : Nat} {cfg : Cfg} {results : List Ty} {c : ContextId}
    {args : List Arg} {org : OriginId} (ha : TypedArgsClaim n cfg results args)
    (env : Env) (state : St) (source : ArgsSource n cfg env args state)
    (hmetadata : source.resultsMatch results)
    (hc : ∀ values after, mapList (evalArg n cfg env) args state = .ok values after →
      EventualM (enterCall n cfg env.depth c values)
        (fun fuel => callFn fuel ⟨cfg.profile, lower cfg.mod⟩ env.depth
          (((cfg.mod.contexts[c]?).map (·.impl)).getD 0) values) after)
    (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerExpr (.call c args org) (lowerEnv cfg.mod env.vars results) ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (evalExpr (n + 1) cfg env (.call c args org))
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state := by
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨ids, middle, after, hargs, hdef, htail⟩ := lowerExpr_call_split hlow
  have hextAfter : ExtT after cx.fn.blocks := by
    rcases htail with ⟨_, hterm⟩ | ⟨_, rfl⟩
    · exact hext.of_adv (adv_emitTerm hterm)
    · exact hext
  have hextMiddle : ExtT middle cx.fn.blocks := hextAfter.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimEAt.bind (ha env state source hmetadata ls middle ids pt cx fr
    hargs hpp hextMiddle hrel hgir hresults) fun values afterArgs pt1 fr1 hdone ⟨hlen, P⟩ => ?_
  have hread := mapList_getVal_cells hlen P.has
  have hi := (Post.def_leaf P hdef hextAfter (.val .unit)).2
  have hcfg : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩ := by
    cases hgc : cx.cfg
    simp only [hgc] at hgir
    have hp := P.rel.prof
    simp only [hgc] at hp
    cases hgir
    cases hp
    rfl
  have hcall : EventualM (enterCall n cfg env.depth c values)
      (fun fuel => callFn fuel cx.cfg fr1.depth
        (((le.mod.contexts[c]?).map (·.impl)).getD 0) values) afterArgs := by
    rw [hcfg, P.rel.depth]
    exact hc values afterArgs hdone
  have hs := SimEAt.call_step hi hread hcall
  rcases htail with ⟨hnr, _⟩ | ⟨_, rfl⟩
  · have hn := Core.Sound.noReturn_sound cfg.mod cfg.profile c hnr n env.depth values
    exact SimEAt.of_stops (hn afterArgs) (fun _ _ h => h) hs
  · exact hs.mono fun value afterValue pt' fr' hdoneValue ⟨hpt, hfr⟩ => by
      subst hpt; subst hfr
      exact (Post.def_leaf P hdef hext (.val value)).1

end Goose.Lower
