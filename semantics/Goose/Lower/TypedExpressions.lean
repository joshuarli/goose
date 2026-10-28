import Goose.Lower.GeneratedBuilder
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

structure ExprSource.ChildAt {cfg : Cfg} {env : Env} {expression childExpression : Expr}
    {state childState : St} (source : ExprSource cfg env expression state)
    (child : ExprSource cfg env childExpression childState) (index : Nat)
    (found : DemandNode.child? (.expression expression) index = some (.expression childExpression)) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [index]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl index (.expression childExpression) .expression found (by trivial))
  typing : child.typingEnv = source.typingEnv
  roots : child.rootsEnv = source.rootsEnv
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained

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

structure ViewSource (cfg : Cfg) (env : Env) (view : View) (state : St) where
  accepted : Core.validate cfg.mod = .ok ()
  plans : Array (Array DemandPoint)
  path : List Nat
  context : EvaluationContext cfg.mod plans path (.view view) .view
  observation : Observation
  world : World
  typingEnv : TEnv
  rootsEnv : PEnv
  typingStart : Nat
  typingEnd : Nat
  element : Ty
  mutable : Bool
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
  typed : tyView typingEnv view typingStart = .ok ((element, mutable), typingEnd)
  rooted : rpView rootsEnv view rootsStart = .ok (roots, rootsEnd)
  effects : EffLe rootsEnd.eff world.E

structure ExprSource.ReadChildAt {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : ExprSource cfg env (.read place) state) (child : PlaceSource cfg env place state) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [0]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl 0 (.place place) .place rfl (by trivial))
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained
  inputFuture : child.context.inputFuture = source.context.inputFuture
  outputFuture : child.context.outputFuture = source.context.outputFuture

structure ViewSource.PlaceChildAt {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : ViewSource cfg env (.of place) state) (child : PlaceSource cfg env place state) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [0]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl 0 (.place place) .place rfl (by trivial))
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained
  inputFuture : child.context.inputFuture = source.context.inputFuture
  outputFuture : child.context.outputFuture = source.context.outputFuture

structure ViewSource.ExpressionChildAt {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    (source : ViewSource cfg env (.val expression) state) (child : ExprSource cfg env expression state) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [0]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl 0 (.expression expression) .expression rfl (by trivial))
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained
  inputFuture : child.context.inputFuture = source.context.inputFuture
  outputFuture : child.context.outputFuture = source.context.outputFuture

structure ExprSource.ViewChildAt {cfg : Cfg} {env : Env} {expression : Expr} {view : View}
    {state childState : St} (source : ExprSource cfg env expression state)
    (child : ViewSource cfg env view childState) (index : Nat)
    (found : DemandNode.child? (.expression expression) index = some (.view view)) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [index]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl index (.view view) .view found (by trivial))
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained

structure PlaceSource.ViewChildAt {cfg : Cfg} {env : Env} {place : Place} {view : View}
    {state childState : St} (source : PlaceSource cfg env place state)
    (child : ViewSource cfg env view childState) (index : Nat)
    (found : DemandNode.child? (.place place) index = some (.view view)) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [index]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl index (.view view) .view found (by trivial))
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained

structure PlaceSource.ExpressionChildAt {cfg : Cfg} {env : Env} {place : Place} {expression : Expr}
    {state childState : St} (source : PlaceSource cfg env place state)
    (child : ExprSource cfg env expression childState) (index : Nat)
    (found : DemandNode.child? (.place place) index = some (.expression expression)) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [index]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl index (.expression expression) .expression found (by trivial))
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained

structure ViewResult {cfg : Cfg} {env : Env} {view : View} {state : St}
    (source : ViewSource cfg env view state) (value : ViewVal) (after : St) : Prop where
  frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
    source.context.outputFuture
  footprint : Footprint (Core.Sound.insts env) (Dset source.world) state after
  rootTypes : PreservesRootTypes cfg.mod source.world.G source.observation.roots state.store after.store
  values : PreservesValues cfg.mod source.world.G source.observation.values state.store after.store
  observed : ObservedSafe cfg.mod source.world
    (source.context.mayShrink source.world.ownerP source.observation) source.observation after.store
  aliases : RetainsAliases cfg.mod source.world env state.store after.store source.context.retained
  pilotStore : PilotStoreLe cfg.mod state after
  typed : Core.Sound.ViewOk after.store value source.element
  rooted : Gam env source.world.P source.roots value.loc.root
  viewAliases : Core.Sound.ViewAliases cfg.mod source.world source.rootsEnv env after.store view value source.element
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store
  forbidden : PreservesForbiddenOwnerRoots (m := cfg.mod) (G := source.world.G)
    (env := env) (P := source.world.P) source.context.forbiddenOwners state after
  mutations : MutationFootprint env source.world.P source.world.base
    (effectMutationRoots cfg.mod source.rootsEnv.impl source.rootsEnd.eff) state after

theorem ViewSource.result {cfg : Cfg} {env : Env} {view : View} {state after : St}
    (source : ViewSource cfg env view state) (n : Nat) (value : ViewVal)
    (h : evalView n cfg env view state = .ok value after) : ViewResult source value after := by
  have hs := (Core.Sound.specs_all (Core.Sound.validate_modOk cfg.mod source.accepted)
    cfg.profile source.plans n).view source.path view source.context source.observation
    source.world source.typingEnv source.rootsEnv env state source.typingStart source.typingEnd
    source.element source.mutable source.rootsStart source.rootsEnd source.roots
    source.active source.access source.protection source.observed source.classified source.permission
    source.frame source.typed source.rooted source.effects
  unfold Core.Sound.Sat at hs
  rw [h] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hs
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

structure BoundSource (cfg : Cfg) (env : Env) (bound : Bound) (state : St) where
  accepted : Core.validate cfg.mod = .ok ()
  plans : Array (Array DemandPoint)
  path : List Nat
  context : EvaluationContext cfg.mod plans path (.bound bound) .bound
  observation : Observation
  world : World
  typingEnv : TEnv
  rootsEnv : PEnv
  typingStart : Nat
  typingEnd : Nat
  rootsStart : RState
  rootsEnd : RState
  active : context.ActiveMatches typingEnv
  access : context.AccessMatches typingEnv rootsEnv
  protection : ShrinkProtected world.D world.A (context.mayShrink world.ownerP observation)
  observed : ObservedSafe cfg.mod world (context.mayShrink world.ownerP observation) observation state.store
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod world.P world.D observation state.store
  permission : Perm cfg.mod world
  frame : Core.Sound.Frame cfg.mod world typingEnv rootsEnv env state context.inputFuture
  typed : tyBound typingEnv bound typingStart = .ok ((), typingEnd)
  rooted : rpBound rootsEnv bound rootsStart = .ok ((), rootsEnd)
  effects : EffLe rootsEnd.eff world.E

structure BoundResult {cfg : Cfg} {env : Env} {bound : Bound} {state : St}
    (source : BoundSource cfg env bound state) (after : St) : Prop where
  frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
    source.context.outputFuture
  footprint : Footprint (Core.Sound.insts env) (Dset source.world) state after
  rootTypes : PreservesRootTypes cfg.mod source.world.G source.observation.roots state.store after.store
  values : PreservesValues cfg.mod source.world.G source.observation.values state.store after.store
  observed : ObservedSafe cfg.mod source.world
    (source.context.mayShrink source.world.ownerP source.observation) source.observation after.store
  aliases : RetainsAliases cfg.mod source.world env state.store after.store source.context.retained
  pilotStore : PilotStoreLe cfg.mod state after
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store
  forbidden : PreservesForbiddenOwnerRoots (m := cfg.mod) (G := source.world.G)
    (env := env) (P := source.world.P) source.context.forbiddenOwners state after
  mutations : MutationFootprint env source.world.P source.world.base
    (effectMutationRoots cfg.mod source.rootsEnv.impl source.rootsEnd.eff) state after

theorem BoundSource.result {cfg : Cfg} {env : Env} {bound : Bound} {state after : St}
    (source : BoundSource cfg env bound state) (n length : Nat) (default value : Int)
    (h : evalBound n cfg env length default bound state = .ok value after) : BoundResult source after := by
  have hs := (Core.Sound.specs_all (Core.Sound.validate_modOk cfg.mod source.accepted)
    cfg.profile source.plans n).bound source.path bound source.context source.observation
    source.world source.typingEnv source.rootsEnv env state length default source.typingStart source.typingEnd
    source.rootsStart source.rootsEnd
    source.active source.access source.protection source.observed source.classified source.permission
    source.frame source.typed source.rooted source.effects
  unfold Core.Sound.Sat at hs
  rw [h] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

def SourceResults (typingEnv : TEnv) (rootsEnv : PEnv) (results : List Ty) : Prop :=
  ∀ impl, typingEnv.impl = some impl → rootsEnv.impl = impl ∧ results = impl.results.toList

def TypedExprClaim (n : Nat) (cfg : Cfg) (results : List Ty) (expr : Expr) : Prop :=
  ∀ (env : Env) (state : St) (source : ExprSource cfg env expr state),
    SourceResults source.typingEnv source.rootsEnv results → ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerExpr expr (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    SimEAt cx pt fr (evalExpr n cfg env expr)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state

def TypedPlaceClaim (n : Nat) (cfg : Cfg) (results : List Ty) (place : Place) : Prop :=
  ∀ (env : Env) (state : St) (source : PlaceSource cfg env place state),
    SourceResults source.typingEnv source.rootsEnv results → ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerPlace place (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    SimEAt cx pt fr (evalPlace n cfg env place)
      (fun location pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val (.ref location))]) state

def TypedViewClaim (n : Nat) (cfg : Cfg) (results : List Ty) (view : View) : Prop :=
  ∀ (env : Env) (state : St) (source : ViewSource cfg env view state),
    SourceResults source.typingEnv source.rootsEnv results → ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerView view (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    SimEAt cx pt fr (evalView n cfg env view)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .view value)]) state

def TypedBoundClaim (n : Nat) (cfg : Cfg) (results : List Ty) (bound : Bound) : Prop :=
  ∀ (env : Env) (state : St) (source : BoundSource cfg env bound state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls ls' : LS) (bnd : Bnd) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame) (length : Nat) (default : Int),
    lowerBound bound (lowerEnv cfg.mod env.vars results) ls = (bnd, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    SimEAt cx pt fr (evalBound n cfg env length default bound)
      (fun value pt' fr' => ∃ cells, BndSpec length default bnd value cells ∧
        Post cfg env cx ls fr ls' fr' pt' cells) state

theorem ExprSource.notChild {cfg : Cfg} {env : Env} {expr : Expr} {state : St}
    (source : ExprSource cfg env (.not expr) state) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = .bool ∧ source.ChildAt child 0 rfl := by
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
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, rfl, ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, ?_⟩⟩
  · exact ec.child_activeMatches rfl 0 (.expression expr) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.expression expr) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · simpa [hrootsEnd] using source.effects
  · intro alias member
    exact ec.child_retained_subset rfl 0 (.expression expr) .expression rfl (by trivial) member

theorem ExprSource.unChild {cfg : Cfg} {env : Env} {expr : Expr} {state : St} (op : UnOp) (origin : OriginId)
    (source : ExprSource cfg env (.un op expr origin) state) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ ∃ intTy, child.ty = .int intTy ∧ source.ChildAt child 0 rfl := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨_, inputTy, finish, ht, intTy, rfl, hresult⟩ := ht
  obtain ⟨roots, rootsFinish, hr, htail⟩ := hr
  have childEffects : EffLe rootsFinish.eff source.world.E := by
    refine EffLe.trans ?_ source.effects
    cases op <;> inv at htail
    · obtain ⟨next, habort, _, rfl⟩ := htail
      exact (Core.Sound.PMono.noteAborts _ _ _ habort).2
    · obtain ⟨_, rfl⟩ := htail
      exact EffLe.refl _
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
    typingEnd := finish, ty := .int intTy, rootsStart := source.rootsStart, rootsEnd := rootsFinish,
    roots := roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, intTy, rfl, ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, ?_⟩⟩
  · exact ec.child_activeMatches rfl 0 (.expression expr) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.expression expr) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact childEffects
  · intro alias member
    exact ec.child_retained_subset rfl 0 (.expression expr) .expression rfl (by trivial) member

structure BoundSource.ExpressionChildAt {cfg : Cfg} {env : Env} {bound : Bound} {expression : Expr} {state : St}
    (source : BoundSource cfg env bound state) (child : ExprSource cfg env expression state)
    (found : DemandNode.child? (.bound bound) 0 = some (.expression expression)) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [0]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl 0 (.expression expression) .expression found (by trivial))
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained
  inputFuture : child.context.inputFuture = source.context.inputFuture
  outputFuture : child.context.outputFuture = source.context.outputFuture

structure ExprSource.BoundChildAt {cfg : Cfg} {env : Env} {expression : Expr} {bound : Bound}
    {state childState : St} (source : ExprSource cfg env expression state)
    (child : BoundSource cfg env bound childState) (index : Nat)
    (found : DemandNode.child? (.expression expression) index = some (.bound bound)) : Prop where
  world : child.world = source.world
  path : child.path = source.path ++ [index]
  plans : child.plans = source.plans
  context : HEq child.context
    (source.context.child rfl index (.bound bound) .bound found (by trivial))
  retained : ∀ alias ∈ source.context.retained, alias ∈ child.context.retained

theorem BoundSource.expressionChild {cfg : Cfg} {env : Env} {expr : Expr} {state : St} (fromEnd : Bool)
    (source : BoundSource cfg env (if fromEnd then .fromEnd expr else .expr expr) state) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ ∃ intTy, child.ty = .int intTy ∧
      source.ExpressionChildAt child (by cases fromEnd <;> rfl) := by
  cases fromEnd
  all_goals (
    have ht := source.typed
    have hr := source.rooted
    simp only [Bool.false_eq_true, ite_false, ite_true, tyBound] at ht
    inv at ht
    simp only [Bool.false_eq_true, ite_false, ite_true, rpBound] at hr
    inv at hr
    obtain ⟨inputTy, finish, ht, intTy, rfl, hend⟩ := ht
    obtain ⟨roots, hr⟩ := hr
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
        DemandNode.variables, DemandNode.visibleAfter, Expr.variables, Bound.variables, Bool.false_eq_true, ite_false, ite_true]
    refine ⟨{
      accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
      context := child, observation := source.observation, world := source.world,
      typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
      typingEnd := finish, ty := .int intTy, rootsStart := source.rootsStart, rootsEnd := source.rootsEnd,
      roots := roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
      classified := source.classified, permission := source.permission, frame := ?_,
      typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, intTy, rfl,
      ⟨rfl, rfl, rfl, HEq.rfl, fun alias member => ec.child_retained_subset rfl 0
        (.expression expr) .expression rfl (by trivial) member, hinput, hfuture⟩⟩
    · exact ec.child_activeMatches rfl 0 (.expression expr) .expression rfl (by trivial)
        source.typingEnv source.typingEnv source.active (by intro x; rfl)
    · exact (ec.child_accessMatches_iff rfl 0 (.expression expr) .expression rfl
        (by trivial) source.typingEnv source.rootsEnv).mpr source.access
    · simpa [hshrink] using source.protection
    · simpa [hshrink] using source.observed
    · simpa [hinput] using source.frame
    · exact source.effects
  )

theorem ExprSource.lenChild {cfg : Cfg} {env : Env} {view : View} {state : St} (source : ExprSource cfg env (.len view) state) :
    ∃ child : ViewSource cfg env view state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ source.ViewChildAt child 0 rfl ∧
      child.context.outputFuture = source.context.outputFuture := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨element, mutable, finish, ht, htype, hend⟩ := ht
  obtain ⟨roots, rootsFinish, hr, hroots, hrootsEnd⟩ := hr
  have childEffects : EffLe rootsFinish.eff source.world.E := by
    rw [← hrootsEnd]
    exact source.effects
  let ec := source.context
  let child := ec.child rfl 0 (.view view) .view rfl (by trivial)
  have hshrink : child.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.view view) .view rfl
      (by trivial) source.world.ownerP source.observation root)
  have hfuture : child.outputFuture = ec.outputFuture := by
    dsimp only [child]
    cases ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 0 (.view view) .view rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hinputFormula : child.inputFuture = view.variables ++ child.outputFuture := by
    dsimp only [child]
    cases ec <;> rfl
  have hinput : child.inputFuture = ec.inputFuture := by
    rw [hinputFormula, hfuture]
    cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
      Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
      DemandNode.variables, DemandNode.visibleAfter, Expr.variables, View.variables]
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
    context := child, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
    typingEnd := finish, element := element, mutable := mutable, rootsStart := source.rootsStart, rootsEnd := rootsFinish,
    roots := roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl,
      ⟨rfl, rfl, rfl, HEq.rfl, fun alias member => ec.child_retained_subset rfl 0
        (.view view) .view rfl (by trivial) member⟩, hfuture⟩
  · exact ec.child_activeMatches rfl 0 (.view view) .view rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.view view) .view rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact childEffects

theorem ExprSource.fillChild {cfg : Cfg} {env : Env} {expr : Expr} {state : St} (target : Ty)
    (source : ExprSource cfg env (.fill target expr) state) :
    ∃ element count, target = .arr element count ∧ ∃ child : ExprSource cfg env expr state,
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧ child.ty = element ∧ source.ChildAt child 0 rfl := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  cases target <;> inv at ht
  rename_i element count
  obtain ⟨hcanon, hflat, inputTy, finish, ht, heq, htype, hend⟩ := ht
  have hinputTy : inputTy = element := by simpa using heq
  subst inputTy
  obtain ⟨roots, rootsFinish, hr, hroots, hrootsEnd⟩ := hr
  have childEffects : EffLe rootsFinish.eff source.world.E := by
    rw [← hrootsEnd]
    exact source.effects
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
  refine ⟨element, count, rfl, {
    accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
    context := child, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
    typingEnd := finish, ty := element, rootsStart := source.rootsStart, rootsEnd := rootsFinish,
    roots := roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, rfl, ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, ?_⟩⟩
  · exact ec.child_activeMatches rfl 0 (.expression expr) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.expression expr) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact childEffects
  · intro alias member
    exact ec.child_retained_subset rfl 0 (.expression expr) .expression rfl (by trivial) member

theorem ExprSource.convChild {cfg : Cfg} {env : Env} {expr : Expr} {state : St} (kind : ConvKind) (target : Ty) (origin : OriginId)
    (source : ExprSource cfg env (.conv kind target expr origin) state) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ ∃ intTy targetTy, child.ty = .int intTy ∧ target = .int targetTy ∧ source.ChildAt child 0 rfl := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨_, inputTy, finish, ht, intTy, rfl, hresult⟩ := ht
  obtain ⟨roots, rootsFinish, hr, htail⟩ := hr
  have childEffects : EffLe rootsFinish.eff source.world.E := by
    refine EffLe.trans ?_ source.effects
    cases kind <;> inv at htail
    all_goals first
      | (obtain ⟨next, habort, _, rfl⟩ := htail; exact (Core.Sound.PMono.noteAborts _ _ _ habort).2)
      | (obtain ⟨_, rfl⟩ := htail; exact EffLe.refl _)
  have targetIsInt : ∃ intTy, target = .int intTy := by
    cases target <;> inv at hresult
    exact ⟨_, rfl⟩
  obtain ⟨targetInt, rfl⟩ := targetIsInt
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
    typingEnd := finish, ty := .int intTy, rootsStart := source.rootsStart, rootsEnd := rootsFinish,
    roots := roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, intTy, targetInt, rfl, rfl, ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, ?_⟩⟩
  · exact ec.child_activeMatches rfl 0 (.expression expr) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.expression expr) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact childEffects
  · intro alias member
    exact ec.child_retained_subset rfl 0 (.expression expr) .expression rfl (by trivial) member

theorem PlaceSource.derefChild {cfg : Cfg} {env : Env} {expr : Expr} {state : St}
    (source : PlaceSource cfg env (.deref expr) state)
    (hnormal : sliceRefTy source.typingEnv expr = none) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧
      ∃ mutability target, child.ty = .ref mutability target := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyPlace, hnormal] at ht
  inv at ht
  simp only [rpPlace] at hr
  obtain ⟨ty, finish, ⟨inputTy, before, ht, hnr, rfl, rfl⟩, hinfo⟩ := ht
  cases ty <;> inv at hinfo
  rename_i mutability target
  obtain ⟨_, _, _, _⟩ := hinfo
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
      DemandNode.variables, DemandNode.visibleAfter, Place.variables]
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
    context := child, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
    typingEnd := finish, ty := .ref mutability target, rootsStart := source.rootsStart, rootsEnd := source.rootsEnd,
    roots := source.roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, mutability, target, rfl⟩
  · exact ec.child_activeMatches rfl 0 (.expression expr) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.expression expr) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact source.effects

theorem ExprSource.readChild {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : ExprSource cfg env (.read place) state) :
    ∃ child : PlaceSource cfg env place state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ source.ReadChildAt child := by
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
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl,
      ⟨rfl, rfl, rfl, HEq.rfl, fun alias member =>
        ec.child_retained_subset rfl 0 (.place place) .place rfl (by trivial) member,
        hinput, hfuture⟩⟩
  · exact ec.child_activeMatches rfl 0 (.place place) .place rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.place place) .place rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact (Core.Sound.PMono.addReads _ _ _ _ hadd).2.trans source.effects

theorem ExprSource.popChild {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (origin : OriginId) (source : ExprSource cfg env (.pop place origin) state) :
    ∃ child : PlaceSource cfg env place state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨pre, hprofile, horg, ty, mutable, contents, finish, ht, element, final,
    helement, hwrite, htype, hend⟩ := ht
  obtain ⟨roots, rootsFinish, hr, readFinish, hadd, shrinkFinish, hshrink,
    abortFinish, habort, hroots, hrootsEnd⟩ := hr
  have childEffects : EffLe rootsFinish.eff source.world.E :=
    (Core.Sound.PMono.addReads _ _ _ _ hadd).2.trans
      ((Core.Sound.PMono.addShrinks _ _ _ _ hshrink).2.trans
        ((Core.Sound.PMono.noteAborts _ _ _ habort).2.trans
          (by simpa only [hrootsEnd] using source.effects)))
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
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := pre,
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
  · exact childEffects

theorem PlaceSource.fieldChild {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (index : Nat) (source : PlaceSource cfg env (.field place index) state) :
    ∃ child : PlaceSource cfg env place state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.path = source.path ++ [0] ∧
      child.world = source.world := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyPlace] at ht
  inv at ht
  simp only [rpPlace] at hr
  obtain ⟨ty, mutable, contents, finish, ht, field, final, hfield,
    hty, hmutable, hcontents, hend⟩ := ht
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
      DemandNode.variables, DemandNode.visibleAfter, Place.variables]
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
    context := child, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
    typingEnd := finish, ty := ty, mutable := mutable, contents := contents, rootsStart := source.rootsStart, rootsEnd := source.rootsEnd,
    roots := source.roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, rfl, rfl⟩
  · exact ec.child_activeMatches rfl 0 (.place place) .place rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.place place) .place rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact source.effects

theorem ViewSource.ofChild {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : ViewSource cfg env (.of place) state) :
    ∃ child : PlaceSource cfg env place state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ source.PlaceChildAt child := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyView] at ht
  inv at ht
  simp only [rpView] at hr
  inv at hr
  obtain ⟨ty, mutable, contents, finish, ht, htail⟩ := ht
  obtain ⟨roots, rootsFinish, hr, next, hadd, hroots, hrootsEnd⟩ := hr
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
      DemandNode.variables, DemandNode.visibleAfter, View.variables]
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
    context := child, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
    typingEnd := finish, ty := ty, mutable := mutable, contents := contents, rootsStart := source.rootsStart, rootsEnd := rootsFinish,
    roots := roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl,
      ⟨rfl, rfl, rfl, HEq.rfl, fun alias member =>
        ec.child_retained_subset rfl 0 (.place place) .place rfl (by trivial) member,
        hinput, hfuture⟩⟩
  · exact ec.child_activeMatches rfl 0 (.place place) .place rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.place place) .place rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact (Core.Sound.PMono.addReads _ _ _ _ hadd).2.trans (by simpa only [hrootsEnd] using source.effects)

theorem ViewSource.valChild {cfg : Cfg} {env : Env} {expr : Expr} {state : St} (source : ViewSource cfg env (.val expr) state) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ ∃ mutability, child.ty = .slice mutability source.element ∧ source.ExpressionChildAt child := by
  have ht := source.typed
  simp only [tyView] at ht
  inv at ht
  obtain ⟨inputTy, finish, ht, htail⟩ := ht
  cases inputTy <;> inv at htail
  rename_i mutability element
  obtain ⟨helement, hmutable, hend⟩ := htail
  have hr := source.rooted
  simp only [rpView] at hr
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
      DemandNode.variables, DemandNode.visibleAfter, Expr.variables, View.variables]
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := (source.path ++ [0]),
    context := child, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := source.typingStart,
    typingEnd := finish, ty := .slice mutability element, rootsStart := source.rootsStart, rootsEnd := source.rootsEnd,
    roots := source.roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl, mutability, by rw [helement],
    ⟨rfl, rfl, rfl, HEq.rfl, fun alias member => ec.child_retained_subset rfl 0
      (.expression expr) .expression rfl (by trivial) member, hinput, hfuture⟩⟩
  · exact ec.child_activeMatches rfl 0 (.expression expr) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.expression expr) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact source.effects

theorem ExprSource.refChild {cfg : Cfg} {env : Env} {place : Place} {state : St} (mutability : Mutability)
    (source : ExprSource cfg env (.ref mutability place) state) :
    ∃ child : PlaceSource cfg env place state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  obtain ⟨ty, mutable, contents, finish, ht, hallowed, htarget, hresult⟩ := ht
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
    typingEnd := finish, ty := ty, mutable := mutable, contents := contents, rootsStart := source.rootsStart, rootsEnd := source.rootsEnd,
    roots := source.roots, active := ?_, access := ?_, protection := ?_, observed := ?_,
    classified := source.classified, permission := source.permission, frame := ?_,
    typed := ht, rooted := hr, effects := ?_ }, rfl, rfl⟩
  · exact ec.child_activeMatches rfl 0 (.place place) .place rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl)
  · exact (ec.child_accessMatches_iff rfl 0 (.place place) .place rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access
  · simpa [hshrink] using source.protection
  · simpa [hshrink] using source.observed
  · simpa [hinput] using source.frame
  · exact source.effects

theorem ExprSource.binChildren {cfg : Cfg} {env : Env} {a b : Expr} {state : St}
    (op : BinOp) (origin : OriginId) (source : ExprSource cfg env (.bin op a b origin) state) :
    ∃ intTy, ∃ left : ExprSource cfg env a state,
      left.typingEnv = source.typingEnv ∧ left.rootsEnv = source.rootsEnv ∧ left.ty = .int intTy ∧ source.ChildAt left 0 rfl ∧
      ∀ n value after, evalExpr n cfg env a state = .ok value after →
        ∃ right : ExprSource cfg env b after, right.typingEnv = source.typingEnv ∧
          right.rootsEnv = source.rootsEnv ∧ right.ty = .int intTy ∧ source.ChildAt right 1 rfl := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨_, ta, t1, hta, intTy, rfl, tb, t2, htb, other, rfl, rfl, htype, hend⟩ := ht
  obtain ⟨ra, r1, hra, rb, r2, hrb, htail⟩ := hr
  have hE2 : EffLe r2.eff source.world.E := by
    refine EffLe.trans ?_ source.effects
    rcases htail with ⟨_, next, hnext, _, rfl⟩ | ⟨_, _, rfl⟩
    · exact (Core.Sound.PMono.noteAborts _ _ _ hnext).2
    · exact EffLe.refl _
  let ec := source.context
  let lc := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
  let rc := ec.child rfl 1 (.expression b) .expression rfl (by trivial)
  have hFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      state ec.inputFuture := source.frame
  have hActive : ec.ActiveMatches source.typingEnv := source.active
  have hLeftShrink : lc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
      (by trivial) source.world.ownerP source.observation root)
  have hRightShrink : rc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 1 (.expression b) .expression rfl
      (by trivial) source.world.ownerP source.observation root)
  have hLeftFuture : lc.outputFuture = match (generalizing := false) ec with
      | .pilot _ active => active
      | .shrink _ context => b.variables ++ context.expected.frame.future := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active =>
      simp [hec, EvaluationContext.child, EvaluationContext.outputFuture,
        DemandNode.visibleAfter, DemandNode.visibleForChild]
    | shrink profile context =>
      let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
      change transition.context.expected.frame.future = b.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hLeftInput : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      state lc.inputFuture := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hFrame
      apply hFrame.narrowFuture
      intro x hx
      change x ∈ a.variables ++ active at hx
      simp only [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
        DemandNode.visibleAfter]
      rcases List.mem_append.mp hx with hxa | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hxa)
      · exact List.mem_append_right _ hactive
    | shrink profile context =>
      dsimp only [lc] at hLeftFuture
      rw [hec] at hFrame hLeftFuture
      have hformula : ((EvaluationContext.shrink profile context).child rfl 0
          (.expression a) .expression rfl (by trivial)).inputFuture = a.variables ++
          ((EvaluationContext.shrink profile context).child rfl 0
          (.expression a) .expression rfl (by trivial)).outputFuture := rfl
      rw [hformula, hLeftFuture]
      simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
        DemandNode.variables, Expr.variables, List.append_assoc] using hFrame
  let left : ExprSource cfg env a state := {
    accepted := source.accepted, plans := source.plans, path := source.path ++ [0], context := lc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := source.typingStart, typingEnd := t1, ty := .int intTy,
    rootsStart := source.rootsStart, rootsEnd := r1, roots := ra,
    active := ec.child_activeMatches rfl 0 (.expression a) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hLeftShrink] using source.protection,
    observed := by simpa [hLeftShrink] using source.observed,
    classified := source.classified, permission := source.permission, frame := hLeftInput,
    typed := hta, rooted := hra, effects := (Core.Sound.rpExpr_mono hrb).2.trans hE2 }
  have leftMetadata : source.ChildAt left 0 rfl :=
    ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, fun alias member =>
      ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) member⟩
  refine ⟨intTy, left, rfl, rfl, rfl, leftMetadata, ?_⟩
  intro n value after hdone
  have output := left.result n value hdone
  have hF1 : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      after lc.outputFuture := output.frame
  have hRightOutput : rc.outputFuture = ec.outputFuture := by
    dsimp only [rc]
    cases hec : ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 1 (.expression b) .expression rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hRightInput : rc.inputFuture = b.variables ++ ec.outputFuture := by
    have hformula : rc.inputFuture = b.variables ++ rc.outputFuture := by
      dsimp only [rc]
      cases ec <;> rfl
    rw [hformula, hRightOutput]
  have hFrameRight : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      after rc.inputFuture := by
    rw [hRightInput]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hActive
      dsimp only [lc] at hF1
      rw [hec] at hF1
      apply hF1.changeFuture
      intro x hx _
      exact (hActive x).mpr hx
    | shrink profile context =>
      rw [hec] at hLeftFuture
      have hfuture : lc.outputFuture = b.variables ++ context.expected.frame.future := by
        simpa [EvaluationContext.outputFuture] using hLeftFuture
      have framed : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
          after (b.variables ++ context.expected.frame.future) := by
        simpa only [hfuture] using hF1
      simpa [EvaluationContext.outputFuture, Core.Sound.NodeContext.outputFuture] using framed
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [1], context := rc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := t1, typingEnd := t2, ty := .int intTy,
    rootsStart := r1, rootsEnd := r2, roots := rb,
    active := ec.child_activeMatches rfl 1 (.expression b) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 1 (.expression b) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hRightShrink] using source.protection,
    observed := by simpa only [left, hLeftShrink, hRightShrink] using output.observed,
    classified := output.classified, permission := source.permission, frame := hFrameRight,
    typed := htb, rooted := hrb, effects := hE2 }, rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, fun alias member =>
      ec.child_retained_subset rfl 1 (.expression b) .expression rfl (by trivial) member⟩⟩

theorem PlaceSource.elemChildren {cfg : Cfg} {env : Env} {view : View} {index : Expr} {state : St}
    (origin : OriginId) (source : PlaceSource cfg env (.elem view index origin) state) :
    ∃ intTy, ∃ left : ViewSource cfg env view state,
      left.typingEnv = source.typingEnv ∧ left.rootsEnv = source.rootsEnv ∧ source.ViewChildAt left 0 rfl ∧
      ∀ n value after, evalView n cfg env view state = .ok value after →
        ∃ right : ExprSource cfg env index after, right.typingEnv = source.typingEnv ∧
          right.rootsEnv = source.rootsEnv ∧ right.ty = .int intTy ∧ source.ExpressionChildAt right 1 rfl := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyPlace] at ht
  inv at ht
  simp only [rpPlace] at hr
  inv at hr
  obtain ⟨_, element, mutable, t1, hta, inputTy, t2, htb, intTy, rfl,
    htype, hmutable, hcontents, hend⟩ := ht
  obtain ⟨ra, r1, hra, rb, r2, hrb, r3, hnote, hroot, hrootEnd⟩ := hr
  have hE2 : EffLe r2.eff source.world.E :=
    (Core.Sound.PMono.noteAborts _ _ _ hnote).2.trans (by simpa only [hrootEnd] using source.effects)
  let ec := source.context
  let lc := ec.child rfl 0 (.view view) .view rfl (by trivial)
  let rc := ec.child rfl 1 (.expression index) .expression rfl (by trivial)
  have hFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      state ec.inputFuture := source.frame
  have hActive : ec.ActiveMatches source.typingEnv := source.active
  have hLeftShrink : lc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.view view) .view rfl
      (by trivial) source.world.ownerP source.observation root)
  have hRightShrink : rc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 1 (.expression index) .expression rfl
      (by trivial) source.world.ownerP source.observation root)
  have hLeftFuture : lc.outputFuture = match (generalizing := false) ec with
      | .pilot _ active => active
      | .shrink _ context => index.variables ++ context.expected.frame.future := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active =>
      simp [hec, EvaluationContext.child, EvaluationContext.outputFuture,
        DemandNode.visibleAfter, DemandNode.visibleForChild]
    | shrink profile context =>
      let transition := context.child rfl 0 (.view view) .view rfl (by trivial)
      change transition.context.expected.frame.future = index.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hLeftInput : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      state lc.inputFuture := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hFrame
      apply hFrame.narrowFuture
      intro x hx
      change x ∈ view.variables ++ active at hx
      simp only [EvaluationContext.inputFuture, DemandNode.variables, Place.variables, Expr.variables, View.variables,
        DemandNode.visibleAfter]
      rcases List.mem_append.mp hx with hxa | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hxa)
      · exact List.mem_append_right _ hactive
    | shrink profile context =>
      dsimp only [lc] at hLeftFuture
      rw [hec] at hFrame hLeftFuture
      have hformula : ((EvaluationContext.shrink profile context).child rfl 0
          (.view view) .view rfl (by trivial)).inputFuture = view.variables ++
          ((EvaluationContext.shrink profile context).child rfl 0
          (.view view) .view rfl (by trivial)).outputFuture := rfl
      rw [hformula, hLeftFuture]
      simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
        DemandNode.variables, Place.variables, Expr.variables, View.variables, List.append_assoc] using hFrame
  let left : ViewSource cfg env view state := {
    accepted := source.accepted, plans := source.plans, path := source.path ++ [0], context := lc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := source.typingStart, typingEnd := t1, element := element, mutable := mutable,
    rootsStart := source.rootsStart, rootsEnd := r1, roots := ra,
    active := ec.child_activeMatches rfl 0 (.view view) .view rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 0 (.view view) .view rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hLeftShrink] using source.protection,
    observed := by simpa [hLeftShrink] using source.observed,
    classified := source.classified, permission := source.permission, frame := hLeftInput,
    typed := hta, rooted := hra, effects := (Core.Sound.rpExpr_mono hrb).2.trans hE2 }
  refine ⟨intTy, left, rfl, rfl,
    ⟨rfl, rfl, rfl, HEq.rfl, fun alias member =>
      ec.child_retained_subset rfl 0 (.view view) .view rfl (by trivial) member⟩, ?_⟩
  intro n value after hdone
  have output := left.result n value hdone
  have hF1 : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      after lc.outputFuture := output.frame
  have hRightOutput : rc.outputFuture = ec.outputFuture := by
    dsimp only [rc]
    cases hec : ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 1 (.expression index) .expression rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hRightInput : rc.inputFuture = index.variables ++ ec.outputFuture := by
    have hformula : rc.inputFuture = index.variables ++ rc.outputFuture := by
      dsimp only [rc]
      cases ec <;> rfl
    rw [hformula, hRightOutput]
  have hFrameRight : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      after rc.inputFuture := by
    rw [hRightInput]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hActive
      dsimp only [lc] at hF1
      rw [hec] at hF1
      apply hF1.changeFuture
      intro x hx _
      exact (hActive x).mpr hx
    | shrink profile context =>
      rw [hec] at hLeftFuture
      have hfuture : lc.outputFuture = index.variables ++ context.expected.frame.future := by
        simpa [EvaluationContext.outputFuture] using hLeftFuture
      have framed : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
          after (index.variables ++ context.expected.frame.future) := by
        simpa only [hfuture] using hF1
      simpa [EvaluationContext.outputFuture, Core.Sound.NodeContext.outputFuture] using framed
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [1], context := rc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := t1, typingEnd := t2, ty := .int intTy,
    rootsStart := r1, rootsEnd := r2, roots := rb,
    active := ec.child_activeMatches rfl 1 (.expression index) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 1 (.expression index) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hRightShrink] using source.protection,
    observed := by simpa only [left, hLeftShrink, hRightShrink] using output.observed,
    classified := output.classified, permission := source.permission, frame := hFrameRight,
    typed := htb, rooted := hrb, effects := hE2 }, rfl, rfl, rfl,
      ⟨rfl, rfl, rfl, HEq.rfl, fun alias member =>
        ec.child_retained_subset rfl 1 (.expression index) .expression rfl (by trivial) member⟩⟩

theorem ExprSource.pushChildren {cfg : Cfg} {env : Env} {owner : Place} {argument : Expr} {state : St}
    (origin : Option OriginId) (source : ExprSource cfg env (.push owner argument origin) state) :
    ∃ left : PlaceSource cfg env owner state,
      left.typingEnv = source.typingEnv ∧ left.rootsEnv = source.rootsEnv ∧
      ∀ n value after, evalPlace n cfg env owner state = .ok value after →
        ∃ right : ExprSource cfg env argument after, right.typingEnv = source.typingEnv ∧
          right.rootsEnv = source.rootsEnv := by
  have ht := source.typed
  have hr := source.rooted
  have hprofileOrg := Core.Sound.tyExpr_push_profileOrg_ok source.typingEnv owner argument origin
    source.ty source.typingStart source.typingEnd ht
  rw [source.frame.mod_t] at hprofileOrg
  have hcore : ∃ ownerTy binding contents t1,
      tyPlace source.typingEnv owner source.typingStart = .ok (⟨ownerTy, binding, contents⟩, t1) ∧
        ∃ element ownerState, ownerElement source.typingEnv ownerTy t1 = .ok (element, ownerState) ∧
          ∃ argumentTy t2, tyExpr source.typingEnv argument ownerState = .ok (argumentTy, t2) ∧
            argumentTy = element ∧
              (requireWrite "push" ((⟨ownerTy, binding, contents⟩ : PlaceInfo).ownerMutationWritable
                source.typingEnv.mod.profile) >>= fun _ => pure (.ref .mutable element)) t2 =
                .ok (source.ty, source.typingEnd) := by
    rcases hprofileOrg with ⟨hprofile, horg⟩ | ⟨hprofile, ⟨org, horg⟩⟩
    · have hprofileT := (congrArg Core.Module.profile source.frame.mod_t).trans hprofile
      simp [tyExpr, source.frame.mod_t, hprofile, hprofileT, horg, checkOrg] at ht
      inv at ht
      simpa [hprofileT] using ht
    · have hprofileT := (congrArg Core.Module.profile source.frame.mod_t).trans hprofile
      simp [tyExpr, source.frame.mod_t, hprofile, hprofileT, horg, checkOrg] at ht
      inv at ht
      simpa [hprofileT] using ht.2
  obtain ⟨ownerTy, binding, contents, t1, hta, element, ownerState, helement,
    argumentTy, t2, htb, hargumentType, hwrite⟩ := hcore
  simp only [rpExpr] at hr
  obtain ⟨ra, r1, hra, tail1⟩ := (Core.Sound.st_bind_ok _ _ _ _).1 hr
  obtain ⟨rb, r2, hrb, tail2⟩ := (Core.Sound.st_bind_ok _ _ _ _).1 tail1
  obtain ⟨_, r3, hgrow, htail⟩ := (Core.Sound.st_bind_ok _ _ _ _).1 tail2
  have hE3 : EffLe r3.eff source.world.E :=
    ((Core.Sound.PMono.profileWriteAbortValue source.rootsEnv owner ra) r3 source.roots
      source.rootsEnd htail).2.trans source.effects
  have hE2 := (Core.Sound.PMono.addGrows _ _ _ _ hgrow).2.trans hE3
  let ec := source.context
  let lc := ec.child rfl 0 (.place owner) .place rfl (by trivial)
  let rc := ec.child rfl 1 (.expression argument) .expression rfl (by trivial)
  have hFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      state ec.inputFuture := source.frame
  have hActive : ec.ActiveMatches source.typingEnv := source.active
  have hLeftShrink : lc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.place owner) .place rfl
      (by trivial) source.world.ownerP source.observation root)
  have hRightShrink : rc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 1 (.expression argument) .expression rfl
      (by trivial) source.world.ownerP source.observation root)
  have hLeftFuture : lc.outputFuture = match (generalizing := false) ec with
      | .pilot _ active => active
      | .shrink _ context => argument.variables ++ context.expected.frame.future := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active =>
      simp [hec, EvaluationContext.child, EvaluationContext.outputFuture,
        DemandNode.visibleAfter, DemandNode.visibleForChild]
    | shrink profile context =>
      let transition := context.child rfl 0 (.place owner) .place rfl (by trivial)
      change transition.context.expected.frame.future = argument.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hLeftInput : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      state lc.inputFuture := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hFrame
      apply hFrame.narrowFuture
      intro x hx
      change x ∈ owner.variables ++ active at hx
      simp only [EvaluationContext.inputFuture, DemandNode.variables, Place.variables, Expr.variables, View.variables,
        DemandNode.visibleAfter]
      rcases List.mem_append.mp hx with hxa | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hxa)
      · exact List.mem_append_right _ hactive
    | shrink profile context =>
      dsimp only [lc] at hLeftFuture
      rw [hec] at hFrame hLeftFuture
      have hformula : ((EvaluationContext.shrink profile context).child rfl 0
          (.place owner) .place rfl (by trivial)).inputFuture = owner.variables ++
          ((EvaluationContext.shrink profile context).child rfl 0
          (.place owner) .place rfl (by trivial)).outputFuture := rfl
      rw [hformula, hLeftFuture]
      simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
        DemandNode.variables, Place.variables, Expr.variables, View.variables, List.append_assoc] using hFrame
  let left : PlaceSource cfg env owner state := {
    accepted := source.accepted, plans := source.plans, path := source.path ++ [0], context := lc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := source.typingStart, typingEnd := t1, ty := ownerTy, mutable := binding, contents := contents,
    rootsStart := source.rootsStart, rootsEnd := r1, roots := ra,
    active := ec.child_activeMatches rfl 0 (.place owner) .place rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 0 (.place owner) .place rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hLeftShrink] using source.protection,
    observed := by simpa [hLeftShrink] using source.observed,
    classified := source.classified, permission := source.permission, frame := hLeftInput,
    typed := hta, rooted := hra, effects := (Core.Sound.rpExpr_mono hrb).2.trans hE2 }
  refine ⟨left, rfl, rfl, ?_⟩
  intro n value after hdone
  have output := left.result n value hdone
  have hF1 : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      after lc.outputFuture := output.frame
  have hRightOutput : rc.outputFuture = ec.outputFuture := by
    dsimp only [rc]
    cases hec : ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 1 (.expression argument) .expression rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hRightInput : rc.inputFuture = argument.variables ++ ec.outputFuture := by
    have hformula : rc.inputFuture = argument.variables ++ rc.outputFuture := by
      dsimp only [rc]
      cases ec <;> rfl
    rw [hformula, hRightOutput]
  have hFrameRight : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      after rc.inputFuture := by
    rw [hRightInput]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hActive
      dsimp only [lc] at hF1
      rw [hec] at hF1
      apply hF1.changeFuture
      intro x hx _
      exact (hActive x).mpr hx
    | shrink profile context =>
      rw [hec] at hLeftFuture
      have hfuture : lc.outputFuture = argument.variables ++ context.expected.frame.future := by
        simpa [EvaluationContext.outputFuture] using hLeftFuture
      have framed : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
          after (argument.variables ++ context.expected.frame.future) := by
        simpa only [hfuture] using hF1
      simpa [EvaluationContext.outputFuture, Core.Sound.NodeContext.outputFuture] using framed
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [1], context := rc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := ownerState, typingEnd := t2, ty := argumentTy,
    rootsStart := r1, rootsEnd := r2, roots := rb,
    active := ec.child_activeMatches rfl 1 (.expression argument) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 1 (.expression argument) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hRightShrink] using source.protection,
    observed := by simpa only [left, hLeftShrink, hRightShrink] using output.observed,
    classified := output.classified, permission := source.permission, frame := hFrameRight,
    typed := htb, rooted := hrb, effects := hE2 }, rfl, rfl⟩

theorem ExprSource.cmpChildren {cfg : Cfg} {env : Env} {a b : Expr} {state : St}
    (op : CmpOp) (source : ExprSource cfg env (.cmp op a b) state) :
    ∃ left : ExprSource cfg env a state,
      left.typingEnv = source.typingEnv ∧ left.rootsEnv = source.rootsEnv ∧ source.ChildAt left 0 rfl ∧
      ∀ n value after, evalExpr n cfg env a state = .ok value after →
        ∃ right : ExprSource cfg env b after, right.typingEnv = source.typingEnv ∧
          right.rootsEnv = source.rootsEnv ∧ source.ChildAt right 1 rfl := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨ta, t1, hta, tb, t2, htb, hcompare⟩ := ht
  obtain ⟨ra, r1, hra, rb, r2, hrb, hroot, hrootEnd⟩ := hr
  have hE2 : EffLe r2.eff source.world.E := by
    rw [← hrootEnd]
    exact source.effects
  let ec := source.context
  let lc := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
  let rc := ec.child rfl 1 (.expression b) .expression rfl (by trivial)
  have hFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      state ec.inputFuture := source.frame
  have hActive : ec.ActiveMatches source.typingEnv := source.active
  have hLeftShrink : lc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
      (by trivial) source.world.ownerP source.observation root)
  have hRightShrink : rc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 1 (.expression b) .expression rfl
      (by trivial) source.world.ownerP source.observation root)
  have hLeftFuture : lc.outputFuture = match (generalizing := false) ec with
      | .pilot _ active => active
      | .shrink _ context => b.variables ++ context.expected.frame.future := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active =>
      simp [hec, EvaluationContext.child, EvaluationContext.outputFuture,
        DemandNode.visibleAfter, DemandNode.visibleForChild]
    | shrink profile context =>
      let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
      change transition.context.expected.frame.future = b.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hLeftInput : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      state lc.inputFuture := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hFrame
      apply hFrame.narrowFuture
      intro x hx
      change x ∈ a.variables ++ active at hx
      simp only [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
        DemandNode.visibleAfter]
      rcases List.mem_append.mp hx with hxa | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hxa)
      · exact List.mem_append_right _ hactive
    | shrink profile context =>
      dsimp only [lc] at hLeftFuture
      rw [hec] at hFrame hLeftFuture
      have hformula : ((EvaluationContext.shrink profile context).child rfl 0
          (.expression a) .expression rfl (by trivial)).inputFuture = a.variables ++
          ((EvaluationContext.shrink profile context).child rfl 0
          (.expression a) .expression rfl (by trivial)).outputFuture := rfl
      rw [hformula, hLeftFuture]
      simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
        DemandNode.variables, Expr.variables, List.append_assoc] using hFrame
  let left : ExprSource cfg env a state := {
    accepted := source.accepted, plans := source.plans, path := source.path ++ [0], context := lc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := source.typingStart, typingEnd := t1, ty := ta,
    rootsStart := source.rootsStart, rootsEnd := r1, roots := ra,
    active := ec.child_activeMatches rfl 0 (.expression a) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hLeftShrink] using source.protection,
    observed := by simpa [hLeftShrink] using source.observed,
    classified := source.classified, permission := source.permission, frame := hLeftInput,
    typed := hta, rooted := hra, effects := (Core.Sound.rpExpr_mono hrb).2.trans hE2 }
  have leftMetadata : source.ChildAt left 0 rfl :=
    ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, fun alias member =>
      ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) member⟩
  refine ⟨left, rfl, rfl, leftMetadata, ?_⟩
  intro n value after hdone
  have output := left.result n value hdone
  have hF1 : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      after lc.outputFuture := output.frame
  have hRightOutput : rc.outputFuture = ec.outputFuture := by
    dsimp only [rc]
    cases hec : ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 1 (.expression b) .expression rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hRightInput : rc.inputFuture = b.variables ++ ec.outputFuture := by
    have hformula : rc.inputFuture = b.variables ++ rc.outputFuture := by
      dsimp only [rc]
      cases ec <;> rfl
    rw [hformula, hRightOutput]
  have hFrameRight : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      after rc.inputFuture := by
    rw [hRightInput]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hActive
      dsimp only [lc] at hF1
      rw [hec] at hF1
      apply hF1.changeFuture
      intro x hx _
      exact (hActive x).mpr hx
    | shrink profile context =>
      rw [hec] at hLeftFuture
      have hfuture : lc.outputFuture = b.variables ++ context.expected.frame.future := by
        simpa [EvaluationContext.outputFuture] using hLeftFuture
      have framed : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
          after (b.variables ++ context.expected.frame.future) := by
        simpa only [hfuture] using hF1
      simpa [EvaluationContext.outputFuture, Core.Sound.NodeContext.outputFuture] using framed
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [1], context := rc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := t1, typingEnd := t2, ty := tb,
    rootsStart := r1, rootsEnd := r2, roots := rb,
    active := ec.child_activeMatches rfl 1 (.expression b) .expression rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 1 (.expression b) .expression rfl
      (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hRightShrink] using source.protection,
    observed := by simpa only [left, hLeftShrink, hRightShrink] using output.observed,
    classified := output.classified, permission := source.permission, frame := hFrameRight,
    typed := htb, rooted := hrb, effects := hE2 }, rfl, rfl,
    ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, fun alias member =>
      ec.child_retained_subset rfl 1 (.expression b) .expression rfl (by trivial) member⟩⟩

theorem ExprSource.shortCircuitChildrenDemand {cfg : Cfg} {env : Env} {a b : Expr} {state : St}
    (isAnd : Bool) (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state) :
    ∃ left : ExprSource cfg env a state,
      left.typingEnv = source.typingEnv ∧ left.rootsEnv = source.rootsEnv ∧ left.ty = .bool ∧
      left.world = source.world ∧ left.path = source.path ++ [0] ∧ left.plans = source.plans ∧
      HEq left.context (source.context.child rfl 0 (.expression a) .expression
        (by cases isAnd <;> rfl) (by trivial)) ∧
      (∀ alias ∈ source.context.retained, alias ∈ left.context.retained) ∧
      ∀ n value after, evalExpr n cfg env a state = .ok value after →
        ∃ right : ExprSource cfg env b after, right.typingEnv = source.typingEnv ∧
          right.rootsEnv = source.rootsEnv ∧ right.ty = .bool ∧
          right.world = source.world ∧ right.path = source.path ++ [1] ∧ right.plans = source.plans ∧
          HEq right.context (source.context.child rfl 1 (.expression b) .expression
            (by cases isAnd <;> rfl) (by trivial)) ∧
          (∀ alias ∈ source.context.retained, alias ∈ right.context.retained) := by
  cases isAnd
  all_goals (
    have ht := source.typed
    have hr := source.rooted
    simp only [Bool.false_eq_true, ite_false, ite_true, tyExpr] at ht
    inv at ht
    simp only [Bool.false_eq_true, ite_false, ite_true, rpExpr] at hr
    inv at hr
    obtain ⟨ta, t1, hta, rfl, tb, t2, htb, rfl, htype, hend⟩ := ht
    obtain ⟨ra, r1, hra, rb, r2, hrb, hroot, hrootEnd⟩ := hr
    have hE2 : EffLe r2.eff source.world.E := by
      rw [← hrootEnd]
      exact source.effects
    let ec := source.context
    let lc := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
    let rc := ec.child rfl 1 (.expression b) .expression rfl (by trivial)
    have hFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
        state ec.inputFuture := source.frame
    have hActive : ec.ActiveMatches source.typingEnv := source.active
    have hLeftShrink : lc.mayShrink source.world.ownerP source.observation =
        ec.mayShrink source.world.ownerP source.observation := by
      funext root
      exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
        (by trivial) source.world.ownerP source.observation root)
    have hRightShrink : rc.mayShrink source.world.ownerP source.observation =
        ec.mayShrink source.world.ownerP source.observation := by
      funext root
      exact propext (ec.child_mayShrink_iff rfl 1 (.expression b) .expression rfl
        (by trivial) source.world.ownerP source.observation root)
    have hLeftFuture : lc.outputFuture = match (generalizing := false) ec with
        | .pilot _ active => active
        | .shrink _ context => b.variables ++ context.expected.frame.future := by
      dsimp only [lc]
      cases hec : ec with
      | pilot profile active =>
        simp [hec, EvaluationContext.child, EvaluationContext.outputFuture,
          DemandNode.visibleAfter, DemandNode.visibleForChild]
      | shrink profile context =>
        let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
        change transition.context.expected.frame.future = b.variables ++ context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hLeftInput : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
        state lc.inputFuture := by
      dsimp only [lc]
      cases hec : ec with
      | pilot profile active =>
        rw [hec] at hFrame
        apply hFrame.narrowFuture
        intro x hx
        change x ∈ a.variables ++ active at hx
        simp only [Bool.false_eq_true, ite_false, ite_true, EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
          DemandNode.visibleAfter]
        rcases List.mem_append.mp hx with hxa | hactive
        · exact List.mem_append_left _ (List.mem_append_left _ hxa)
        · exact List.mem_append_right _ hactive
      | shrink profile context =>
        dsimp only [lc] at hLeftFuture
        rw [hec] at hFrame hLeftFuture
        have hformula : ((EvaluationContext.shrink profile context).child rfl 0
            (.expression a) .expression rfl (by trivial)).inputFuture = a.variables ++
            ((EvaluationContext.shrink profile context).child rfl 0
            (.expression a) .expression rfl (by trivial)).outputFuture := rfl
        rw [hformula, hLeftFuture]
        simpa [Bool.false_eq_true, ite_false, ite_true, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
          DemandNode.variables, Expr.variables, List.append_assoc] using hFrame
    let left : ExprSource cfg env a state := {
      accepted := source.accepted, plans := source.plans, path := source.path ++ [0], context := lc,
      observation := source.observation, world := source.world, typingEnv := source.typingEnv,
      rootsEnv := source.rootsEnv, typingStart := source.typingStart, typingEnd := t1, ty := .bool,
      rootsStart := source.rootsStart, rootsEnd := r1, roots := ra,
      active := ec.child_activeMatches rfl 0 (.expression a) .expression rfl (by trivial)
        source.typingEnv source.typingEnv source.active (by intro x; rfl),
      access := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
      protection := by simpa [hLeftShrink] using source.protection,
      observed := by simpa [hLeftShrink] using source.observed,
      classified := source.classified, permission := source.permission, frame := hLeftInput,
      typed := hta, rooted := hra, effects := (Core.Sound.rpExpr_mono hrb).2.trans hE2 }
    refine ⟨left, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl, ?_, ?_⟩
    · intro alias member
      exact ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) member
    intro n value after hdone
    have output := left.result n value hdone
    have hF1 : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
        after lc.outputFuture := output.frame
    have hRightOutput : rc.outputFuture = ec.outputFuture := by
      dsimp only [rc]
      cases hec : ec with
      | pilot profile active => rfl
      | shrink profile context =>
        let transition := context.child rfl 1 (.expression b) .expression rfl (by trivial)
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hRightInput : rc.inputFuture = b.variables ++ ec.outputFuture := by
      have hformula : rc.inputFuture = b.variables ++ rc.outputFuture := by
        dsimp only [rc]
        cases ec <;> rfl
      rw [hformula, hRightOutput]
    have hFrameRight : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
        after rc.inputFuture := by
      rw [hRightInput]
      cases hec : ec with
      | pilot profile active =>
        rw [hec] at hActive
        dsimp only [lc] at hF1
        rw [hec] at hF1
        apply hF1.changeFuture
        intro x hx _
        exact (hActive x).mpr hx
      | shrink profile context =>
        rw [hec] at hLeftFuture
        have hfuture : lc.outputFuture = b.variables ++ context.expected.frame.future := by
          simpa [EvaluationContext.outputFuture] using hLeftFuture
        have framed : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
            after (b.variables ++ context.expected.frame.future) := by
          simpa only [hfuture] using hF1
        simpa [EvaluationContext.outputFuture, Core.Sound.NodeContext.outputFuture] using framed
    refine ⟨{
      accepted := source.accepted, plans := source.plans, path := source.path ++ [1], context := rc,
      observation := source.observation, world := source.world, typingEnv := source.typingEnv,
      rootsEnv := source.rootsEnv, typingStart := t1, typingEnd := t2, ty := .bool,
      rootsStart := r1, rootsEnd := r2, roots := rb,
      active := ec.child_activeMatches rfl 1 (.expression b) .expression rfl (by trivial)
        source.typingEnv source.typingEnv source.active (by intro x; rfl),
      access := (ec.child_accessMatches_iff rfl 1 (.expression b) .expression rfl
        (by trivial) source.typingEnv source.rootsEnv).mpr source.access,
      protection := by simpa [hRightShrink] using source.protection,
      observed := by simpa only [left, hLeftShrink, hRightShrink] using output.observed,
      classified := output.classified, permission := source.permission, frame := hFrameRight,
      typed := htb, rooted := hrb, effects := hE2 }, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl, ?_⟩
    intro alias member
    exact ec.child_retained_subset rfl 1 (.expression b) .expression rfl (by trivial) member
  )


theorem ExprSource.shortCircuitChildren {cfg : Cfg} {env : Env} {a b : Expr} {state : St}
    (isAnd : Bool) (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state) :
    ∃ left : ExprSource cfg env a state,
      left.typingEnv = source.typingEnv ∧ left.rootsEnv = source.rootsEnv ∧ left.ty = .bool ∧
      ∀ n value after, evalExpr n cfg env a state = .ok value after →
        ∃ right : ExprSource cfg env b after, right.typingEnv = source.typingEnv ∧
          right.rootsEnv = source.rootsEnv ∧ right.ty = .bool := by
  obtain ⟨left, typing, roots, type, _, _, _, _, _, next⟩ := source.shortCircuitChildrenDemand isAnd
  refine ⟨left, typing, roots, type, ?_⟩
  intro fuel value after done
  obtain ⟨right, rightTyping, rightRoots, rightType, _, _, _, _, _⟩ := next fuel value after done
  exact ⟨right, rightTyping, rightRoots, rightType⟩

theorem ExprSource.sliceChildren {cfg : Cfg} {env : Env} {view : View} {low high : Bound}
    {state : St} (mutability : Mutability) (origin : OriginId)
    (source : ExprSource cfg env (.slice mutability view low high origin) state) :
    ∃ sampled : ViewSource cfg env view state,
      sampled.typingEnv = source.typingEnv ∧ sampled.rootsEnv = source.rootsEnv ∧
      source.ViewChildAt sampled 0 rfl ∧
      ∀ n value after, evalView n cfg env view state = .ok value after →
        ∃ lower : BoundSource cfg env low after,
          lower.typingEnv = source.typingEnv ∧ lower.rootsEnv = source.rootsEnv ∧
          source.BoundChildAt lower 1 rfl ∧
          ∀ k lowerValue lowerAfter,
            evalBound k cfg env value.len 0 low after = .ok lowerValue lowerAfter →
            ∃ upper : BoundSource cfg env high lowerAfter,
              upper.typingEnv = source.typingEnv ∧ upper.rootsEnv = source.rootsEnv ∧
              source.BoundChildAt upper 2 rfl := by
  have ht := source.typed
  have hr := source.rooted
  simp only [tyExpr] at ht
  inv at ht
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨_, element, mutable, t1, hview, t2, hlow, t3, hhigh, htail⟩ := ht
  obtain ⟨roots, r1, hrview, r2, hrlow, r3, hrhigh, r4, hnote, hroots, hrootsEnd⟩ := hr
  have hE3 : EffLe r3.eff source.world.E :=
    (Core.Sound.PMono.noteAborts _ _ _ hnote).2.trans (by simpa only [hrootsEnd] using source.effects)
  have hE2 := (Core.Sound.rpBound_mono hrhigh).2.trans hE3
  have hE1 := (Core.Sound.rpBound_mono hrlow).2.trans hE2
  let ec := source.context
  let vc := ec.child rfl 0 (.view view) .view rfl (by trivial)
  let lc := ec.child rfl 1 (.bound low) .bound rfl (by trivial)
  let hc := ec.child rfl 2 (.bound high) .bound rfl (by trivial)
  have hFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      ec.inputFuture := source.frame
  have hActive : ec.ActiveMatches source.typingEnv := source.active
  have hVShrink : vc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.view view) .view rfl (by trivial)
      source.world.ownerP source.observation root)
  have hLShrink : lc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 1 (.bound low) .bound rfl (by trivial)
      source.world.ownerP source.observation root)
  have hHShrink : hc.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 2 (.bound high) .bound rfl (by trivial)
      source.world.ownerP source.observation root)
  have hVFuture : vc.outputFuture = match (generalizing := false) ec with
      | .pilot _ active => active
      | .shrink _ context => low.variables ++ high.variables ++ context.expected.frame.future := by
    dsimp only [vc]
    cases hec : ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 0 (.view view) .view rfl (by trivial)
      change transition.context.expected.frame.future =
        low.variables ++ high.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hLFuture : lc.outputFuture = match (generalizing := false) ec with
      | .pilot _ active => active
      | .shrink _ context => high.variables ++ context.expected.frame.future := by
    dsimp only [lc]
    cases hec : ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 1 (.bound low) .bound rfl (by trivial)
      change transition.context.expected.frame.future = high.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hHFuture : hc.outputFuture = ec.outputFuture := by
    dsimp only [hc]
    cases ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 2 (.bound high) .bound rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hVInput : vc.inputFuture = view.variables ++ vc.outputFuture := by
    dsimp only [vc]
    cases ec <;> rfl
  have hLInput : lc.inputFuture = low.variables ++ lc.outputFuture := by
    dsimp only [lc]
    cases ec <;> rfl
  have hHInput : hc.inputFuture = high.variables ++ hc.outputFuture := by
    dsimp only [hc]
    cases ec <;> rfl
  have hViewFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      vc.inputFuture := by
    rw [hVInput, hVFuture]
    cases hec : ec with
    | pilot profile active =>
      rw [hec] at hFrame
      apply hFrame.narrowFuture
      intro x hx
      simp only [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
        List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (Or.inl (Or.inl hx))
      · exact Or.inr hx
    | shrink profile context =>
      rw [hec] at hFrame
      simpa [EvaluationContext.inputFuture, Core.Sound.NodeContext.inputFuture,
        DemandNode.variables, Expr.variables, List.append_assoc] using hFrame
  let sampled : ViewSource cfg env view state := {
    accepted := source.accepted, plans := source.plans, path := source.path ++ [0], context := vc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := source.typingStart, typingEnd := t1,
    element := element, mutable := mutable, rootsStart := source.rootsStart, rootsEnd := r1,
    roots := roots, active := ec.child_activeMatches rfl 0 (.view view) .view rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 0 (.view view) .view rfl (by trivial)
      source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hVShrink] using source.protection,
    observed := by simpa [hVShrink] using source.observed,
    classified := source.classified, permission := source.permission, frame := hViewFrame,
    typed := hview, rooted := hrview, effects := hE1 }
  refine ⟨sampled, rfl, rfl, ⟨rfl, rfl, rfl, HEq.rfl, fun alias member =>
    ec.child_retained_subset rfl 0 (.view view) .view rfl (by trivial) member⟩, ?_⟩
  intro n value after hdone
  have viewResult := sampled.result n value hdone
  have hVF : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
      vc.outputFuture := viewResult.frame
  have hLowFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
      lc.inputFuture := by
    rw [hLInput, hLFuture]
    cases hec : ec with
    | pilot profile active =>
      dsimp only [vc] at hVF
      rw [hec] at hVF hActive
      apply hVF.changeFuture
      intro x hx _
      exact (hActive x).mpr hx
    | shrink profile context =>
      rw [hVFuture, hec] at hVF
      simpa [List.append_assoc] using hVF
  let lower : BoundSource cfg env low after := {
    accepted := source.accepted, plans := source.plans, path := source.path ++ [1], context := lc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := t1, typingEnd := t2,
    rootsStart := r1, rootsEnd := r2,
    active := ec.child_activeMatches rfl 1 (.bound low) .bound rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 1 (.bound low) .bound rfl (by trivial)
      source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hLShrink] using source.protection,
    observed := by simpa only [sampled, hVShrink, hLShrink] using viewResult.observed,
    classified := viewResult.classified, permission := source.permission, frame := hLowFrame,
    typed := hlow, rooted := hrlow, effects := hE2 }
  refine ⟨lower, rfl, rfl, ⟨rfl, rfl, rfl, HEq.rfl, fun alias member =>
    ec.child_retained_subset rfl 1 (.bound low) .bound rfl (by trivial) member⟩, ?_⟩
  intro k lowerValue lowerAfter hlowDone
  have lowResult := lower.result k value.len 0 lowerValue hlowDone
  have hLF : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env lowerAfter
      lc.outputFuture := lowResult.frame
  have hHighFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env lowerAfter
      hc.inputFuture := by
    rw [hHInput, hHFuture]
    cases hec : ec with
    | pilot profile active =>
      dsimp only [lc] at hLF
      rw [hec] at hLF hActive
      apply hLF.changeFuture
      intro x hx _
      exact (hActive x).mpr hx
    | shrink profile context =>
      rw [hLFuture, hec] at hLF
      simpa [EvaluationContext.outputFuture, Core.Sound.NodeContext.outputFuture] using hLF
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [2], context := hc,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := t2, typingEnd := t3,
    rootsStart := r2, rootsEnd := r3,
    active := ec.child_activeMatches rfl 2 (.bound high) .bound rfl (by trivial)
      source.typingEnv source.typingEnv source.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 2 (.bound high) .bound rfl (by trivial)
      source.typingEnv source.rootsEnv).mpr source.access,
    protection := by simpa [hHShrink] using source.protection,
    observed := by simpa only [lower, hLShrink, hHShrink] using lowResult.observed,
    classified := lowResult.classified, permission := source.permission, frame := hHighFrame,
    typed := hhigh, rooted := hrhigh, effects := hE3 }, rfl, rfl,
    ⟨rfl, rfl, rfl, HEq.rfl, fun alias member =>
      ec.child_retained_subset rfl 2 (.bound high) .bound rfl (by trivial) member⟩⟩

theorem typedExprClaim_zero (cfg : Cfg) (results : List Ty) (expr : Expr) :
    TypedExprClaim 0 cfg results expr := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  simp only [evalExpr]
  exact SimEAt.of_timeout state

theorem typedPlaceClaim_zero (cfg : Cfg) (results : List Ty) (place : Place) :
    TypedPlaceClaim 0 cfg results place := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  simp only [evalPlace]
  exact SimEAt.of_timeout state

theorem typedBoundClaim_zero (cfg : Cfg) (results : List Ty) (bound : Bound) :
    TypedBoundClaim 0 cfg results bound := by
  intro env state source hmetadata ls ls' bnd pt cx fr length default hlow hpp hext hrel hgir hresults hgenerated
  simp only [evalBound]
  exact SimEAt.of_timeout state

theorem typedBoundClaim_omitted (n : Nat) (cfg : Cfg) (results : List Ty) :
    TypedBoundClaim n cfg results .omitted := by
  cases n with
  | zero => exact typedBoundClaim_zero _ _ _
  | succ n =>
    intro env state source hmetadata ls ls' bnd pt cx fr length default hlow hpp hext hrel hgir hresults hgenerated
    simp only [lowerBound, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    simp only [evalBound]
    exact SimEAt.ret ⟨[], ⟨rfl, rfl⟩, Post.init hrel hpp⟩

private theorem typedBoundClaim_expression {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) (fromEnd : Bool) :
    TypedBoundClaim (n + 1) cfg results (if fromEnd then .fromEnd expr else .expr expr) := by
  cases fromEnd
  all_goals (
    intro env state source hmetadata ls ls' bnd pt cx fr length default hlow hpp hext hrel hgir hresults hgenerated
    obtain ⟨child, htyping, hroots, intTy, htype, _⟩ := source.expressionChild _
    have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
      rw [htyping, hroots]
      exact hmetadata
    simp only [Bool.false_eq_true, ite_false, ite_true, lowerBound, bind_eq] at hlow
    obtain ⟨id, middle, hchild, hpure⟩ := hlow
    rw [pure_run] at hpure
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpure
    simp only [Bool.false_eq_true, ite_false, ite_true, evalBound]
    refine SimEAt.bind (he env state child hchildMetadata ls middle id pt cx fr hchild hpp hext
      hrel hgir hresults hgenerated) fun value after pt' fr' hdone P => ?_
    have hvalue := (child.result n value hdone).typed
    rw [htype] at hvalue
    obtain ⟨integer, rfl⟩ := Core.Sound.hasTy_int hvalue
    simp only [Core.expectInt, pure_bind]
    refine SimEAt.ret ⟨[(id, .val (.int intTy integer))], ?_, P⟩
    first | exact ⟨intTy, rfl⟩ | exact ⟨intTy, integer, rfl, rfl⟩
  )

theorem typedBoundClaim_expr {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedBoundClaim (n + 1) cfg results (.expr expr) :=
  typedBoundClaim_expression he false

theorem typedBoundClaim_fromEnd {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedBoundClaim (n + 1) cfg results (.fromEnd expr) :=
  typedBoundClaim_expression he true

theorem typedViewClaim_zero (cfg : Cfg) (results : List Ty) (view : View) :
    TypedViewClaim 0 cfg results view := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  simp only [evalView]
  exact SimEAt.of_timeout state

theorem typedViewClaim_of {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) : TypedViewClaim (n + 1) cfg results (.of place) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots, _⟩ := source.ofChild
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerView, bind_eq] at hlow
  obtain ⟨address, middle, hplace, hview⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitDef hview)
  simp only [evalView]
  refine SimEAt.bind (hp env state child hchildMetadata ls middle address pt cx fr hplace hpp
    hextMiddle hrel hgir hresults hgenerated) fun location after pt' fr' hdone P => ?_
  have hcell := P.has (address, .val (.ref location)) (by simp)
  apply SimEAt.of_simG
  refine leaf_def P hview hext (by simp) RVal.view ?_
  simp only [execPure, getVal_of hcell, Core.expectRef, pure_bind, bind_assoc]

theorem typedViewClaim_val {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedViewClaim (n + 1) cfg results (.val expr) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots, mutability, htype, _⟩ := source.valChild
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerView, bind_eq] at hlow
  obtain ⟨id, middle, hchild, hview⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitDef hview)
  simp only [evalView]
  refine SimEAt.bind (he env state child hchildMetadata ls middle id pt cx fr hchild hpp
    hextMiddle hrel hgir hresults hgenerated) fun value after pt' fr' hdone P => ?_
  have hvalue := (child.result n value hdone).typed
  rw [htype] at hvalue
  obtain ⟨location, start, length, rfl, hslice⟩ := hvalue
  simp only [Core.expectSlice, pure_bind]
  have hcell := P.has (id, .val (.slice location start length)) (by simp)
  apply SimEAt.of_simG
  refine leaf_def P hview hext (by simp) RVal.view ?_
  simp only [execPure, getVal_of hcell, Core.expectSlice, pure_bind, bind_assoc]

theorem typedExprClaim_len {n : Nat} {cfg : Cfg} {results : List Ty} {view : View}
    (hv : TypedViewClaim n cfg results view) : TypedExprClaim (n + 1) cfg results (.len view) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots, _, _⟩ := source.lenChild
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨id, middle, hview, hlen⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitDef hlen)
  simp only [evalExpr]
  refine SimEAt.bind (hv env state child hchildMetadata ls middle id pt cx fr hview hpp
    hextMiddle hrel hgir hresults hgenerated) fun value after pt' fr' hdone P => ?_
  have hcell := P.has (id, .view value) (by simp)
  apply SimEAt.of_simG
  refine leaf_def P hlen hext (by simp) RVal.val ?_
  simp only [execPure, getView_of hcell, pure_bind]

theorem typedExprClaim_slice {n : Nat} {cfg : Cfg} {results : List Ty} {view : View} {low high : Bound}
    (hv : TypedViewClaim n cfg results view) (hl : TypedBoundClaim n cfg results low)
    (hh : TypedBoundClaim n cfg results high) (mutability : Mutability) (origin : OriginId) :
    TypedExprClaim (n + 1) cfg results (.slice mutability view low high origin) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨sampled, htyping, hroots, _, next⟩ := source.sliceChildren mutability origin
  have hviewMetadata : SourceResults sampled.typingEnv sampled.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨rv, first, hview, bl, second, hlower, bh, third, hupper, hdef⟩ := hlow
  have hextThird : ExtT third cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  have hextSecond := hextThird.of_adv (advB_lowerBound high _ _ _ _ hupper)
  have hextFirst := hextSecond.of_adv (advB_lowerBound low _ _ _ _ hlower)
  simp only [evalExpr]
  refine SimEAt.bind (hv env state sampled hviewMetadata ls first rv pt cx fr hview hpp hextFirst
    hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P1 => ?_
  obtain ⟨lower, hltyping, hlroots, _, nextLow⟩ := next n value after hdone
  have hlmetadata : SourceResults lower.typingEnv lower.rootsEnv results := by
    rw [hltyping, hlroots]
    exact hmetadata
  refine SimEAt.bind (hl env after lower hlmetadata first second bl pt1 cx fr1 value.len 0
    hlower P1.pp hextSecond P1.rel hgir hresults (hgenerated.lowerView view hview)) fun lo after2 pt2 fr2 hdone2 ⟨cl, hsl, P2⟩ => ?_
  obtain ⟨upper, hhtyping, hhroots, _⟩ := nextLow n lo after2 hdone2
  have hhmetadata : SourceResults upper.typingEnv upper.rootsEnv results := by
    rw [hhtyping, hhroots]
    exact hmetadata
  refine SimEAt.bind (hh env after2 upper hhmetadata second third bh pt2 cx fr2 value.len value.len
    hupper P2.pp hextThird P2.rel hgir hresults ((hgenerated.lowerView view hview).lowerBound low hlower)) fun hi after3 pt3 fr3 hdone3 ⟨ch, hsh, P3⟩ => ?_
  have P123 := (P1.comp P2).comp P3
  have hviewCell := P123.has (rv, .view value) (by simp)
  have hcl : ∀ p ∈ cl, fr3.vals[p.1]? = some p.2 := fun p hp => P123.has p (by simp [hp])
  have hch : ∀ p ∈ ch, fr3.vals[p.1]? = some p.2 := fun p hp => P123.has p (by simp [hp])
  have elow := evalBnd_of_spec hsl hcl
  have ehigh := evalBnd_of_spec hsh hch
  apply SimEAt.of_simG
  refine leaf_def P123 hdef hext (by simp) RVal.val ?_
  simp only [execPure, getView_of hviewCell, elow, ehigh, bind_assoc, pure_bind]
  by_cases hbound : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ (value.len : Int)
  · simp [hbound]
  · simp [hbound, abortAtOrg, abortAt, M.stop, bind_apply]
    rfl

theorem typedExprClaim_lit (n : Nat) (cfg : Cfg) (results : List Ty) (ty : IntTy) (value : Int) :
    TypedExprClaim n cfg results (.lit ty value) := by
  cases n with
  | zero => exact typedExprClaim_zero _ _ _
  | succ n =>
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
    simp only [lowerExpr] at hlow
    simp only [evalExpr]
    exact SimEAt.of_simG (leaf_def (Post.init hrel hpp) hlow hext (by simp) RVal.val
      (by simp [execPure])) state

theorem typedExprClaim_bool (n : Nat) (cfg : Cfg) (results : List Ty) (value : Bool) :
    TypedExprClaim n cfg results (.bool value) := by
  cases n with
  | zero => exact typedExprClaim_zero _ _ _
  | succ n =>
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
    simp only [lowerExpr] at hlow
    simp only [evalExpr]
    exact SimEAt.of_simG (leaf_def (Post.init hrel hpp) hlow hext (by simp) RVal.val
      (by simp [execPure])) state

theorem typedExprClaim_not {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedExprClaim (n + 1) cfg results (.not expr) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots, hbool, _⟩ := source.notChild
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, middle, hchild, hdef⟩ := hlow
  have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimEAt.bind (he env state child hchildMetadata ls middle x pt cx fr hchild hpp
    hextMiddle hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P => ?_
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
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots, _⟩ := source.readChild
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨id, middle, hchild, hread⟩ := hlow
  rcases hread with ⟨value, afterLoad, hload, unitResult, afterRecord, hrecord, hreturn⟩
  cases unitResult
  rw [pure_run] at hreturn
  rcases Prod.mk.inj hreturn with ⟨rfl, rfl⟩
  have hadvRecord : afterLoad.Adv afterRecord :=
    advB_recordReadValueRootRecipe value place (lowerEnv cfg.mod env.vars results)
      afterLoad () afterRecord hrecord
  have hextMiddle : ExtT middle cx.fn.blocks :=
    hext.of_adv ((adv_emitDef hload).trans hadvRecord)
  have hextAfterLoad : ExtT afterLoad cx.fn.blocks := hext.of_adv hadvRecord
  simp only [evalExpr]
  refine SimEAt.bind (hp env state child hchildMetadata ls middle id pt cx fr hchild hpp
    hextMiddle hrel hgir hresults hgenerated) fun location after pt1 fr1 hdone P => ?_
  have hx := P.has (id, .val (.ref location)) (by simp)
  apply SimEAt.of_simG
  refine SimG.mono (leaf_def P hload hextAfterLoad (by simp) RVal.val ?_) ?_
  · simp only [execPure, getVal_of hx, Goose.Core.expectRef, pure_bind]
  · intro result pt' fr' post
    exact Post.recordReadValueRootRecipe post hrecord

theorem typedExprClaim_ref {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) (mutability : Mutability) :
    TypedExprClaim (n + 1) cfg results (.ref mutability place) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots⟩ := source.refChild mutability
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨id, middle, hchild, hfreeze⟩ := hlow
  rcases borrowTo_ref_cases hfreeze with ⟨rfl, rfl⟩ | hfreeze | hfreeze
  · simp only [evalExpr]
    refine SimEAt.bind (hp env state child hchildMetadata ls ls' r pt cx fr hchild hpp
      hext hrel hgir hresults hgenerated) fun location after pt1 fr1 hdone P => ?_
    exact SimEAt.ret P
  all_goals
    have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hfreeze)
    simp only [evalExpr]
    refine SimEAt.bind (hp env state child hchildMetadata ls middle id pt cx fr hchild hpp
      hextMiddle hrel hgir hresults hgenerated) fun location after pt1 fr1 hdone P => ?_
    have hx := P.has (id, .val (.ref location)) (by simp)
    apply SimEAt.of_simG
    exact leaf_def P hfreeze hext (by simp) RVal.val
      (by simp only [execPure, getVal_of hx, Goose.Core.expectRef, pure_bind])

theorem typedExprClaim_bin {n : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (ha : TypedExprClaim n cfg results a) (hb : TypedExprClaim n cfg results b)
    (op : BinOp) (origin : OriginId) : TypedExprClaim (n + 1) cfg results (.bin op a b origin) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨intTy, left, htyping, hroots, htype, _, next⟩ := source.binChildren op origin
  have hleftMetadata : SourceResults left.typingEnv left.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, first, hfirst, y, middle, hsecond, actualTy, same, hty, hdef⟩ := hlow
  have hsame := intTyOf_eq hty
  subst hsame
  have hextMiddle : ExtT same cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  have hextFirst : ExtT first cx.fn.blocks := hextMiddle.of_adv (advB_lowerExpr b _ _ _ _ hsecond)
  simp only [evalExpr]
  refine SimEAt.bind (ha env state left hleftMetadata ls first x pt cx fr hfirst hpp
    hextFirst hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P1 => ?_
  have hvalue := (left.result n value hdone).typed
  rw [htype] at hvalue
  obtain ⟨integer, rfl⟩ := Core.Sound.hasTy_int hvalue
  simp only [Goose.Core.expectInt, pure_bind]
  obtain ⟨right, htypingRight, hrootsRight, htypeRight, _⟩ := next n (.int intTy integer) after hdone
  have hrightMetadata : SourceResults right.typingEnv right.rootsEnv results := by
    rw [htypingRight, hrootsRight]
    exact hmetadata
  refine SimEAt.bind (hb env after right hrightMetadata first same y pt1 cx fr1 hsecond P1.pp
    hextMiddle P1.rel hgir hresults (hgenerated.lowerExpr a hfirst)) fun value2 after2 pt2 fr2 hdone2 P2 => ?_
  have hvalue2 := (right.result n value2 hdone2).typed
  rw [htypeRight] at hvalue2
  obtain ⟨integer2, rfl⟩ := Core.Sound.hasTy_int hvalue2
  simp only [Goose.Core.expectInt, Goose.Core.expectSameTy, ite_true, pure_bind]
  have P12 := P1.comp P2
  have hx := P12.has (x, .val (.int intTy integer)) (by simp)
  have hy := P12.has (y, .val (.int intTy integer2)) (by simp)
  apply SimEAt.of_simG
  exact leaf_def P12 hdef hext (by simp) RVal.val (execPure_bin P2.rel.prof hx hy)

theorem typed_shortCircuit_sim {isAnd : Bool} {x : ValueId} {rhs : B ValueId} {le : LEnv} {ls1 : LS} {r : ValueId}
    {ls' : LS} {pt1 : Pt} {cfg : Cfg} {env : Env} {cx : FnCtx} {fr1 : Frame} {cb : M Val} {β : Bool} {state : St}
    (hs : shortCircuit isAnd x rhs le ls1 = (r, ls')) (hpp : ls1.pp = some pt1)
    (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr1 ls1)
    (hx : fr1.vals[x]? = some (.val (.bool β))) (hadv : AdvB rhs)
    (hgenerated : GeneratedBuilderState ls1)
    (hrhs : ∀ (ls_d : LS) (y : ValueId) (ls_e : LS) (pt_d : Pt), rhs le ls_d = (y, ls_e) →
      ls_d.pp = some pt_d → ExtT ls_e cx.fn.blocks → Rel cfg env cx fr1 ls_d →
      GeneratedBuilderState ls_d → SimEAt cx pt_d fr1 cb (fun vb pt' fr' => Post cfg env cx ls_d fr1 ls_e fr' pt' [(y, .val vb)]) state) :
    SimEAt cx pt1 fr1 (if isAnd then
      if β then cb >>= fun v => expectBool v >>= fun b => pure (.bool b) else pure (.bool false)
      else if β then pure (.bool true) else cb >>= fun v => expectBool v >>= fun b => pure (.bool b)) (fun v pt' fr' => Post cfg env cx ls1 fr1 ls' fr' pt' [(r, .val v)]) state := by
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some hpp
  unfold shortCircuit at hs
  rw [whenLive_some _ _ _ hc1] at hs
  simp only [bind_eq] at hs
  obtain ⟨⟨rb, jb, p⟩, ls_c, h1, u2, ls_d, h2, y, ls_e, h3, u4, ls_f, h4, u5, ls_g, h5, hpure⟩ := hs
  rw [pure_run] at hpure
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpure
  have a_rhs : ls_d.Adv ls_e := hadv _ _ _ _ h3
  have a_f := adv_emitTerm h4
  have hg : ls_g = { ls_f with cur := some jb } := by
    rw [setCur_run] at h5; exact (Prod.mk.inj h5).2.symm
  have hd : ls_d = { ls_c with cur := some rb } := by
    rw [setCur_run] at h2; exact (Prod.mk.inj h2).2.symm
  have hext_f : ExtT ls_f cx.fn.blocks := by rw [hg] at hext; exact hext
  have hext_e : ExtT ls_e cx.fn.blocks := hext_f.of_adv a_f
  have hext_d : ExtT ls_d cx.fn.blocks := hext_e.of_adv a_rhs
  have hext_c : ExtT ls_c cx.fn.blocks := by rw [hd] at hext_d; exact hext_d
  obtain ⟨hrb, hjb, hpv, hvc, hstc, hcurc, hinst, hbrb, hbjb⟩ := scFork_facts h1 hpp hext_c
  obtain ⟨-, hszc⟩ := scFork_ids h1
  subst hrb hjb hpv
  obtain ⟨Trb, hTrb, hTrbp⟩ := hext_c.params hbrb
  obtain ⟨Tjb, hTjb, hTjbp⟩ := hext_c.params hbjb
  have hdb : ls_d.blocks = ls_c.blocks := by rw [hd]
  have hdpp : ls_d.pp = some (ls1.blocks.size, 0) := by
    rw [hd]; exact LS.pp_cur hbrb
  have hstd : ls_d.stack = ls1.stack := by rw [hd]; exact hstc
  have hrel_d : Rel cfg env cx fr1 ls_d := hrel.stack_eq hstd
  have hvd : ls_d.vals.size = ls1.vals.size + 1 := by rw [hd]; exact hvc
  have hjb_d : ls_d.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    rw [hdb]; exact hbjb
  have hjb_e : ls_e.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    refine a_rhs.keep _ _ ?_ hjb_d
    rw [hd]
    intro hh
    have := Option.some.inj hh
    nat_omega
  have hjb_f : ls_f.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    cases hce : ls_e.cur with
    | none =>
      rw [emitTerm_none _ _ hce] at h4
      obtain ⟨-, rfl⟩ := Prod.mk.inj h4
      exact hjb_e
    | some be =>
      rw [emitTerm_run _ _ hce] at h4
      obtain ⟨-, rfl⟩ := Prod.mk.inj h4
      have hbe : be ≠ ls1.blocks.size + 1 := by
        rcases a_rhs.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [hce] at h; cases h
        · rw [hce, hd] at h
          have := Option.some.inj h
          have hszd : ls_d.blocks.size = ls1.blocks.size + 2 := by rw [hdb]; exact hszc
          nat_omega
        · rw [hce] at hc
          have := Option.some.inj hc
          have hszd : ls_d.blocks.size = ls1.blocks.size + 2 := by rw [hdb]; exact hszc
          nat_omega
      show (ls_e.blocks.modify be _)[ls1.blocks.size + 1]? = _
      rw [getElem?_modify_ne hbe]
      exact hjb_e
  have hpp_g : ls_g.pp = some (ls1.blocks.size + 1, 0) := by
    rw [hg]; exact LS.pp_cur hjb_f
  have hst_g : ls_g.stack = ls1.stack := by
    rw [hg]
    show ls_f.stack = _
    rw [a_f.stack, a_rhs.stack, hstd]
  have hv_g : ls1.vals.size + 1 ≤ ls_g.vals.size := by
    rw [hg]
    show _ ≤ ls_f.vals.size
    have := a_f.vals; have := a_rhs.vals
    nat_omega
  have hmono : ls1.vals.size ≤ ls_g.vals.size := Nat.le_trans (Nat.le_succ _) hv_g
  have hlt : ls1.vals.size < ls_g.vals.size := hv_g
  have hTrb' : cx.fn.blocks[ls1.blocks.size]? = some Trb := hTrb
  have hTjb' : cx.fn.blocks[ls1.blocks.size + 1]? = some Tjb := hTjb
  have hjoin : ∀ (vb : Val) (pt_e : Pt) (fr_e : Frame),
      Post cfg env cx ls_d fr1 ls_e fr_e pt_e [(y, .val vb)] → ∀ bb, vb = .bool bb →
      SimG cx pt_e fr_e (pure (Val.bool bb) : M Val) (fun v pt' fr' =>
        Post cfg env cx ls1 fr1 ls_g fr' pt' [(ls1.vals.size, .val v)]) := by
    intro vb pt_e fr_e P bb hvb
    subst hvb
    obtain ⟨-, -, -, hinst_e⟩ := emitTerm_facts h4 P.pp hext_f
    have hy : fr_e.vals[y]? = some (.val (.bool bb)) := P.has (y, _) (by simp)
    have g2 := goes_br1 (cx := cx) (pt := pt_e) (fr := fr_e) hinst_e hTjb' hTjbp hy
    refine SimG.goes g2 (SimG.ret ?_)
    have hsame : Same ls1.vals.size fr1 fr_e := P.same.mono (by nat_omega)
    have hrel_e : Rel cfg env cx fr_e ls1 := P.rel.stack_eq (by rw [a_rhs.stack, hstd])
    exact Post.join hsame hrel_e (Nat.le_refl _) hlt hmono hst_g hpp_g
  have hshort : ∀ b' : Bool, Goes cx pt1 fr1 (ls1.blocks.size + 1, 0)
      (fr1.set ls1.vals.size (.val (.bool b'))) →
      SimG cx pt1 fr1 (pure (Val.bool b') : M Val) (fun v pt' fr' =>
        Post cfg env cx ls1 fr1 ls_g fr' pt' [(ls1.vals.size, .val v)]) := by
    intro b' hg'
    refine SimG.goes hg' (SimG.ret ?_)
    exact Post.join (Same.refl _ _) hrel (Nat.le_refl _) hlt hmono hst_g hpp_g
  have generatedC := hgenerated.scFork isAnd x h1
  have generatedD := generatedC.setCur (some ls1.blocks.size)
    (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp hbrb).1) h2
  have hrhs' := hrhs ls_d y ls_e (ls1.blocks.size, 0) h3 hdpp hext_e hrel_d generatedD
  cases isAnd <;> cases β
  · -- or, false: the right operand
    have hi : instAt cx.fn pt1 = some (.term (.condbr x (ls1.blocks.size + 1) [x] ls1.blocks.size [])) := hinst
    refine SimEAt.goes (goes_condbr_else0 hi hx hTrb' hTrbp rfl) ?_
    exact SimEAt.bind hrhs' fun vb after pt_e fr_e hdone P =>
      SimEAt.of_simG (SimG.expectBool fun bb hvb => hjoin vb pt_e fr_e P bb hvb) after
  · -- or, true: the join directly
    have hi : instAt cx.fn pt1 = some (.term (.condbr x (ls1.blocks.size + 1) [x] ls1.blocks.size [])) := hinst
    exact SimEAt.of_simG (hshort true (goes_condbr_then1 hi hx hTjb' hTjbp rfl hx)) state
  · -- and, false: the join directly
    have hi : instAt cx.fn pt1 = some (.term (.condbr x ls1.blocks.size [] (ls1.blocks.size + 1) [x])) := hinst
    exact SimEAt.of_simG (hshort false (goes_condbr_else1 hi hx hTjb' hTjbp rfl hx)) state
  · -- and, true: the right operand
    have hi : instAt cx.fn pt1 = some (.term (.condbr x ls1.blocks.size [] (ls1.blocks.size + 1) [x])) := hinst
    refine SimEAt.goes (goes_condbr_then0 hi hx hTrb' hTrbp rfl) ?_
    exact SimEAt.bind hrhs' fun vb after pt_e fr_e hdone P =>
      SimEAt.of_simG (SimG.expectBool fun bb hvb => hjoin vb pt_e fr_e P bb hvb) after


private theorem typedExprClaim_shortCircuit {n : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (ha : TypedExprClaim n cfg results a) (hb : TypedExprClaim n cfg results b) (isAnd : Bool) :
    TypedExprClaim (n + 1) cfg results (if isAnd then .and a b else .or a b) := by
  cases isAnd
  all_goals (
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
    obtain ⟨left, htyping, hroots, htype, next⟩ := source.shortCircuitChildren _
    have hleftMetadata : SourceResults left.typingEnv left.rootsEnv results := by
      rw [htyping, hroots]
      exact hmetadata
    simp only [Bool.false_eq_true, ite_false, ite_true, lowerExpr, bind_eq] at hlow
    obtain ⟨x, first, hfirst, hsc⟩ := hlow
    have hadv := advB_lowerExpr b
    have hextFirst : ExtT first cx.fn.blocks :=
      hext.of_adv (advB_shortCircuit _ x hadv _ _ _ _ hsc)
    simp only [Bool.false_eq_true, ite_false, ite_true, evalExpr]
    refine SimEAt.bind (ha env state left hleftMetadata ls first x pt cx fr hfirst hpp
      hextFirst hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P1 => ?_
    have hvalue := (left.result n value hdone).typed
    rw [htype] at hvalue
    obtain ⟨boolean, rfl⟩ := Core.Sound.hasTy_bool hvalue
    simp only [Goose.Core.expectBool, pure_bind]
    obtain ⟨right, htypingRight, hrootsRight, htypeRight⟩ := next n (.bool boolean) after hdone
    have hrightMetadata : SourceResults right.typingEnv right.rootsEnv results := by
      rw [htypingRight, hrootsRight]
      exact hmetadata
    have hx := P1.has (x, .val (.bool boolean)) (by simp)
    refine SimEAt.mono (typed_shortCircuit_sim (cb := evalExpr n cfg env b) hsc P1.pp hext
      P1.rel hx hadv (hgenerated.lowerExpr a hfirst) ?_) fun v after2 pt' fr' done P => ?_
    · intro ls_d y ls_e pt_d h3 hpp_d hext_e hrel_d generatedD
      exact hb env after right hrightMetadata ls_d ls_e y pt_d cx fr1 h3 hpp_d hext_e
        hrel_d hgir hresults generatedD
    · exact (P1.comp P).sub (by simp)
  )

theorem typedExprClaim_and {n : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (ha : TypedExprClaim n cfg results a) (hb : TypedExprClaim n cfg results b) :
    TypedExprClaim (n + 1) cfg results (.and a b) := typedExprClaim_shortCircuit ha hb true

theorem typedExprClaim_or {n : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (ha : TypedExprClaim n cfg results a) (hb : TypedExprClaim n cfg results b) :
    TypedExprClaim (n + 1) cfg results (.or a b) := typedExprClaim_shortCircuit ha hb false

theorem typedExprClaim_cmp {n : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (ha : TypedExprClaim n cfg results a) (hb : TypedExprClaim n cfg results b)
    (op : CmpOp) : TypedExprClaim (n + 1) cfg results (.cmp op a b) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨left, htyping, hroots, _, next⟩ := source.cmpChildren op
  have hleftMetadata : SourceResults left.typingEnv left.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, first, hfirst, y, middle, hsecond, actualTy, same, hty, hdef⟩ := hlow
  have hsame := valTy_eq hty
  subst hsame
  have step : ∃ instruction, emitDef instruction (lowerEnv cfg.mod env.vars results) same = (r, ls') ∧
      (instruction = .boolCmp op x y ∨ ∃ t, instruction = .cmp op t x y) := by
    cases actualTy with
    | data t =>
      cases t <;> first
        | exact ⟨_, hdef, Or.inr ⟨_, rfl⟩⟩
        | exact ⟨_, hdef, Or.inl rfl⟩
    | view _ _ => exact ⟨_, hdef, Or.inl rfl⟩
  obtain ⟨instruction, hstep, hkind⟩ := step
  have hextMiddle : ExtT same cx.fn.blocks := hext.of_adv (adv_emitDef hstep)
  have hextFirst : ExtT first cx.fn.blocks := hextMiddle.of_adv (advB_lowerExpr b _ _ _ _ hsecond)
  simp only [evalExpr]
  refine SimEAt.bind (ha env state left hleftMetadata ls first x pt cx fr hfirst hpp
    hextFirst hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P1 => ?_
  obtain ⟨right, htypingRight, hrootsRight, _⟩ := next n value after hdone
  have hrightMetadata : SourceResults right.typingEnv right.rootsEnv results := by
    rw [htypingRight, hrootsRight]
    exact hmetadata
  refine SimEAt.bind (hb env after right hrightMetadata first same y pt1 cx fr1 hsecond P1.pp
    hextMiddle P1.rel hgir hresults (hgenerated.lowerExpr a hfirst)) fun value2 after2 pt2 fr2 hdone2 P2 => ?_
  have P12 := P1.comp P2
  have hx := P12.has (x, .val value) (by simp)
  have hy := P12.has (y, .val value2) (by simp)
  have hnc : ∀ f args origin, instruction ≠ .call f args origin := by
    rcases hkind with rfl | ⟨t, rfl⟩ <;> simp
  apply SimEAt.of_simG
  refine leaf_def P12 hstep hext hnc RVal.val ?_
  rcases hkind with rfl | ⟨t, rfl⟩
  · exact (execPure_cmp hx hy).2
  · exact (execPure_cmp hx hy).1 t

theorem typedExprClaim_un {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) (op : UnOp) (origin : OriginId) :
    TypedExprClaim (n + 1) cfg results (.un op expr origin) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots, intTy, htype, _⟩ := source.unChild op origin
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨id, middle, hchild, actualTy, same, hty, hdef⟩ := hlow
  have hsame := intTyOf_eq hty
  subst hsame
  have hextMiddle : ExtT same cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimEAt.bind (he env state child hchildMetadata ls same id pt cx fr hchild hpp
    hextMiddle hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P => ?_
  have hvalue := (child.result n value hdone).typed
  rw [htype] at hvalue
  obtain ⟨integer, rfl⟩ := Core.Sound.hasTy_int hvalue
  simp only [Goose.Core.expectInt, pure_bind]
  have hx := P.has (id, .val (.int intTy integer)) (by simp)
  apply SimEAt.of_simG
  exact leaf_def P hdef hext (by simp) RVal.val (execPure_un P.rel.prof hx)

theorem typedExprClaim_push {n : Nat} {cfg : Cfg} {results : List Ty} {owner : Place} {argument : Expr}
    (hp : TypedPlaceClaim n cfg results owner) (ha : TypedExprClaim n cfg results argument)
    (origin : Option OriginId) : TypedExprClaim (n + 1) cfg results (.push owner argument origin) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨left, htyping, hroots, next⟩ := source.pushChildren origin
  have hleftMetadata : SourceResults left.typingEnv left.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨address, first, howner, id, middle, hargument, hdef⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitDef hdef)
  have hextFirst := hextMiddle.of_adv (advB_lowerExpr argument _ _ _ _ hargument)
  simp only [evalExpr]
  refine SimEAt.bind (hp env state left hleftMetadata ls first address pt cx fr howner hpp
    hextFirst hrel hgir hresults hgenerated) fun location after pt1 fr1 hdone P1 => ?_
  obtain ⟨right, htypingRight, hrootsRight⟩ := next n location after hdone
  have hrightMetadata : SourceResults right.typingEnv right.rootsEnv results := by
    rw [htypingRight, hrootsRight]
    exact hmetadata
  refine SimEAt.bind (ha env after right hrightMetadata first middle id pt1 cx fr1 hargument P1.pp
    hextMiddle P1.rel hgir hresults (hgenerated.lowerPlace owner howner)) fun value after2 pt2 fr2 hdone2 P2 => ?_
  have P12 := P1.comp P2
  have hownerCell := P12.has (address, .val (.ref location)) (by simp)
  have hvalueCell := P12.has (id, .val value) (by simp)
  apply SimEAt.of_simG
  refine leaf_def P12 hdef hext (by simp) RVal.val ?_
  cases origin with
  | none => simp [execPure, getVal_of hownerCell, getVal_of hvalueCell, Core.expectRef]
  | some origin =>
    simp [execPure, getVal_of hownerCell, getVal_of hvalueCell, Core.expectRef, bind_assoc, pure_bind,
      checkCapacityAtOrg, Core.checkedAppendLoc, checkAppendCapacity, abortAtOrg, abortAt]
    rfl

theorem typedExprClaim_pop {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) (origin : OriginId) :
    TypedExprClaim (n + 1) cfg results (.pop place origin) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots⟩ := source.popChild origin
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨address, middle, hplace, hpop⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitDef hpop)
  simp only [evalExpr]
  refine SimEAt.bind (hp env state child hchildMetadata ls middle address pt cx fr hplace hpp
    hextMiddle hrel hgir hresults hgenerated) fun location after pt' fr' hdone P => ?_
  have hcell := P.has (address, .val (.ref location)) (by simp)
  apply SimEAt.of_simG
  refine leaf_def P hpop hext (by simp) RVal.val ?_
  simp [execPure, getVal_of hcell, Core.expectRef, abortAtOrg, abortAt]
  funext state
  cases hlen : lengthLoc location state with
  | stop err final => simp [bind_apply, hlen]
  | ok length middle =>
    by_cases hzero : length = 0
    · simp [bind_apply, hlen, hzero, Functor.map, M.stop, M.bind', M.pure']
    · simp only [bind_apply, hlen, if_neg hzero]
      cases hread : readLoc { root := location.root, path := location.path ++ [length - 1] } middle with
      | stop err final => simp [bind_apply, hread]
      | ok value afterRead =>
        cases htruncate : truncateLoc location (length - 1) afterRead with
        | stop err final => simp [bind_apply, hread, htruncate]
        | ok _ final => simp [bind_apply, hread, htruncate]

theorem typedExprClaim_fill {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) (target : Ty) :
    TypedExprClaim (n + 1) cfg results (.fill target expr) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨element, count, htarget, child, htyping, hroots, htype, _⟩ := source.fillChild target
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  subst target
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨id, middle, hchild, hdef⟩ := hlow
  have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  simp only [evalExpr, Goose.Core.expectFixedCount, pure_bind]
  refine SimEAt.bind (he env state child hchildMetadata ls middle id pt cx fr hchild hpp
    hextMiddle hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P => ?_
  have hx := P.has (id, .val value) (by simp)
  apply SimEAt.of_simG
  refine leaf_def P hdef hext (by simp) RVal.val ?_
  simp only [execPure, getVal_of hx, Goose.Core.expectFixedCount, pure_bind, bind_assoc]

theorem typedExprClaim_conv {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) (kind : ConvKind) (target : Ty) (origin : OriginId) :
    TypedExprClaim (n + 1) cfg results (.conv kind target expr origin) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots, intTy, targetInt, htype, htarget, _⟩ := source.convChild kind target origin
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  subst target
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨id, middle, hchild, actualTy, same, hty, hdef⟩ := hlow
  have hsame := intTyOf_eq hty
  subst hsame
  have hextMiddle : ExtT same cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimEAt.bind (he env state child hchildMetadata ls same id pt cx fr hchild hpp
    hextMiddle hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P => ?_
  have hvalue := (child.result n value hdone).typed
  rw [htype] at hvalue
  obtain ⟨integer, rfl⟩ := Core.Sound.hasTy_int hvalue
  simp only [Goose.Core.expectInt, Goose.Core.expectIntTy, pure_bind]
  have hx := P.has (id, .val (.int intTy integer)) (by simp)
  apply SimEAt.of_simG
  exact leaf_def P hdef hext (by simp) RVal.val (execPure_conv P.rel.prof hx)

theorem typedPlaceClaim_var (n : Nat) (cfg : Cfg) (results : List Ty) (id : VarId) :
    TypedPlaceClaim n cfg results (.var id) := by
  cases n with
  | zero => exact typedPlaceClaim_zero _ _ _
  | succ n =>
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
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
    intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
    simp only [lowerPlace] at hlow
    simp only [evalPlace]
    exact SimEAt.of_simG (leaf_def (Post.init hrel hpp) hlow hext (by simp)
      (fun location => RVal.val (.ref location)) (by simp [execPure])) state

theorem typedPlace_deref_sim {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) (env : Env) (state : St)
    (source : PlaceSource cfg env (.deref expr) state)
    (hnormal : sliceRefTy source.typingEnv expr = none)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerPlace (.deref expr) (lowerEnv cfg.mod env.vars results) ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results)
    (hgenerated : GeneratedBuilderState ls) :
    SimEAt cx pt fr (evalPlace (n + 1) cfg env (.deref expr))
      (fun location pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val (.ref location))]) state := by
  obtain ⟨child, htyping, hroots, mutability, target, htype⟩ := source.derefChild hnormal
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerPlace] at hlow
  simp only [evalPlace]
  refine SimEAt.bind (he env state child hchildMetadata ls ls' r pt cx fr hlow hpp
    hext hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P => ?_
  have hvalue := (child.result n value hdone).typed
  rw [htype] at hvalue
  obtain ⟨location, rfl, _⟩ := hvalue
  simp only [Goose.Core.expectRef]
  exact SimEAt.ret P

theorem read_var_sim (n : Nat) (cfg : Cfg) (results : List Ty) (env : Env) (id : VarId)
    (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerExpr (.read (.var id)) (lowerEnv cfg.mod env.vars results) ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (evalExpr n cfg env (.read (.var id)))
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) := by
  cases n with
  | zero => simp only [evalExpr]; exact SimG.of_timeout
  | succ n =>
    simp only [lowerExpr, bind_eq] at hlow
    obtain ⟨address, middle, hplace, hread⟩ := hlow
    rcases hread with ⟨value, afterLoad, hload, unitResult, afterRecord, hrecord, hreturn⟩
    cases unitResult
    rw [pure_run] at hreturn
    rcases Prod.mk.inj hreturn with ⟨rfl, rfl⟩
    have hadvRecord : afterLoad.Adv afterRecord :=
      advB_recordReadValueRootRecipe value (.var id) (lowerEnv cfg.mod env.vars results)
        afterLoad () afterRecord hrecord
    have hextMiddle : ExtT middle cx.fn.blocks :=
      hext.of_adv ((adv_emitDef hload).trans hadvRecord)
    have hextAfterLoad : ExtT afterLoad cx.fn.blocks := hext.of_adv hadvRecord
    have hs : SimG cx pt fr (evalPlace n cfg env (.var id))
        (fun location pt' fr' =>
          Post cfg env cx ls fr middle fr' pt' [(address, .val (.ref location))]) := by
      cases n with
      | zero => simp only [evalPlace]; exact SimG.of_timeout
      | succ n =>
        simp only [lowerPlace] at hplace
        simp only [evalPlace]
        exact leaf_def (Post.init hrel hpp) hplace hextMiddle (by simp)
          (fun location => RVal.val (.ref location))
          (by simp only [execPure, slotRoot_eq hrel id, bind_assoc, pure_bind])
    simp only [evalExpr]
    refine SimG.bind hs fun location pt1 fr1 P => ?_
    have hx := P.has (address, .val (.ref location)) (by simp)
    refine SimG.mono (leaf_def P hload hextAfterLoad (by simp) RVal.val ?_) ?_
    · simp only [execPure, getVal_of hx, Goose.Core.expectRef, pure_bind]
    · intro value pt' fr' post
      exact Post.recordReadValueRootRecipe post hrecord

open Core.Sound in
theorem typedPlaceClaim_deref {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedPlaceClaim (n + 1) cfg results (.deref expr) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  cases hslice : sliceRefTy source.typingEnv expr with
  | none =>
    exact typedPlace_deref_sim he env state source hslice hmetadata
      ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  | some ty =>
    obtain ⟨id, localDecl, mu0, mu, element, rfl, hvisible, hvariable, htype, hflat, hty⟩ :=
      sliceRefTy_some hslice
    have hfuture : id ∈ source.context.inputFuture := by
      cases hc : source.context <;> simp [hc, EvaluationContext.inputFuture,
        NodeContext.inputFuture, DemandNode.variables, Place.variables, Expr.variables]
    have hs : Sat (evalExpr n cfg env (.read (.var id))) state
        (fun value _ => ∃ location, value = .ref location) := by
      apply sat_read_var source.frame hvisible hfuture n
      intro actual scopeInst value hat _ _ hvalue
      rw [source.frame.vars_t, hat] at hvariable
      cases hvariable
      rw [htype] at hvalue
      obtain ⟨location, rfl, _⟩ := hvalue
      exact ⟨location, rfl⟩
    simp only [lowerPlace] at hlow
    simp only [evalPlace]
    refine SimEAt.bind (SimEAt.of_simG (read_var_sim n cfg results env id ls ls' r pt cx fr
      hlow hpp hext hrel) state) fun value after pt1 fr1 hdone P => ?_
    unfold Sat at hs
    rw [hdone] at hs
    obtain ⟨location, rfl⟩ := hs
    simp only [Goose.Core.expectRef]
    exact SimEAt.ret P

theorem typedPlaceClaim_elem {n : Nat} {cfg : Cfg} {results : List Ty} {view : View} {index : Expr}
    (hv : TypedViewClaim n cfg results view) (hi : TypedExprClaim n cfg results index)
    (origin : OriginId) : TypedPlaceClaim (n + 1) cfg results (.elem view index origin) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨intTy, left, htyping, hroots, _, next⟩ := source.elemChildren origin
  have hleftMetadata : SourceResults left.typingEnv left.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerPlace, bind_eq] at hlow
  obtain ⟨vw, first, hfirst, iv, middle, hsecond, hdef⟩ := hlow
  have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  have hextFirst : ExtT first cx.fn.blocks := hextMiddle.of_adv (advB_lowerExpr index _ _ _ _ hsecond)
  simp only [evalPlace]
  refine SimEAt.bind (hv env state left hleftMetadata ls first vw pt cx fr hfirst hpp
    hextFirst hrel hgir hresults hgenerated) fun value after pt1 fr1 hdone P1 => ?_
  obtain ⟨right, htypingRight, hrootsRight, htype, _⟩ := next n value after hdone
  have hrightMetadata : SourceResults right.typingEnv right.rootsEnv results := by
    rw [htypingRight, hrootsRight]
    exact hmetadata
  refine SimEAt.bind (hi env after right hrightMetadata first middle iv pt1 cx fr1 hsecond P1.pp
    hextMiddle P1.rel hgir hresults (hgenerated.lowerView view hfirst)) fun value2 after2 pt2 fr2 hdone2 P2 => ?_
  have hvalue := (right.result n value2 hdone2).typed
  rw [htype] at hvalue
  obtain ⟨integer, rfl⟩ := Core.Sound.hasTy_int hvalue
  simp only [Core.expectInt, pure_bind]
  have P12 := P1.comp P2
  have hview := P12.has (vw, .view value) (by simp)
  have hindex := P12.has (iv, .val (.int intTy integer)) (by simp)
  apply SimEAt.of_simG
  refine leaf_def P12 hdef hext (by simp) (fun location => RVal.val (.ref location)) ?_
  simp only [execPure, getView_of hview, getVal_of hindex, Core.expectInt, bind_assoc, pure_bind]
  by_cases hbound : 0 ≤ integer ∧ integer < (value.len : Int)
  · simp [hbound]
  · simp [hbound, abortAtOrg, abortAt, M.stop, bind_apply]
    rfl

theorem typedPlaceClaim_field {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) (index : Nat) :
    TypedPlaceClaim (n + 1) cfg results (.field place index) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots, _, _⟩ := source.fieldChild index
  have hchildMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  simp only [lowerPlace, bind_eq] at hlow
  obtain ⟨address, middle, hplace, hfield⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitDef hfield)
  simp only [evalPlace]
  refine SimEAt.bind (hp env state child hchildMetadata ls middle address pt cx fr hplace hpp
    hextMiddle hrel hgir hresults hgenerated) fun location after pt' fr' hdone P => ?_
  have hcell := P.has (address, .val (.ref location)) (by simp)
  apply SimEAt.of_simG
  refine leaf_def P hfield hext (by simp) (fun l => RVal.val (.ref l)) ?_
  simp only [execPure, getVal_of hcell, Core.expectRef, pure_bind]

theorem typedPlaceClaim_deref_ref {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) (mutability : Mutability) :
    TypedPlaceClaim (n + 2) cfg results (.deref (.ref mutability place)) := by
  exact typedPlaceClaim_deref (typedExprClaim_ref hp mutability)

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
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    SimEAt cx pt fr (evalArg n cfg env arg)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state

theorem typedArgClaim_zero (cfg : Cfg) (results : List Ty) (arg : Arg) :
    TypedArgClaim 0 cfg results arg := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  simp only [evalArg]
  exact SimEAt.of_timeout state

theorem typedArgClaim_byVal {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedArgClaim (n + 1) cfg results (.byVal expr) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  cases source with
  | byVal source =>
    simp only [lowerArg] at hlow
    simp only [evalArg]
    exact he env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated

theorem typedArgClaim_byRef {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) (mutability : Mutability) :
    TypedArgClaim (n + 1) cfg results (.byRef mutability place) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  cases source with
  | byRef _ source target =>
    simp only [lowerArg, bind_eq] at hlow
    obtain ⟨id, middle, hplace, hfreeze⟩ := hlow
    rcases borrowTo_ref_cases hfreeze with ⟨rfl, rfl⟩ | hfreeze | hfreeze
    · simp only [evalArg]
      refine SimEAt.bind (hp env state source hmetadata ls ls' r pt cx fr hplace hpp hext hrel hgir hresults hgenerated)
        fun location after pt' fr' hdone P => ?_
      exact SimEAt.ret P
    all_goals
      have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hfreeze)
      simp only [evalArg]
      refine SimEAt.bind (hp env state source hmetadata ls middle id pt cx fr hplace hpp hextMiddle hrel hgir hresults hgenerated)
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

open Core.Sound
def ArgSource.MatchesContext {cfg : Cfg} {env : Env} {state : St} {arg : Arg}
    {plans : Array (Array DemandPoint)} {path : List Nat} (world : World) (typing : TEnv) (roots : PEnv)
    (context : ArgContext cfg.mod plans path arg) (source : ArgSource cfg env state arg) : Prop :=
  match source, context with
  | .byVal child, .byVal argumentContext => child.plans = plans ∧ child.path = path ∧ child.world = world ∧
      child.typingEnv = typing ∧ child.rootsEnv = roots ∧ HEq child.context argumentContext
  | .byRef _ child _, .byRef argumentContext => child.plans = plans ∧ child.path = path ∧ child.world = world ∧
      child.typingEnv = typing ∧ child.rootsEnv = roots ∧ HEq child.context argumentContext

def ArgsSource.CallChildren {n : Nat} {cfg : Cfg} {env : Env} {initial : St}
    {c : ContextId} {all : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call c all origin) initial) :
    ∀ {args : List Arg} {state : St}, Nat → ArgsSource n cfg env args state → Prop
  | [], _, _, .nil _ => True
  | arg :: args, _, offset, .cons head rest =>
    ∃ found : all[offset]? = some arg,
      head.MatchesContext root.world root.typingEnv root.rootsEnv (callArgContext root.context offset arg found) ∧
      ∀ value after done, (rest value after done).CallChildren root (offset + 1)

open Core.Sound in
private theorem argSource_of_spec {cfg : Cfg} {env : Env} {expr : Expr} {initial state : St}
    (root : ExprSource cfg env expr initial) {path : List Nat} (arg : Arg)
    (ac : ArgContext cfg.mod root.plans path arg) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (roots : List RootRef) (results : List Ty)
    (active : ac.ActiveMatches root.typingEnv) (access : ac.AccessMatches root.typingEnv root.rootsEnv)
    (protection : ShrinkProtected root.world.D root.world.A
      (ac.mayShrink root.world.ownerP root.observation))
    (observed : ObservedSafe cfg.mod root.world
      (ac.mayShrink root.world.ownerP root.observation) root.observation state.store)
    (classified : cfg.mod.profile = .shrink →
      ClassifiedParameters cfg.mod root.world.P root.world.D root.observation state.store)
    (frame : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state ac.inputFuture)
    (typed : ArgTy root.typingEnv arg tn ty tn') (rooted : ArgRp root.rootsEnv arg rst roots rst')
    (effects : EffLe rst'.eff root.world.E)
    (metadata : SourceResults root.typingEnv root.rootsEnv results) :
    ∃ source : ArgSource cfg env state arg, source.resultsMatch results ∧ source.MatchesContext root.world root.typingEnv root.rootsEnv ac := by
  cases arg with
  | byVal expr =>
    cases ac with
    | byVal context =>
      exact ⟨.byVal {
        accepted := root.accepted, plans := root.plans, path := path, context := context,
        observation := root.observation, world := root.world, typingEnv := root.typingEnv,
        rootsEnv := root.rootsEnv, typingStart := tn, typingEnd := tn', ty := ty,
        rootsStart := rst, rootsEnd := rst', roots := roots, active := active, access := access,
        protection := protection, observed := observed, classified := classified,
        permission := root.permission, frame := frame, typed := typed, rooted := rooted,
        effects := effects }, metadata, ⟨rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩⟩
  | byRef mutability place =>
    cases ac with
    | byRef context =>
      obtain ⟨target, caps, typed, allowed, rfl⟩ := typed
      exact ⟨.byRef mutability {
        accepted := root.accepted, plans := root.plans, path := path, context := context,
        observation := root.observation, world := root.world, typingEnv := root.typingEnv,
        rootsEnv := root.rootsEnv, typingStart := tn, typingEnd := tn', ty := target,
        mutable := caps.1, contents := caps.2, rootsStart := rst, rootsEnd := rst', roots := roots,
        active := active, access := access, protection := protection, observed := observed,
        classified := classified, permission := root.permission, frame := frame,
        typed := typed, rooted := rooted, effects := effects } allowed, metadata, ⟨rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩⟩

open Core.Sound in
private theorem typedArgsSource_suffix {n : Nat} {cfg : Cfg} {env : Env} {initial : St}
    {c : ContextId} {all : List Arg} {origin : OriginId} {results : List Ty}
    (root : ExprSource cfg env (.call c all origin) initial)
    (metadata : SourceResults root.typingEnv root.rootsEnv results) (callee : Impl) :
    ∀ (args : List Arg) (ps : List Param) (offset : Nat) (state : St)
      (tn tn' : Nat) (rst rst' : RState) (ars : List (List RootRef)),
    args = all.drop offset → offset ≤ all.length →
    Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state
      (callArgsFuture root.context offset args) →
    ObservedSafe cfg.mod root.world (root.context.mayShrink root.world.ownerP root.observation)
      root.observation state.store →
    (cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod root.world.P root.world.D
      root.observation state.store) →
    ps.length = args.length → tyArgs root.typingEnv callee ps args tn = .ok ((), tn') →
    rpArgs root.rootsEnv args rst = .ok (ars, rst') → EffLe rst'.eff root.world.E →
    ∃ source : ArgsSource n cfg env args state, source.resultsMatch results ∧ source.CallChildren root offset
  | [], _, _, state, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨.nil state, trivial, trivial⟩
  | arg :: args, [], _, _, _, _, _, _, _, _, _, _, _, _, size, _, _, _ => by simp at size
  | arg :: args, param :: params, offset, state, tn, tn', rst, rst', ars, sourceEq, bound,
      frame, observed, classified, size, ht, hr, effects => by
    let tenv := root.typingEnv
    let penv := root.rootsEnv
    let ec := root.context
    have hl' : params.length = args.length := by simpa using size
    have harg : all[offset]? = some arg := by
      have first : (all.drop offset)[0]? = some arg := by rw [← sourceEq]; rfl
      simpa using first
    have hrest : args = all.drop (offset + 1) := by
      rw [List.drop_add_one_eq_tail_drop, ← sourceEq]
      rfl
    have nextBound : offset + 1 ≤ all.length := by
      have := (List.getElem?_eq_some_iff.mp harg).1
      omega
    cases hv : callee.vars[param.var]? with
    | none => cases arg <;> (simp only [tyArgs, hv] at ht; inv at ht)
    | some pv =>
      have key : ∃ ty t1 rho r1 ars', argMode arg = param.mode ∧ ArgTy tenv arg tn ty t1 ∧ ty.passableTo pv.ty = true ∧
          tyArgs tenv callee params args t1 = .ok ((), tn') ∧ ArgRp penv arg rst rho r1 ∧
          rpArgs penv args r1 = .ok (ars', rst') ∧ ars = rho :: ars' := by
        cases arg with
        | byVal e =>
          simp only [tyArgs, hv] at ht; inv at ht
          simp only [rpArgs] at hr; inv at hr
          obtain ⟨modeEq, te, t1, hte, hpass, tailTyping⟩ := ht
          obtain ⟨rho, r1, hre, ars', r2, hra, rfl, rfl⟩ := hr
          exact ⟨te, t1, rho, r1, ars', by simpa using modeEq, hte, hpass, tailTyping, hre, hra, rfl⟩
        | byRef mu p' =>
          simp only [tyArgs, hv] at ht; inv at ht
          simp only [rpArgs] at hr; inv at hr
          obtain ⟨modeEq, t, b, contents, t1, htp, hallowed, hrt, ht⟩ := ht
          obtain ⟨rho, r1, hre, ars', r2, hra, rfl, rfl⟩ := hr
          have h2 : (Ty.ref mu t).passableTo pv.ty = true ∧
              tyArgs tenv callee params args t1 = .ok ((), tn') := by
            rcases ht with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> exact ⟨h1, h2⟩
          have hrt' : t.refTarget = true ∨ (t.isSlice = true ∧ b = true ∧ p'.sliceArg = true) := by
            cases t <;> simpa [PlaceInfo.referenceWritable, Ty.refTarget, Ty.isSlice,
              Bool.or_eq_true, Bool.and_eq_true, and_assoc] using hrt
          exact ⟨.ref mu t, t1, rho, r1, ars', by simpa using modeEq, ⟨t, (b, contents), htp, hrt', rfl⟩, h2.1, h2.2, hre, hra, rfl⟩
      obtain ⟨ty, t1, rho, r1, ars', modeEq, hat, hpass, tailTyping, har, hra, rfl⟩ := key


      let ac := callArgContext ec offset arg harg
      have shrinkEq : ac.mayShrink root.world.ownerP root.observation =
          ec.mayShrink root.world.ownerP root.observation := by
        funext r
        exact propext (callArgContext_mayShrink_iff ec offset arg harg
          root.world.ownerP root.observation r)
      have childFrame : Core.Sound.Frame cfg.mod root.world tenv penv env state ac.inputFuture :=
        frame.changeFuture (fun x _ member =>
          callArgContext_inputFuture_subset ec offset arg args harg hrest member)
      have childProtected : ShrinkProtected root.world.D root.world.A
          (ac.mayShrink root.world.ownerP root.observation) := by
        rw [shrinkEq]
        exact root.protection
      have childObserved : ObservedSafe cfg.mod root.world
          (ac.mayShrink root.world.ownerP root.observation) root.observation state.store := by
        rw [shrinkEq]
        exact observed
      have childEffects : EffLe r1.eff root.world.E := (rpArgs_mono hra).2.trans effects
      obtain ⟨source, hmetadata, hcanonical⟩ := argSource_of_spec root arg ac tn t1 ty rst r1 rho results
        (callArgContext_activeMatches ec offset arg harg root.active)
        (callArgContext_accessMatches ec offset arg harg root.access)
        childProtected childObserved classified childFrame hat har childEffects metadata
      have nextReady : ∀ value after, evalArg n cfg env arg state = .ok value after →
          ∃ source : ArgsSource n cfg env args after, source.resultsMatch results ∧ source.CallChildren root (offset + 1) := by
        intro value after hdone
        have hs := (Core.Sound.specs_all (Core.Sound.validate_modOk cfg.mod root.accepted)
          cfg.profile root.plans n).arg (root.path ++ [offset]) arg ac root.observation
          root.world tenv penv env state tn t1 ty rst r1 rho
          (callArgContext_activeMatches ec offset arg harg root.active)
          (callArgContext_accessMatches ec offset arg harg root.access)
          childProtected childObserved classified root.permission childFrame hat har childEffects
        unfold Sat at hs
        rw [hdone] at hs
        obtain ⟨frame1, footprint1, types1, values1, observed1, retained1, pilot1,
          typed1, roots1, classified1, ownerRooted1, forbidden1, mutations1⟩ := hs
        rw [shrinkEq] at observed1
        exact typedArgsSource_suffix root metadata callee args params (offset + 1) after
          t1 tn' r1 rst' ars' hrest nextBound
          (callArgFrame_rest ec offset arg args harg hrest root.active frame1)
          observed1 classified1 hl' tailTyping hra effects
      let rest := fun value after hdone => Classical.choose (nextReady value after hdone)
      refine ⟨.cons source rest, ⟨hmetadata, fun value after hdone =>
        (Classical.choose_spec (nextReady value after hdone)).1⟩, harg, hcanonical, ?_⟩
      intro value after hdone
      exact (Classical.choose_spec (nextReady value after hdone)).2

open Core.Sound in
theorem ExprSource.callArgsCanonical {cfg : Cfg} {env : Env} {state : St} {c : ContextId}
    {args : List Arg} {origin : OriginId} (root : ExprSource cfg env (.call c args origin) state)
    (n : Nat) (results : List Ty) (metadata : SourceResults root.typingEnv root.rootsEnv results) :
    ∃ source : ArgsSource n cfg env args state, source.resultsMatch results ∧ source.CallChildren root 0 := by
  have replay := root.rooted
  simp only [rpExpr] at replay
  inv at replay
  obtain ⟨ars, middle, argumentsReplay, contentsCheck, callReplay⟩ := replay
  have argumentsEffects := (PMono.rpCall _ _ _ _ _ _ callReplay).2.trans root.effects
  obtain ⟨context, callee, contextAt, implementationAt, argumentCheck, effectAt, resultReplay⟩ :=
    rpCall_ok _ _ _ _ _ _ callReplay
  rw [root.frame.mod_p] at contextAt implementationAt
  have contextAtT : root.typingEnv.mod.contexts[c]? = some context := by
    rw [root.frame.mod_t]
    exact contextAt
  have implementationAtT : root.typingEnv.mod.impls[context.impl]? = some callee := by
    rw [root.frame.mod_t]
    exact implementationAt
  have typing := root.typed
  simp only [tyExpr, contextAtT, implementationAtT] at typing
  inv at typing
  obtain ⟨_, size, next, argumentTypes, _, _, resultType, _⟩ := typing
  have suffixFuture : callArgsFuture root.context 0 args = root.context.inputFuture := by
    cases root.context <;> simp [callArgsFuture, EvaluationContext.inputFuture,
      NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables, Expr.variables]
  exact typedArgsSource_suffix root metadata callee args callee.params.toList 0 state
    root.typingStart next root.rootsStart middle ars (by simp) (by omega)
    (by simpa [suffixFuture] using root.frame) root.observed root.classified
    (by simpa using size) argumentTypes argumentsReplay argumentsEffects

def TypedArgsClaim (n : Nat) (cfg : Cfg) (results : List Ty) (args : List Arg) : Prop :=
  ∀ (env : Env) (state : St) (source : ArgsSource n cfg env args state), source.resultsMatch results →
    ∀ (ls ls' : LS) (ids : List ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerArgs args (lowerEnv cfg.mod env.vars results) ls = (ids, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    SimEAt cx pt fr (mapList (evalArg n cfg env) args)
      (fun values pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr ls' fr' pt' (cellsOf ids values)) state

theorem ExprSource.callArgs {cfg : Cfg} {env : Env} {state : St} {c : ContextId}
    {args : List Arg} {origin : OriginId} (root : ExprSource cfg env (.call c args origin) state)
    (n : Nat) (results : List Ty) (metadata : SourceResults root.typingEnv root.rootsEnv results) :
    ∃ source : ArgsSource n cfg env args state, source.resultsMatch results := by
  obtain ⟨source, metadata, canonical⟩ := root.callArgsCanonical n results metadata
  exact ⟨source, metadata⟩

theorem typedArgsClaim {n : Nat} {cfg : Cfg} {results : List Ty} : ∀ (args : List Arg),
    (∀ arg ∈ args, TypedArgClaim n cfg results arg) → TypedArgsClaim n cfg results args
  | [], _ => by
    intro env state source hmetadata ls ls' ids pt cx fr hlow hpp hext hrel hgir hresults hgenerated
    simp only [lowerArgs, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    exact SimEAt.ret ⟨rfl, by simpa [cellsOf] using Post.init hrel hpp⟩
  | arg :: args, ha => by
    intro env state source hmetadata ls ls' ids pt cx fr hlow hpp hext hrel hgir hresults hgenerated
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
        harg hpp hextMiddle hrel hgir hresults hgenerated) fun value state1 pt1 fr1 hdone P => ?_
      refine SimEAt.bind (typedArgsClaim args (fun arg harg => ha arg (by simp [harg]))
        env state1 (rest value state1 hdone) (hmetadata.2 value state1 hdone) middle after restIds pt1 cx fr1 hargs P.pp hext P.rel hgir hresults (hgenerated.lowerArg arg harg))
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
          c values) after)
    (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerExpr (.call c args org) (lowerEnv cfg.mod env.vars results) ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results)
    (hgenerated : GeneratedBuilderState ls) :
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
    hargs hpp hextMiddle hrel hgir hresults hgenerated) fun values afterArgs pt1 fr1 hdone ⟨hlen, P⟩ => ?_
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
        c values) afterArgs := by
    rw [hcfg, P.rel.depth]
    exact hc values afterArgs hdone
  have hs := SimEAt.call_step hi hread hcall
  rcases htail with ⟨hnr, _⟩ | ⟨_, rfl⟩
  · have hn := Core.Sound.noReturn_sound cfg.mod cfg.profile c hnr n env.depth values
    exact SimEAt.of_stops (hn afterArgs) (fun _ _ h => h) hs
  · exact hs.mono fun value afterValue pt' fr' hdoneValue ⟨hpt, hfr⟩ => by
      subst hpt; subst hfr
      exact (Post.def_leaf P hdef hext (.val value)).1

theorem typedExprClaim_call {n : Nat} {cfg : Cfg} {results : List Ty} {c : ContextId}
    {args : List Arg} {origin : OriginId} (ha : TypedArgsClaim n cfg results args)
    (hc : ∀ env state (source : ExprSource cfg env (.call c args origin) state),
      SourceResults source.typingEnv source.rootsEnv results → ∀ values after,
      mapList (evalArg n cfg env) args state = .ok values after →
      EventualM (enterCall n cfg env.depth c values)
        (fun fuel => callFn fuel ⟨cfg.profile, lower cfg.mod⟩ env.depth
          c values) after) :
    TypedExprClaim (n + 1) cfg results (.call c args origin) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨argsSource, argsMetadata⟩ := source.callArgs n results hmetadata
  exact typed_call_sim ha env state argsSource argsMetadata (hc env state source hmetadata)
    ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated

inductive ExprsSource (n : Nat) (cfg : Cfg) (env : Env) : List Expr → St → Type
  | nil (state : St) : ExprsSource n cfg env [] state
  | cons {expr : Expr} {exprs : List Expr} {state : St}
      (source : ExprSource cfg env expr state)
      (rest : ∀ value after, evalExpr n cfg env expr state = .ok value after →
        ExprsSource n cfg env exprs after) : ExprsSource n cfg env (expr :: exprs) state

def ExprsSource.resultsMatch {n : Nat} {cfg : Cfg} {env : Env} :
    {exprs : List Expr} → {state : St} → ExprsSource n cfg env exprs state → List Ty → Prop
  | [], _, .nil _, _ => True
  | _ :: _, _, .cons source rest, results =>
      SourceResults source.typingEnv source.rootsEnv results ∧
        ∀ value after hdone, (rest value after hdone).resultsMatch results

private inductive ExprsTyping (env : TEnv) : List Expr → Nat → Nat → Prop
  | nil (count : Nat) : ExprsTyping env [] count count
  | cons {expr : Expr} {rest : List Expr} {before middle after : Nat} {ty : Ty}
      (head : tyExpr env expr before = .ok (ty, middle))
      (tail : ExprsTyping env rest middle after) : ExprsTyping env (expr :: rest) before after

private theorem exprsTyping_of_as {env : TEnv} {el : Ty} :
    ∀ {es : List Expr} {before after : Nat},
    tyExprsAs env el es before = .ok ((), after) → ExprsTyping env es before after
  | [], _, _, h => by
    simp only [tyExprsAs] at h
    have h' := (Core.Sound.st_pure_ok _ _ _).1 h
    cases h'
    exact .nil _
  | _ :: _, _, _, h => by
    simp only [tyExprsAs] at h
    inv at h
    obtain ⟨_, _, head, _, tail⟩ := h
    exact .cons head (exprsTyping_of_as tail)

private theorem exprsTyping_of_struct {env : TEnv} :
    ∀ {ts : List Ty} {es : List Expr} {before after : Nat},
    tyStructExprs env ts es before = .ok ((), after) → ExprsTyping env es before after
  | [], [], _, _, h => by
    simp only [tyStructExprs] at h
    have h' := (Core.Sound.st_pure_ok _ _ _).1 h
    cases h'
    exact .nil _
  | [], _ :: _, _, _, h => by simp only [tyStructExprs] at h; inv at h
  | _ :: _, [], _, _, h => by simp only [tyStructExprs] at h; inv at h
  | _ :: _, _ :: _, _, _, h => by
    simp only [tyStructExprs] at h
    inv at h
    obtain ⟨_, _, head, _, tail⟩ := h
    exact .cons head (exprsTyping_of_struct tail)

open Core.Sound in
private theorem typedExprsSource_suffix {n : Nat} {cfg : Cfg} {env : Env} {initial : St}
    {isStruct : Bool} {target : Ty} {all : List Expr} {results : List Ty}
    (root : ExprSource cfg env
      (if isStruct then .structLit target all else .arrLit target all) initial)
    (metadata : SourceResults root.typingEnv root.rootsEnv results) :
    ∀ (es : List Expr) (offset : Nat) (state : St) (tn tn' : Nat) (rst rst' : RState),
    all.drop offset = es →
    Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state
      (es.flatMap Expr.variables ++ root.context.outputFuture) →
    ObservedSafe cfg.mod root.world (root.context.mayShrink root.world.ownerP root.observation)
      root.observation state.store →
    (cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod root.world.P root.world.D
      root.observation state.store) →
    ExprsTyping root.typingEnv es tn tn' →
    rpExprs root.rootsEnv es rst = .ok ((), rst') → EffLe rst'.eff root.world.E →
    ∃ source : ExprsSource n cfg env es state, source.resultsMatch results
  | [], _, state, _, _, _, _, _, _, _, _, _, _, _ => ⟨.nil state, trivial⟩
  | expr :: rest, offset, state, tn, tn', rst, rst', hdrop, frame, observed,
      classified, typing, rooted, effects => by
    cases typing with
    | cons head tail =>
      simp only [rpExprs] at rooted
      inv at rooted
      obtain ⟨roots, middle, hre, hrr⟩ := rooted
      let ec := root.context
      change Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state
        ((expr :: rest).flatMap Expr.variables ++ ec.outputFuture) at frame
      have hget : all[offset]? = some expr := by
        have first : (all.drop offset)[0]? = some expr := by rw [hdrop]; rfl
        simpa using first
      have hdropTail : all.drop (offset + 1) = rest := by
        rw [List.drop_add_one_eq_tail_drop, hdrop]
        rfl
      have hchild : (DemandNode.expression
          (if isStruct then .structLit target all else .arrLit target all)).child? offset =
          some (.expression expr) := by
        cases isStruct <;> simp [DemandNode.child?, DemandNode.children, hget]
      have phase : DemandPhase.expression = (DemandNode.expression
          (if isStruct then .structLit target all else .arrLit target all)).primaryPhase := by
        cases isStruct <;> rfl
      let child := ec.child phase offset (.expression expr) .expression hchild (by trivial)
      have active := ec.child_activeMatches phase offset (.expression expr) .expression hchild
        (by trivial) root.typingEnv root.typingEnv root.active (by intro x; rfl)
      have access := (ec.child_accessMatches_iff phase offset (.expression expr) .expression hchild
        (by trivial) root.typingEnv root.rootsEnv).mpr root.access
      have shrinkEq : child.mayShrink root.world.ownerP root.observation =
          ec.mayShrink root.world.ownerP root.observation := by
        funext r
        exact propext (ec.child_mayShrink_iff phase offset (.expression expr) .expression hchild
          (by trivial) root.world.ownerP root.observation r)
      have childOutput : child.outputFuture =
          match (generalizing := false) ec with
          | .pilot _ active => active
          | .shrink _ context => rest.flatMap Expr.variables ++ context.expected.frame.future := by
        dsimp only [child]
        cases ec with
        | pilot profile active => cases isStruct <;> rfl
        | @shrink pc profile context =>
          let transition := context.child phase offset (.expression expr) .expression hchild (by trivial)
          change transition.context.expected.frame.future =
            rest.flatMap Expr.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          have hlt : offset < all.length := by
            have hpos : 0 < (all.drop offset).length := by rw [hdrop]; simp
            rw [List.length_drop] at hpos
            omega
          have hexpect : (DemandNode.expression
                (if isStruct then .structLit target all else .arrLit target all)).childExpectation?
              pc.approvals.access
              ⟨root.path, .expression, context.expected.frame.active, context.expected.frame.future,
                context.expected.frame.retained⟩ offset = some
              ⟨context.expected.frame.active, rest.flatMap Expr.variables ++ context.expected.frame.future⟩ := by
            cases isStruct <;>
              simp [DemandNode.childExpectation?, DemandNode.childFuture,
                DemandNode.visibleForChild, DemandNode.child?, DemandNode.children, hget, hlt, hdropTail]
          exact DemandNode.childFrame_future transition.childFrameEq hexpect
      have childInput : child.inputFuture = expr.variables ++ child.outputFuture := by
        dsimp only [child]
        cases ec <;> rfl
      have childFrame : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv
          env state child.inputFuture := by
        rw [childInput, childOutput]
        cases hec : ec with
        | pilot profile active =>
          change Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state
            (expr.variables ++ active)
          have outputEq : ec.outputFuture = active := by
            rw [hec]
            cases isStruct <;> rfl
          rw [outputEq] at frame
          apply frame.narrowFuture
          intro x hx
          simp only [List.mem_append] at hx
          change x ∈ (expr.variables ++ rest.flatMap Expr.variables) ++ active
          rcases hx with h | h
          · exact List.mem_append_left _ (List.mem_append_left _ h)
          · exact List.mem_append_right _ h
        | shrink profile context =>
          simpa [hec, EvaluationContext.outputFuture, NodeContext.outputFuture,
            List.flatMap_cons, List.append_assoc] using frame
      let source : ExprSource cfg env expr state := {
        accepted := root.accepted, plans := root.plans, path := root.path ++ [offset],
        context := child, observation := root.observation, world := root.world,
        typingEnv := root.typingEnv, rootsEnv := root.rootsEnv,
        typingStart := _, typingEnd := _, ty := _, rootsStart := rst, rootsEnd := middle,
        roots := roots, active := active, access := access,
        protection := by simpa [shrinkEq] using root.protection,
        observed := by simpa [shrinkEq] using observed, classified := classified,
        permission := root.permission, frame := childFrame, typed := head, rooted := hre,
        effects := (rpExprs_mono hrr).2.trans effects }
      have nextReady : ∀ value after, evalExpr n cfg env expr state = .ok value after →
          ∃ source : ExprsSource n cfg env rest after, source.resultsMatch results := by
        intro value after hdone
        have done := source.result n value hdone
        have frame1 := done.frame
        change Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv
          env after child.outputFuture at frame1
        rw [childOutput] at frame1
        have tailFrame : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv
            env after (rest.flatMap Expr.variables ++ ec.outputFuture) := by
          cases hec : ec with
          | pilot profile live =>
            have hframe : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv
                env after live := by
              simpa only [hec] using frame1
            apply hframe.changeFuture
            intro x hx _
            have hactive := root.active
            change ec.ActiveMatches root.typingEnv at hactive
            rw [hec] at hactive
            exact (hactive x).mpr hx
          | shrink profile context =>
            simpa [hec, EvaluationContext.outputFuture, NodeContext.outputFuture] using frame1
        exact typedExprsSource_suffix root metadata rest (offset + 1) after _ tn' middle rst'
          hdropTail tailFrame (by simpa [source, shrinkEq] using done.observed)
          done.classified tail hrr effects
      let next := fun value after hdone => Classical.choose (nextReady value after hdone)
      exact ⟨.cons source next, metadata, fun value after hdone =>
        Classical.choose_spec (nextReady value after hdone)⟩

private theorem aggregate_sources {n : Nat} {cfg : Cfg} {env : Env} {state : St}
    {isStruct : Bool} {target : Ty} {es : List Expr} {results : List Ty}
    (source : ExprSource cfg env
      (if isStruct then .structLit target es else .arrLit target es) state)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (typed : ExprsTyping source.typingEnv es source.typingStart source.typingEnd)
    (rooted : rpExprs source.rootsEnv es source.rootsStart = .ok ((), source.rootsEnd)) :
    ∃ children : ExprsSource n cfg env es state, children.resultsMatch results := by
  have frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (es.flatMap Expr.variables ++ source.context.outputFuture) := by
    have hf := source.frame
    cases isStruct <;> cases hec : source.context <;>
      simpa [hec, Core.Sound.EvaluationContext.inputFuture, Core.Sound.EvaluationContext.outputFuture,
        Core.Sound.NodeContext.inputFuture, Core.Sound.NodeContext.outputFuture,
        DemandNode.variables, DemandNode.visibleAfter, Expr.variables] using hf
  exact typedExprsSource_suffix source metadata es 0 state source.typingStart source.typingEnd
    source.rootsStart source.rootsEnd rfl frame source.observed source.classified typed rooted source.effects

theorem ExprSource.arrLitChildren {cfg : Cfg} {env : Env} {state : St} {target : Ty}
    {es : List Expr} (source : ExprSource cfg env (.arrLit target es) state) (n : Nat)
    (results : List Ty) (metadata : SourceResults source.typingEnv source.rootsEnv results) :
    ∃ children : ExprsSource n cfg env es state, children.resultsMatch results := by
  have rooted := source.rooted
  simp only [rpExpr] at rooted
  inv at rooted
  obtain ⟨middle, hre, _, hend⟩ := rooted
  cases hend
  have typed : ExprsTyping source.typingEnv es source.typingStart source.typingEnd := by
    have ht := source.typed
    cases target <;> simp only [tyExpr] at ht <;> inv at ht
    · obtain ⟨_, _, _, next, check, _, hend⟩ := ht
      cases hend
      exact exprsTyping_of_as check
    · obtain ⟨_, _, next, check, _, hend⟩ := ht
      cases hend
      exact exprsTyping_of_as check
    · obtain ⟨_, _, next, check, _, hend⟩ := ht
      cases hend
      exact exprsTyping_of_as check
    · obtain ⟨_, _, next, check, _, hend⟩ := ht
      cases hend
      exact exprsTyping_of_as check
  exact aggregate_sources (isStruct := false) source metadata typed hre

theorem ExprSource.structLitChildren {cfg : Cfg} {env : Env} {state : St} {target : Ty}
    {es : List Expr} (source : ExprSource cfg env (.structLit target es) state) (n : Nat)
    (results : List Ty) (metadata : SourceResults source.typingEnv source.rootsEnv results) :
    ∃ children : ExprsSource n cfg env es state, children.resultsMatch results := by
  have rooted := source.rooted
  simp only [rpExpr] at rooted
  inv at rooted
  obtain ⟨middle, hre, _, hend⟩ := rooted
  cases hend
  have typed := source.typed
  simp only [tyExpr] at typed
  inv at typed
  obtain ⟨definition, next, hdefinition, _, after, check, _, hend⟩ := typed
  obtain ⟨_, _, _, _, _, _, hstart⟩ := Core.Sound.structDef_ok _ _ _ _ _ hdefinition
  cases hstart
  cases hend
  exact aggregate_sources (isStruct := true) source metadata (exprsTyping_of_struct check) hre

def TypedExprsClaim (n : Nat) (cfg : Cfg) (results : List Ty) (exprs : List Expr) : Prop :=
  ∀ (env : Env) (state : St) (source : ExprsSource n cfg env exprs state), source.resultsMatch results →
    ∀ (ls ls' : LS) (ids : List ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerExprs exprs (lowerEnv cfg.mod env.vars results) ls = (ids, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    SimEAt cx pt fr (mapList (evalExpr n cfg env) exprs)
      (fun values pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr ls' fr' pt' (cellsOf ids values)) state

theorem typedExprsClaim {n : Nat} {cfg : Cfg} {results : List Ty} : ∀ (exprs : List Expr),
    (∀ expr ∈ exprs, TypedExprClaim n cfg results expr) → TypedExprsClaim n cfg results exprs
  | [], _ => by
    intro env state source hmetadata ls ls' ids pt cx fr hlow hpp hext hrel hgir hresults hgenerated
    simp only [lowerExprs, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    exact SimEAt.ret ⟨rfl, by simpa [cellsOf] using Post.init hrel hpp⟩
  | expr :: exprs, ha => by
    intro env state source hmetadata ls ls' ids pt cx fr hlow hpp hext hrel hgir hresults hgenerated
    cases source with
    | cons source rest =>
      simp only [lowerExprs, bind_eq] at hlow
      obtain ⟨id, middle, hhead, restIds, after, htail, hret⟩ := hlow
      rw [pure_run] at hret
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hret
      have hextMiddle : ExtT middle cx.fn.blocks :=
        hext.of_adv (advB_lowerExprs exprs _ _ _ _ htail)
      simp only [mapList]
      refine SimEAt.bind (ha expr (by simp) env state source hmetadata.1 ls middle id pt cx fr
        hhead hpp hextMiddle hrel hgir hresults hgenerated) fun value state1 pt1 fr1 hdone P => ?_
      refine SimEAt.bind (typedExprsClaim exprs (fun expr h => ha expr (by simp [h]))
        env state1 (rest value state1 hdone) (hmetadata.2 value state1 hdone)
        middle after restIds pt1 cx fr1 htail P.pp hext P.rel hgir hresults (hgenerated.lowerExpr expr hhead))
        fun values state2 pt2 fr2 hdoneRest ⟨hlen, Q⟩ => ?_
      exact SimEAt.ret ⟨by simp [hlen], by simpa [cellsOf] using P.comp Q⟩

theorem typedExprClaim_arrLit {n : Nat} {cfg : Cfg} {results : List Ty} {es : List Expr}
    (children : TypedExprsClaim n cfg results es) (target : Ty) :
    TypedExprClaim (n + 1) cfg results (.arrLit target es) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨sources, hsourceMetadata⟩ := source.arrLitChildren n results hmetadata
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨ids, middle, hchildren, hdef⟩ := hlow
  have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimEAt.bind (children env state sources hsourceMetadata ls middle ids pt cx fr
    hchildren hpp hextMiddle hrel hgir hresults hgenerated) fun values after pt1 fr1 hdone ⟨hlen, P⟩ => ?_
  have hread := mapList_getVal_cells hlen P.has
  apply SimEAt.of_simG
  exact leaf_def P hdef hext (by simp) RVal.val (by simp only [execPure, hread, pure_bind])

theorem typedExprClaim_structLit {n : Nat} {cfg : Cfg} {results : List Ty} {es : List Expr}
    (children : TypedExprsClaim n cfg results es) (target : Ty) :
    TypedExprClaim (n + 1) cfg results (.structLit target es) := by
  intro env state source hmetadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨sources, hsourceMetadata⟩ := source.structLitChildren n results hmetadata
  have typing := source.typed
  simp only [tyExpr] at typing
  inv at typing
  obtain ⟨definition, _, hdefinition, _⟩ := typing
  obtain ⟨sid, ts, rfl, _⟩ := Core.Sound.structDef_ok _ _ _ _ _ hdefinition
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨ids, middle, hchildren, hdef⟩ := hlow
  have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimEAt.bind (children env state sources hsourceMetadata ls middle ids pt cx fr
    hchildren hpp hextMiddle hrel hgir hresults hgenerated) fun values after pt1 fr1 hdone ⟨hlen, P⟩ => ?_
  have hread := mapList_getVal_cells hlen P.has
  apply SimEAt.of_simG
  exact leaf_def P hdef hext (by simp) RVal.val (by simp only [execPure, hread, pure_bind])

end Goose.Lower
