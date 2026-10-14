import Goose.Lower.RuntimeSim
import Goose.Lower.Arguments
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

def TypedExprClaim (n : Nat) (cfg : Cfg) (results : List Ty) (expr : Expr) : Prop :=
  ∀ (env : Env) (state : St), ExprSource cfg env expr state →
    ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerExpr expr (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod →
    SimEAt cx pt fr (evalExpr n cfg env expr)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state

def TypedPlaceClaim (n : Nat) (cfg : Cfg) (results : List Ty) (place : Place) : Prop :=
  ∀ (env : Env) (state : St), PlaceSource cfg env place state →
    ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerPlace place (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod →
    SimEAt cx pt fr (evalPlace n cfg env place)
      (fun location pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val (.ref location))]) state

theorem typedExprClaim_zero (cfg : Cfg) (results : List Ty) (expr : Expr) :
    TypedExprClaim 0 cfg results expr := by
  intro env state source ls ls' r pt cx fr hlow hpp hext hrel hgir
  simp only [evalExpr]
  exact SimEAt.of_timeout state

theorem typedPlaceClaim_zero (cfg : Cfg) (results : List Ty) (place : Place) :
    TypedPlaceClaim 0 cfg results place := by
  intro env state source ls ls' r pt cx fr hlow hpp hext hrel hgir
  simp only [evalPlace]
  exact SimEAt.of_timeout state

theorem typedExprClaim_fragment (n : Nat) (cfg : Cfg) (results : List Ty) (expr : Expr)
    (hok : exprOk expr = true) : TypedExprClaim n cfg results expr := by
  intro env state source ls ls' r pt cx fr hlow hpp hext hrel hgir
  exact SimEAt.of_simG ((claims n).expr expr hok (lowerEnv cfg.mod env.vars results)
    ls r ls' pt cfg env cx fr hlow hpp hext hrel) state

theorem typedPlaceClaim_fragment (n : Nat) (cfg : Cfg) (results : List Ty) (place : Place)
    (hok : placeOk place = true) : TypedPlaceClaim n cfg results place := by
  intro env state source ls ls' r pt cx fr hlow hpp hext hrel hgir
  exact SimEAt.of_simG ((claims n).place place hok (lowerEnv cfg.mod env.vars results)
    ls r ls' pt cfg env cx fr hlow hpp hext hrel) state

inductive ArgSource (cfg : Cfg) (env : Env) (state : St) : Arg → Type
  | byVal {expr : Expr} (source : ExprSource cfg env expr state) :
      ArgSource cfg env state (.byVal expr)
  | byRef {place : Place} (mutability : Mutability) (source : PlaceSource cfg env place state)
      (target : source.ty.refTarget = true ∨
        (source.ty.isSlice = true ∧ source.mutable = true ∧ place.sliceArg = true)) :
      ArgSource cfg env state (.byRef mutability place)

def TypedArgClaim (n : Nat) (cfg : Cfg) (results : List Ty) (arg : Arg) : Prop :=
  ∀ (env : Env) (state : St), ArgSource cfg env state arg →
    ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerArg arg (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod →
    SimEAt cx pt fr (evalArg n cfg env arg)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state

theorem typedArgClaim_zero (cfg : Cfg) (results : List Ty) (arg : Arg) :
    TypedArgClaim 0 cfg results arg := by
  intro env state source ls ls' r pt cx fr hlow hpp hext hrel hgir
  simp only [evalArg]
  exact SimEAt.of_timeout state

theorem typedArgClaim_byVal {n : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (he : TypedExprClaim n cfg results expr) : TypedArgClaim (n + 1) cfg results (.byVal expr) := by
  intro env state source ls ls' r pt cx fr hlow hpp hext hrel hgir
  cases source with
  | byVal source =>
    simp only [lowerArg] at hlow
    simp only [evalArg]
    exact he env state source ls ls' r pt cx fr hlow hpp hext hrel hgir

theorem typedArgClaim_byRef {n : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (hp : TypedPlaceClaim n cfg results place) (mutability : Mutability) :
    TypedArgClaim (n + 1) cfg results (.byRef mutability place) := by
  intro env state source ls ls' r pt cx fr hlow hpp hext hrel hgir
  cases source with
  | byRef _ source target =>
    simp only [lowerArg, bind_eq] at hlow
    obtain ⟨id, middle, hplace, hfreeze⟩ := hlow
    rcases freezeTo_cases hfreeze with ⟨rfl, rfl⟩ | hfreeze
    · simp only [evalArg]
      refine SimEAt.bind (hp env state source ls ls' r pt cx fr hplace hpp hext hrel hgir)
        fun location after pt' fr' hdone P => ?_
      exact SimEAt.ret P
    · have hextMiddle : ExtT middle cx.fn.blocks := hext.of_adv (adv_emitDef hfreeze)
      simp only [evalArg]
      refine SimEAt.bind (hp env state source ls middle id pt cx fr hplace hpp hextMiddle hrel hgir)
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

def TypedArgsClaim (n : Nat) (cfg : Cfg) (results : List Ty) (args : List Arg) : Prop :=
  ∀ (env : Env) (state : St), ArgsSource n cfg env args state →
    ∀ (ls ls' : LS) (ids : List ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerArgs args (lowerEnv cfg.mod env.vars results) ls = (ids, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod →
    SimEAt cx pt fr (mapList (evalArg n cfg env) args)
      (fun values pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr ls' fr' pt' (cellsOf ids values)) state

theorem typedArgsClaim {n : Nat} {cfg : Cfg} {results : List Ty} : ∀ (args : List Arg),
    (∀ arg ∈ args, TypedArgClaim n cfg results arg) → TypedArgsClaim n cfg results args
  | [], _ => by
    intro env state source ls ls' ids pt cx fr hlow hpp hext hrel hgir
    simp only [lowerArgs, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    exact SimEAt.ret ⟨rfl, by simpa [cellsOf] using Post.init hrel hpp⟩
  | arg :: args, ha => by
    intro env state source ls ls' ids pt cx fr hlow hpp hext hrel hgir
    cases source with
    | cons source rest =>
      simp only [lowerArgs, bind_eq] at hlow
      obtain ⟨id, middle, harg, restIds, after, hargs, hret⟩ := hlow
      rw [pure_run] at hret
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hret
      have hextMiddle : ExtT middle cx.fn.blocks :=
        hext.of_adv (advB_lowerArgs args _ _ _ _ hargs)
      simp only [mapList]
      refine SimEAt.bind (ha arg (by simp) env state source ls middle id pt cx fr
        harg hpp hextMiddle hrel hgir) fun value state1 pt1 fr1 hdone P => ?_
      refine SimEAt.bind (typedArgsClaim args (fun arg harg => ha arg (by simp [harg]))
        env state1 (rest value state1 hdone) middle after restIds pt1 cx fr1 hargs P.pp hext P.rel hgir)
        fun values state2 pt2 fr2 hdoneRest ⟨hlen, Q⟩ => ?_
      exact SimEAt.ret ⟨by simp [hlen], by simpa [cellsOf] using P.comp Q⟩

end Goose.Lower
