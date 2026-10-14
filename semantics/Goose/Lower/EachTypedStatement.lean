import Goose.Lower.EachReentry
import Goose.Lower.EachStatement

namespace Goose.Lower

open Goose.Core Goose.Core.Sound Goose.Proofs.Memory

theorem EachPlan.blockCallback {n : Nat} {cfg : Cfg} {env : Env} {initial : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    (plan : EachPlan source) (results : List Ty)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (blocks : ∀ fuel, fuel < n → ∀ loop pre pre',
      TypedBlockLoopSimulation fuel cfg results (some loop) pre pre' false body)
    (cx : GIR.FnCtx) (module : cx.cfg.mod = lower cfg.mod) (returned : cx.fn.results = results)
    (header : LS) (base : GIR.Frame) (counter irView sampled hb : GIR.ValueId)
    (owner : Option GIR.ValueId) (value : ViewVal) :
    EachBlockCallback n cfg env cx (lowerEnv cfg.mod env.vars results) header counter irView sampled hb
      owner value base x idx byRef body origin (fun i state => EachLoopState plan value state ∧
        LocTy state.store ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩ plan.element) := by
  intro fuel smaller depth exit input withElem withValue output elem irValue result tb i frame
    state element elementState ptValue frValue hElem hValue hBlock extension counterBound
    stackAt depthAt targets point invariant allowed success valuePost pre
  obtain ⟨bodySource, typing, roots, world, observation, plans, path, future, retained, may, context⟩ :=
    allowed.1.bodySource i element allowed.2 success
  have bodyMetadata : SourceResults bodySource.typingEnv bodySource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  have loopDepth : depth = env.scopes.length := by
    rw [depthAt, invariant.rel.stack, List.length_map]
  have loopCounter : LoopCounterAt (some ⟨depth, exit, .next hb .i64 counter⟩) withValue frValue :=
    ⟨Nat.lt_of_lt_of_le counterBound valuePost.mono, .i64, i,
      (valuePost.same counter counterBound).trans invariant.counterValue⟩
  have lexical : bodySource.typingEnv.loops ≠ 0 := by
    rw [typing]
    exact Nat.ne_of_gt (Nat.zero_lt_succ source.typingEnv.loops)
  exact eachBlock_typed_sim bodySource (blocks fuel smaller _ _ _) bodyMetadata
    lexical withValue output result ptValue cx frValue
    hBlock valuePost.pp extension valuePost.rel pre module returned loopDepth targets loopCounter

theorem EachLoopState.afterIteration {cfg : Cfg} {env : Env} {initial state after : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    {plan : EachPlan source} {value : ViewVal} (runtime : EachLoopState plan value state)
    (i fuel : Nat) (flow : Flow)
    (location : LocTy state.store ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩ plan.element)
    (advance : (∃ v, flow = .normal v) ∨ flow = .cont)
    (success : eachIterationCore fuel cfg env x idx byRef body value i state = .ok flow after) :
    EachLoopState plan value after := by
  obtain ⟨element, prepared, bodyRun⟩ := eachIteration_block_success location advance success
  obtain ⟨bodySource, typing, roots, world, observation, plans, path, future, retained, may, context⟩ :=
    runtime.bodySource i element location prepared
  exact runtime.afterBody bodySource typing roots world observation future retained may fuel flow bodyRun

def EachSourceChildSimulation (n : Nat) (cfg : Cfg) (results : List Ty) : View → Prop
  | .of place => TypedPlaceClaim n cfg results place
  | .val expr => TypedExprClaim n cfg results expr

theorem EachPlan.sourceSimulation {n : Nat} {cfg : Cfg} {env : Env} {initial : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    (plan : EachPlan source) (results : List Ty)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (childSimulation : EachSourceChildSimulation n cfg results view)
    (cx : GIR.FnCtx) (module : cx.cfg.mod = lower cfg.mod) (returned : cx.fn.results = results)
    (input output : LS) (frame : GIR.Frame) (point : GIR.Pt) (owner : Option GIR.ValueId)
    (irView : GIR.ValueId)
    (lowered : lowerEachSource view (lowerEnv cfg.mod env.vars results) input = ((owner, irView), output))
    (atPoint : input.pp = some point) (extension : ExtT output cx.fn.blocks)
    (related : Rel cfg env cx frame input) :
    SimEAt cx point frame (evalView (n + 1) cfg env view)
      (fun value pt' fr' => Post cfg env cx input frame output fr' pt'
        (EachSourceCells owner irView value)) initial := by
  have viewMetadata : SourceResults plan.viewSource.typingEnv plan.viewSource.rootsEnv results := by
    rw [plan.viewTyping, plan.viewRoots]
    exact metadata
  cases view with
  | of place =>
    obtain ⟨child, typing, roots⟩ := plan.viewSource.ofChild
    apply lowerEachSource_of_sim_at n cfg env cx _ input output frame point initial place owner irView
      lowered extension
    intro address middle hplace hext
    apply childSimulation env initial child
    · rw [typing, roots]; exact viewMetadata
    · exact hplace
    · exact atPoint
    · exact hext
    · exact related
    · exact module
    · exact returned
  | val expr =>
    obtain ⟨child, typing, roots, mutability, childType⟩ := plan.viewSource.valChild
    apply lowerEachSource_val_sim_at n cfg env cx _ input output frame point initial expr owner irView
      lowered extension
    intro value middle hexpr hext
    apply childSimulation env initial child
    · rw [typing, roots]; exact viewMetadata
    · exact hexpr
    · exact atPoint
    · exact hext
    · exact related
    · exact module
    · exact returned

theorem stmt_each_checked_flow_sim_at {n : Nat} {cfg : Cfg} {env : Env} {initial : St}
    {x : VarId} {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forEach x idx view byRef body origin) initial)
    (results : List Ty) (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (childSimulation : EachSourceChildSimulation n cfg results view)
    (blocks : ∀ fuel, fuel < n + 1 → ∀ loop pre pre',
      TypedBlockLoopSimulation fuel cfg results (some loop) pre pre' false body)
    (cx : GIR.FnCtx) (module : cx.cfg.mod = lower cfg.mod) (returned : cx.fn.results = results)
    (loop : Option LoopCtx) (input output : LS) (frame : GIR.Frame) (point : GIR.Pt)
    (mode : ∀ owner irView middle,
      lowerEachSource view (lowerEnv cfg.mod env.vars results) input = ((owner, irView), middle) →
      (regrowOf owner (lowerEnv cfg.mod env.vars results) middle).1 =
        eachSourceRegrows source.rootsEnv.access view)
    (lowered : lowerStmt loop (.forEach x idx view byRef body origin)
      (lowerEnv cfg.mod env.vars results) input = ((), output))
    (atPoint : input.pp = some point) (extension : ExtT output cx.fn.blocks)
    (related : Rel cfg env cx frame input) :
    SimEAt cx point frame (execStmt (n + 2) cfg env (.forEach x idx view byRef body origin) >>=
      prepareReturn env) (StmtFlowPost cfg env cx input frame output) initial := by
  obtain ⟨plan⟩ := source.eachPlan
  apply stmt_each_flow_sim_at (n + 1) cfg env cx _ input output frame point initial loop x idx view
    byRef body origin source.typingEnv source.typingAfter source.scope source.typingStart source.typingEnd
    source.frame.vars_t source.typed source.rootsEnv source.world plan.element
    (fun owner irView middle hlow hext => plan.sourceSimulation results metadata childSimulation cx
      module returned input middle frame point owner irView hlow atPoint hext related)
    (fun value state success => (plan.initial (n + 1) value success).aliases)
    (fun owner irView middle hlow _ _ _ => mode owner irView middle hlow)
    (fun value _ state => EachLoopState plan value state)
    (fun value i state => EachLoopState plan value state ∧
      LocTy state.store ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩ plan.element)
  · intro value state success
    exact plan.initial (n + 1) value success
  · intro value i state len nextState runtime lengthSuccess inside
    exact ⟨runtime, eachElement_typed_location runtime.typedView lengthSuccess inside⟩
  · intro value fuel smaller i state flow nextState allowed success
    cases flow with
    | normal v => exact allowed.1.afterIteration i fuel (.normal v) allowed.2 (Or.inl ⟨v, rfl⟩) success
    | cont => exact allowed.1.afterIteration i fuel .cont allowed.2 (Or.inr rfl) success
    | brk | ret v => trivial
  · intro value header base counter irView sampled hb owner binder indexBinder
    exact plan.blockCallback results metadata blocks cx module returned header base counter irView sampled hb owner value
  · exact lowered
  · exact atPoint
  · exact extension

end Goose.Lower
