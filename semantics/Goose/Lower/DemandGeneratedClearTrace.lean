import Goose.Lower.DemandGeneratedClear
import Goose.Lower.DemandGeneratedPlaceLeaves

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedClearDemand {cfg : Cfg} {env : Env} {global : GlobalId} {origin : OriginId} {state : St}
    (source : StmtSource cfg env (.clear (.global global) origin) state)
    (map required : RetainedSsaMap) (cx : FnCtx) (before addressed built : LS) (initial : GIR.Frame)
    (start : Pt) (address : ValueId) : DemandRuntimePoint → Prop
  | address {child : PlaceSource cfg env (.global global) state}
      (canonical : source.PlaceChildAt child rfl)
      (site : GeneratedDemandInstruction cfg.mod child.rootsEnv.access cx.fn required
        ⟨child.path, .place, .entry⟩ start (.def address (.globalAddr global)))
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        map.values map.runs ⟨start, initial, state⟩) :
      GeneratedClearDemand source map required cx before addressed built initial start address ⟨start, initial, state⟩
  | clear {child : PlaceSource cfg env (.global global) state} {frame : GIR.Frame} {point : Pt} {location : Loc}
      (canonical : source.PlaceChildAt child rfl)
      (site : GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required
        ⟨source.path ++ [0], .place, .exit⟩ point (.eff (.clear address (some origin))))
      (coverage : map.Covers required)
      (post : Post cfg env cx before initial addressed frame point [(address, .val (.ref location))])
      (result : PlaceResult child location state)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, state⟩) :
      GeneratedClearDemand source map required cx before addressed built initial start address ⟨point, frame, state⟩
  | exit {after : St} {point : Pt} {frame : GIR.Frame}
      (post : Post cfg env cx before initial built frame point [])
      (result : StmtResult source (.normal .unit) after)
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨point, frame, after⟩) :
      GeneratedClearDemand source map required cx before addressed built initial start address ⟨point, frame, after⟩

theorem GeneratedClearDemand.realizes {cfg : Cfg} {env : Env} {global : GlobalId} {origin : OriginId} {state : St}
    {source : StmtSource cfg env (.clear (.global global) origin) state}
    {map required : RetainedSsaMap} {cx : FnCtx} {before addressed built : LS} {initial : GIR.Frame}
    {start : Pt} {address : ValueId} {runtime : DemandRuntimePoint}
    (valid : GeneratedClearDemand source map required cx before addressed built initial start address runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases valid with
  | address canonical site coverage demanded =>
    simpa only [RetainedSsaMap.Realizes, canonical.world] using demanded.operands
  | clear canonical site coverage post result demanded =>
    simpa only [RetainedSsaMap.Realizes, canonical.world] using demanded.operands
  | exit post result coverage demanded => exact demanded.operands

theorem accepted_generated_global_clear_traversal {cfg : Cfg} {env : Env} {global : GlobalId} {origin : OriginId}
    {state after : St} (source : StmtSource cfg env (.clear (.global global) origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.clear (.global global) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (atPoint : before.pp = some point) (related : Rel cfg env cx frame before)
    (extended : ExtT (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (truncated : truncateLoc ⟨.global global, []⟩ 0 state = .ok () after) :
    ∃ finalPoint finalFrame,
      DemandUniformTraversal cx (GeneratedClearDemand source map required cx before
        (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).2
        (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results) before).2 frame point
        (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1) 2
        ⟨point, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      Post cfg env cx before frame
        (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results) before).2 finalFrame finalPoint [] ∧
      StmtResult source (.normal .unit) after ∧
      map.Bounded (lowerStmt loop (.clear (.global global) origin) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      map.Realizes cfg.mod source.world env ⟨finalPoint, finalFrame, after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let address := (lowerPlace (.global global) le before).1
  let addressed := (lowerPlace (.global global) le before).2
  let middleFrame := frame.set address (.val (.ref ⟨.global global, []⟩))
  let middlePoint : Pt := (point.1, point.2 + 1)
  let built := (lowerStmt loop (.clear (.global global) origin) le before).2
  obtain ⟨child, _, _, rootsEq, _, _, _, _, canonical⟩ := source.clearChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place (.global global)) before := by
    rw [canonical.path]
    exact .clearPlace occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.clearPlace occurrence) required := .clearPlace rows
    simpa only [rootsEq, canonical.path] using inherited
  have childRealized : map.Realizes cfg.mod child.world env ⟨point, frame, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  have first := accepted_generated_global_place_traversal child childOccurrence childRows coverage bounded childRealized
    atPoint (generated_clear_place_extended extended) related
  have emitted : emitDef (.globalAddr global) le before = (lowerPlace (.global global) le before) := rfl
  have initialPost : Post cfg env cx before frame addressed middleFrame middlePoint
      [(address, .val (.ref ⟨.global global, []⟩))] :=
    (Post.def_leaf (Post.init related atPoint) emitted (generated_clear_place_extended extended)
      (.val (.ref ⟨.global global, []⟩))).1
  have clearSite := GeneratedDemandInstruction.clear_auto occurrence rows initialPost.pp extended
  have cell := initialPost.has (address, .val (.ref ⟨.global global, []⟩)) (by simp)
  have effectRun : execEff cx.fn middleFrame (.clear address (some origin)) state = .ok middleFrame after := by
    simp only [execEff, getVal_of cell, expectRef, bind_apply, pure_apply, truncated]
  have runtime : Evidence.RuntimeStep cx.cfg cx.fn middlePoint middleFrame state
      (middlePoint.1, middlePoint.2 + 1) middleFrame after := .effect clearSite.instruction effectRun
  obtain ⟨_, _, _, _, _, _, _, evaluated, finalPost, result, finalBounded, demanded⟩ :=
    accepted_generated_clear_runtime_step source occurrence rows coverage admitted bounded realized
      (show evalPlace 1 cfg env (.global global) state = .ok ⟨.global global, []⟩ state from by simp only [evalPlace, pure_apply])
      initialPost extended runtime
  have firstMapped : DemandUniformTraversal cx
      (GeneratedClearDemand source map required cx before addressed built frame point address) 1
      ⟨point, frame, state⟩ ⟨middlePoint, middleFrame, state⟩ := by
    apply first.mono
    intro reached valid
    cases valid with
    | entry site coverage demanded =>
      have actualSite := GeneratedDemandInstruction.globalAddress_auto childOccurrence childRows atPoint
        (generated_clear_place_extended extended)
      exact .address canonical actualSite coverage demanded
    | exit post placeResult bounded coverage demanded =>
      exact .clear canonical (.clear_auto occurrence rows post.pp extended) coverage post placeResult demanded
  have last : DemandUniformTraversal cx
      (GeneratedClearDemand source map required cx before addressed built frame point address) 1
      ⟨middlePoint, middleFrame, state⟩ ⟨(middlePoint.1, middlePoint.2 + 1), middleFrame, after⟩ := by
    refine .next ?_ (fun fuel => .effect clearSite.instruction effectRun) (.done (.exit finalPost result coverage demanded))
    have valid := firstMapped.last_valid
    exact valid
  exact ⟨_, _, firstMapped.append last, finalPost, result, finalBounded, demanded.operands⟩

end Goose.Lower
