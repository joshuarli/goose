import Goose.Lower.DemandGeneratedTransfer
import Goose.Lower.DemandSlotStorage

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedPlaceLeafDemand {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : PlaceSource cfg env place state) (map required : RetainedSsaMap) (cx : FnCtx)
    (before built : LS) (initial : GIR.Frame) (start : Pt) (id : ValueId) : DemandRuntimePoint → Prop
  | entry {operation : Op}
      (site : GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required
        ⟨source.path, .place, .entry⟩ start (.def id operation))
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.inputFuture map.values map.runs ⟨start, initial, state⟩) :
      GeneratedPlaceLeafDemand source map required cx before built initial start id ⟨start, initial, state⟩
  | exit {location : Loc}
      (post : Post cfg env cx before initial built (initial.set id (.val (.ref location)))
        (start.1, start.2 + 1) [(id, .val (.ref location))])
      (result : PlaceResult source location state)
      (bounded : map.Bounded built.vals.size)
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.outputFuture map.values map.runs
        ⟨(start.1, start.2 + 1), initial.set id (.val (.ref location)), state⟩) :
      GeneratedPlaceLeafDemand source map required cx before built initial start id
        ⟨(start.1, start.2 + 1), initial.set id (.val (.ref location)), state⟩

theorem accepted_generated_global_place_traversal {cfg : Cfg} {env : Env} {state : St} {global : GlobalId}
    (source : PlaceSource cfg env (.global global) state) {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.global global)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (bounded : map.Bounded before.vals.size)
    {frame : GIR.Frame} {point : Pt} (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (atPoint : before.pp = some point)
    (extended : ExtT (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (related : Rel cfg env cx frame before) :
    DemandUniformTraversal cx (GeneratedPlaceLeafDemand source map required cx before
      (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).2 frame point
      (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1) 1
      ⟨point, frame, state⟩
      ⟨(point.1, point.2 + 1), frame.set
        (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
        (.val (.ref ⟨.global global, []⟩)), state⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let built := lowerPlace (.global global) le before
  have emitted : emitDef (.globalAddr global) le before = built := rfl
  obtain ⟨post, instruction⟩ := Post.def_leaf (Post.init related atPoint) emitted extended (.val (.ref ⟨.global global, []⟩))
  have result := source.result 1 ⟨.global global, []⟩ (show evalPlace 1 cfg env (.global global) state = .ok ⟨.global global, []⟩ state from by simp only [evalPlace, pure_apply])
  have carried := realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl
  refine .next (.entry (.globalAddress_auto occurrence rows atPoint extended) coverage
    ⟨⟨before, atPoint, related⟩, source.frame, realized⟩) ?_
      (.done (.exit post result (bounded.mono post.mono) coverage ⟨⟨_, post.pp, post.rel⟩, result.frame, carried⟩))
  intro fuel
  apply DemandInstructionStep.definition instruction
  simp only [execOp, execPure, pure_apply]

theorem accepted_generated_slot_place_traversal {cfg : Cfg} {env : Env} {state : St} {slot : VarId}
    (source : PlaceSource cfg env (.var slot) state) {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.var slot)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (bounded : map.Bounded before.vals.size)
    {frame : GIR.Frame} {point : Pt} (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (atPoint : before.pp = some point)
    (extended : ExtT (lowerPlace (.var slot) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (related : Rel cfg env cx frame before) :
    ∃ location, DemandUniformTraversal cx (GeneratedPlaceLeafDemand source map required cx before
      (lowerPlace (.var slot) (lowerEnv cfg.mod env.vars results) before).2 frame point
      (lowerPlace (.var slot) (lowerEnv cfg.mod env.vars results) before).1) 1
      ⟨point, frame, state⟩
      ⟨(point.1, point.2 + 1), frame.set
        (lowerPlace (.var slot) (lowerEnv cfg.mod env.vars results) before).1
        (.val (.ref location)), state⟩ := by
  have typed := source.typed
  simp only [tyPlace] at typed
  obtain ⟨binding, next, checked, resultType⟩ := (st_bind_ok _ _ _ _).1 typed
  have visible := ((varOf_ok source.typingEnv slot source.typingStart (binding, next)).1 checked).1
  obtain ⟨binding, scope, old, variableAt, scopeAt, parameter, stored, shape⟩ := source.frame.bindings slot visible
  let location : Loc := ⟨.local env.act scope slot, []⟩
  let le := lowerEnv cfg.mod env.vars results
  let built := lowerPlace (.var slot) le before
  have emitted : emitDef (.slotAddr slot) le before = built := rfl
  obtain ⟨post, instruction⟩ := Post.def_leaf (Post.init related atPoint) emitted extended (.val (.ref location))
  have evaluated : evalPlace 1 cfg env (.var slot) state = .ok location state := by
    simp [evalPlace, rootOf, variableAt, scopeAt, location, bind_apply, pure_apply]
  have result := source.result 1 location evaluated
  have carried := realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl
  refine ⟨location, .next (.entry (.slotAddress_auto occurrence rows atPoint extended) coverage
    ⟨⟨before, atPoint, related⟩, source.frame, realized⟩) ?_
      (.done (.exit post result (bounded.mono post.mono) coverage ⟨⟨_, post.pp, post.rel⟩, result.frame, carried⟩))⟩
  intro fuel
  apply DemandInstructionStep.definition instruction
  simp only [execOp, execPure, slotRoot_eq related]
  simp [rootOf, variableAt, scopeAt, location, bind_apply, pure_apply]

end Goose.Lower
