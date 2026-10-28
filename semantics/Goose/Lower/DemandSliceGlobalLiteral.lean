import Goose.Lower.DemandSliceGlobalSnapshot
import Goose.Lower.DemandGeneratedSliceEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_global_literal_bound {cfg : Cfg} {env : Env} {state sampledState : St}
    {mutability : Mutability} {global : GlobalId} {origin : OriginId} {intType : IntTy} {number : Int}
    (source : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial frame : GIR.Frame} {start point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {sample : ViewVal} (viewed : evalView 2 cfg env (.of (.global global)) state = .ok sample sampledState)
    (viewPost : Post cfg env cx before initial (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).2
      frame point [((lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (extended : ExtT (lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (aliases : List RetainedAlias) (upper : BoundSource cfg env (.expr (.lit intType number)) sampledState),
      let le := lowerEnv cfg.mod env.vars results
      let view : View := .of (.global global)
      let operand : SliceOperands .omitted (.expr (.lit intType number)) := ⟨sample, .omitted, .expression (.lit intType number) intType number⟩
      let upperBefore := sliceUpperBefore view .omitted le before
      let upperId := (lowerExpr (.lit intType number) le upperBefore).1
      let endFrame := frame.set upperId (.val (.int intType number))
      let endPoint := (point.1, point.2 + 1)
      source.rootsEnv.access.aliasView (source.path ++ [0]) view = .ok aliases ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, sampledState⟩ ⟨endPoint, endFrame, sampledState⟩) ∧
      operand.PrefixEvaluated view 1 cfg env state sampledState ∧
      GeneratedDemandRows cfg.mod source.rootsEnv.access (.sliceUpper occurrence)
        (required.addRuns (lowerView view le before).1 aliases) ∧
      (map.addRuns (lowerView view le before).1 aliases).Covers
        (required.addRuns (lowerView view le before).1 aliases) ∧
      source.BoundChildAt upper 2 rfl ∧
      (map.addRuns (lowerView view le before).1 aliases).Admitted cfg.mod.profile upper.context.retained ∧
      (map.addRuns (lowerView view le before).1 aliases).Bounded (sliceEmissionBefore view .omitted (.expr (.lit intType number)) le before).vals.size ∧
      Post cfg env cx before initial (sliceEmissionBefore view .omitted (.expr (.lit intType number)) le before)
        endFrame endPoint (operand.cells view le before) ∧
      DemandFrameAt cfg env cx upper.world upper.typingEnv upper.rootsEnv upper.context.outputFuture
        (map.addRuns (lowerView view le before).1 aliases).values
        (map.addRuns (lowerView view le before).1 aliases).runs ⟨endPoint, endFrame, sampledState⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let view : View := .of (.global global)
  let operand : SliceOperands .omitted (.expr (.lit intType number)) := ⟨sample, .omitted, .expression (.lit intType number) intType number⟩
  let upperBefore := sliceUpperBefore view .omitted le before
  let upper := lowerExpr (.lit intType number) le upperBefore
  have lowerPost : Post cfg env cx (sliceLowerBefore view le before) frame upperBefore frame point [] := by
    simpa [upperBefore, sliceUpperBefore, sliceLowerBefore, view, le, lowerBound, pure_run] using Post.init viewPost.rel viewPost.pp
  have upperExtended : ExtT upper.2 cx.fn.blocks := by
    simpa [upper, upperBefore, sliceEmissionBefore, lowerBound, bind_run, pure_run] using generated_slice_upper_extended extended
  have emitted : emitDef (.constInt intType number) le upperBefore = (upper.1, upper.2) := rfl
  obtain ⟨upperPost, instruction⟩ := Post.def_leaf (Post.init lowerPost.rel lowerPost.pp) emitted upperExtended (.val (.int intType number))
  have upperPost' : Post cfg env cx upperBefore frame (sliceEmissionBefore view .omitted (.expr (.lit intType number)) le before)
      (frame.set upper.1 (.val (.int intType number))) (point.1, point.2 + 1)
      (operand.upperOperand.cells le upperBefore) := by
    simpa [operand, upper, sliceEmissionBefore, lowerBound, bind_run, pure_run, SliceBoundOperand.cells] using upperPost
  obtain ⟨aliases, query⟩ := source.sliceGlobalViewAlias
  have lowerDone : operand.lowerOperand.PrefixEvaluated 1 cfg env sampledState sampledState := rfl
  have upperDone : operand.upperOperand.PrefixEvaluated 1 cfg env sampledState sampledState := by
    simp [operand, SliceBoundOperand.PrefixEvaluated, evalExpr, pure_apply]
  obtain ⟨_, upperRows, covered, child, canonical, childAdmitted, childBounded, post, demanded⟩ :=
    accepted_generated_slice_operands source operand viewed lowerDone upperDone occurrence rows coverage admitted bounded realized
      query viewPost lowerPost upperPost'
  refine ⟨aliases, child, query, ?_, ?_, upperRows, covered, canonical, childAdmitted, childBounded, post, demanded⟩
  · intro fuel
    exact .definition instruction (by simp [execOp, execPure, pure_apply])
  · exact ⟨sampledState, sampledState, viewed, lowerDone, upperDone⟩

theorem accepted_generated_slice_global_literal_step {cfg : Cfg} {env : Env} {state sampledState after : St}
    {mutability : Mutability} {global : GlobalId} {origin : OriginId} {intType : IntTy} {number : Int}
    (source : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial frame : GIR.Frame} {start point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {sample : ViewVal} (viewed : evalView 2 cfg env (.of (.global global)) state = .ok sample sampledState)
    (viewPost : Post cfg env cx before initial (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).2
      frame point [((lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (extended : ExtT (lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : RuntimeStep cx.cfg cx.fn (point.1, point.2 + 1)
      (frame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
        (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results) before)).1 (.val (.int intType number)))
      sampledState next nextFrame after) :
    ∃ value, evalExpr 3 cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin) state = .ok value after ∧
      Post cfg env cx before initial
        (lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin)
          (lowerEnv cfg.mod env.vars results) before).2 nextFrame next
        [((lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin)
          (lowerEnv cfg.mod env.vars results) before).1, .val value)] := by
  obtain ⟨aliases, child, query, literalStep, evaluated, upperRows, covered, canonical, childAdmitted,
    childBounded, post, demanded⟩ :=
    accepted_generated_slice_global_literal_bound source occurrence rows coverage admitted bounded realized viewed viewPost extended
  have carried := demanded.operands
  rw [canonical.world] at carried
  obtain ⟨value, computed, afterEq, nextEq, frameEq, done, boundary, traversal, generated⟩ :=
    accepted_generated_slice_runtime_step source ⟨sample, .omitted, .expression (.lit intType number) intType number⟩ evaluated
      occurrence upperRows covered post childBounded carried extended step
  exact ⟨value, done, boundary.post⟩


theorem accepted_generated_slice_global_literal_stop {cfg : Cfg} {env : Env} {state sampledState after : St}
    {mutability : Mutability} {global : GlobalId} {origin : OriginId} {intType : IntTy} {number : Int}
    (source : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial frame : GIR.Frame} {start point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {sample : ViewVal} (viewed : evalView 2 cfg env (.of (.global global)) state = .ok sample sampledState)
    (viewPost : Post cfg env cx before initial (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).2
      frame point [((lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (extended : ExtT (lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel
      ⟨(point.1, point.2 + 1),
        frame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
          (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results) before)).1 (.val (.int intType number)),
        sampledState⟩ stop after) (nonTimeout : stop ≠ .timeout) :
    evalExpr 3 cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) origin) state = .stop stop after := by
  obtain ⟨aliases, child, query, literalStep, evaluated, upperRows, covered, canonical, childAdmitted,
    childBounded, post, demanded⟩ :=
    accepted_generated_slice_global_literal_bound source occurrence rows coverage admitted bounded realized viewed viewPost extended
  have carried := demanded.operands
  rw [canonical.world] at carried
  obtain ⟨_, _, done, _, _, _⟩ :=
    accepted_generated_slice_runtime_abort source ⟨sample, .omitted, .expression (.lit intType number) intType number⟩ evaluated
      occurrence upperRows covered post carried extended stopped nonTimeout
  exact done

#print axioms accepted_generated_slice_global_literal_stop

#print axioms accepted_generated_slice_global_literal_step

#print axioms accepted_generated_slice_global_literal_bound
end Goose.Lower
