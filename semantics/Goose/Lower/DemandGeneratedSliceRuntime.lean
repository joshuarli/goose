import Goose.Lower.DemandGeneratedSlice

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive SliceDemandCursor {cfg : Cfg} {env : Env} {mutability : Mutability} {view : View}
    {lower upper : Bound} {origin : OriginId} {state : St}
    (source : ExprSource cfg env (.slice mutability view lower upper origin) state)
    (map required : RetainedSsaMap) (cx : FnCtx) : DemandRuntimePoint → Prop where
  | upper {upperState : St} {child : BoundSource cfg env upper upperState} {runtime : DemandRuntimePoint}
      (canonical : source.BoundChildAt child 2 rfl) {instruction : Inst}
      (site : GeneratedSliceInstruction cfg.mod source.rootsEnv.access cx.fn required
        ⟨source.path ++ [2], .bound, .exit⟩ runtime.point instruction)
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs runtime) : SliceDemandCursor source map required cx runtime
  | result {runtime : DemandRuntimePoint} (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs runtime) : SliceDemandCursor source map required cx runtime

theorem SliceDemandCursor.carried {cfg : Cfg} {env : Env} {mutability : Mutability} {view : View}
    {lower upper : Bound} {origin : OriginId} {state : St}
    {source : ExprSource cfg env (.slice mutability view lower upper origin) state}
    {map required : RetainedSsaMap} {cx : FnCtx} {runtime : DemandRuntimePoint}
    (cursor : SliceDemandCursor source map required cx runtime) : map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | upper canonical site coverage demanded =>
    simpa only [RetainedSsaMap.Realizes, canonical.world] using demanded.operands
  | result coverage demanded => exact demanded.operands

theorem SliceOperands.canonical_upper {cfg : Cfg} {env : Env} {mutability : Mutability} {view : View}
    {lower upper : Bound} {origin : OriginId} {state intermediate : St}
    (operands : SliceOperands lower upper) (source : ExprSource cfg env (.slice mutability view lower upper origin) state)
    {fuel : Nat} (evaluated : operands.PrefixEvaluated view fuel cfg env state intermediate) :
    ∃ (upperState : St) (child : BoundSource cfg env upper upperState), source.BoundChildAt child 2 rfl ∧
      Core.Sound.Frame cfg.mod child.world child.typingEnv child.rootsEnv env intermediate child.context.outputFuture := by
  obtain ⟨afterView, afterLower, viewed, low, high⟩ := evaluated
  obtain ⟨sampled, _, _, _, next⟩ := source.sliceChildren mutability origin
  obtain ⟨lowSource, _, _, _, nextUpper⟩ := next (fuel + 1) operands.sample afterView viewed
  have lowerDone := operands.lowerOperand.source_evaluated low (length := operands.sample.len) (default := 0)
  obtain ⟨highSource, _, _, canonical⟩ :=
    nextUpper (fuel + 1) (operands.lowerOperand.value operands.sample.len 0) afterLower lowerDone
  have upperDone := operands.upperOperand.source_evaluated high (length := operands.sample.len) (default := operands.sample.len)
  exact ⟨afterLower, highSource, canonical,
    (highSource.result (fuel + 1) operands.sample.len operands.sample.len
      (operands.upperOperand.value operands.sample.len operands.sample.len) upperDone).frame⟩

theorem accepted_generated_slice_runtime_step {cfg : Cfg} {env : Env} {mutability : Mutability} {view : View}
    {lower upper : Bound} {origin : OriginId} {state intermediate after : St}
    (source : ExprSource cfg env (.slice mutability view lower upper origin) state)
    (operands : SliceOperands lower upper) {fuel : Nat}
    (evaluated : operands.PrefixEvaluated view fuel cfg env state intermediate)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path
      (.expression (.slice mutability view lower upper origin)) before)
    {required map : RetainedSsaMap}
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access (.sliceUpper occurrence) required)
    (coverage : map.Covers required) {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial (sliceEmissionBefore view lower upper le before) frame point
      (operands.cells view le before))
    (bounded : map.Bounded (sliceEmissionBefore view lower upper le before).vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, intermediate⟩)
    (extended : ExtT (lowerExpr (.slice mutability view lower upper origin) le before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame intermediate next nextFrame after) :
    ∃ value, operands.compute origin = .ok value ∧ after = intermediate ∧ next = (point.1, point.2 + 1) ∧
      nextFrame = frame.set (lowerExpr (.slice mutability view lower upper origin) le before).1 (.val value) ∧
      evalExpr (fuel + 2) cfg env (.slice mutability view lower upper origin) state = .ok value after ∧
      ExpressionDemandBoundary source map cx before initial (lowerExpr (.slice mutability view lower upper origin) le before).2
        (lowerExpr (.slice mutability view lower upper origin) le before).1 value after next nextFrame ∧
      DemandUniformTraversal cx (SliceDemandCursor source map required cx) 1
        ⟨point, frame, intermediate⟩ ⟨next, nextFrame, after⟩ ∧
      ∀ aliases, source.rootsEnv.access.aliasExpr source.path (.slice mutability view lower upper origin) = .ok aliases →
        (map.addValues (lowerExpr (.slice mutability view lower upper origin) le before).1 aliases).Realizes
          cfg.mod source.world env ⟨next, nextFrame, after⟩ := by
  have site : GeneratedSliceInstruction cfg.mod source.rootsEnv.access cx.fn required
      ⟨source.path ++ [2], .bound, .exit⟩ point
      (.def (lowerExpr (.slice mutability view lower upper origin) le before).1
        (sliceOperation mutability view lower upper origin le before)) :=
    .checked occurrence rows post.pp extended
  obtain ⟨upperState, child, canonical, childFrame⟩ := operands.canonical_upper source evaluated
  have cursor : SliceDemandCursor source map required cx ⟨point, frame, intermediate⟩ :=
    .upper canonical site coverage ⟨⟨_, post.pp, post.rel⟩, childFrame,
      by simpa only [RetainedSsaMap.Realizes, canonical.world] using realized⟩
  cases step with
  | define instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    rw [operands.instruction_decompose mutability view origin post.has] at execution
    cases computed : operands.compute origin with
    | error stop => simp only [computed] at execution; cases execution
    | ok value =>
      simp only [computed] at execution
      obtain ⟨rfl, stateEq⟩ := Res.ok.inj execution
      subst after
      have done : evalExpr (fuel + 2) cfg env (.slice mutability view lower upper origin) state = .ok value intermediate := by
        rw [operands.source_decompose mutability view origin evaluated, computed]
      let built := lowerExpr (.slice mutability view lower upper origin) le before
      have emitted : emitDef (sliceOperation mutability view lower upper origin le before) le
          (sliceEmissionBefore view lower upper le before) = (built.1, built.2) := by
        simp only [built, lowerExpr_slice_run]
      obtain ⟨wholePost, _⟩ := Post.def_leaf post emitted extended (.val value)
      obtain ⟨leafPost, _⟩ := Post.def_leaf (Post.init post.rel post.pp) emitted extended (.val value)
      have result := source.result (fuel + 2) value done
      have carried : map.Realizes cfg.mod source.world env
          ⟨(point.1, point.2 + 1), frame.set built.1 (.val value), intermediate⟩ :=
        realized.retained leafPost.same bounded.1 bounded.2 RetainsAliases.refl
      have demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
          map.values map.runs ⟨(point.1, point.2 + 1), frame.set built.1 (.val value), intermediate⟩ :=
        ⟨⟨_, wholePost.pp, wholePost.rel⟩, result.frame, carried⟩
      have boundary : ExpressionDemandBoundary source map cx before initial built.2 built.1 value intermediate
          (point.1, point.2 + 1) (frame.set built.1 (.val value)) :=
        ⟨wholePost, demanded, bounded.mono leafPost.mono,
          ValueAliasAt.of_post wholePost (v := value) (by simp) ⟨result.typed, result.rooted⟩,
          fun aliases query alias member => result.generated_value wholePost query member⟩
      refine ⟨value, rfl, rfl, rfl, rfl, done, boundary,
        .next cursor ?_ (.done (.result coverage demanded)), ?_⟩
      · intro targetFuel
        exact .definition site.instruction (by rw [operands.instruction_decompose mutability view origin post.has, computed])
      · intro aliases query
        exact RetainedSsaMap.addValues_realizes carried
          (fun alias member => result.generated_value wholePost query member)
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

theorem accepted_generated_slice_runtime_abort {cfg : Cfg} {env : Env} {mutability : Mutability} {view : View}
    {lower upper : Bound} {origin : OriginId} {state intermediate after : St}
    (source : ExprSource cfg env (.slice mutability view lower upper origin) state)
    (operands : SliceOperands lower upper) {fuel : Nat}
    (evaluated : operands.PrefixEvaluated view fuel cfg env state intermediate)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path
      (.expression (.slice mutability view lower upper origin)) before)
    {required map : RetainedSsaMap}
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access (.sliceUpper occurrence) required)
    (coverage : map.Covers required) {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial (sliceEmissionBefore view lower upper le before) frame point
      (operands.cells view le before))
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, intermediate⟩)
    (extended : ExtT (lowerExpr (.slice mutability view lower upper origin) le before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, intermediate⟩ stop after)
    (nonTimeout : stop ≠ .timeout) :
    stop = .abort .sliceOob origin ∧ after = intermediate ∧
      evalExpr (fuel + 2) cfg env (.slice mutability view lower upper origin) state = .stop stop after ∧
      map.Covers required ∧ map.Realizes cfg.mod source.world env ⟨point, frame, after⟩ ∧
      DemandStoppedTraversal cx (SliceDemandCursor source map required cx) 0 targetFuel
        ⟨point, frame, intermediate⟩ stop after := by
  have site : GeneratedSliceInstruction cfg.mod source.rootsEnv.access cx.fn required
      ⟨source.path ++ [2], .bound, .exit⟩ point
      (.def (lowerExpr (.slice mutability view lower upper origin) le before).1
        (sliceOperation mutability view lower upper origin le before)) :=
    .checked occurrence rows post.pp extended
  obtain ⟨upperState, child, canonical, childFrame⟩ := operands.canonical_upper source evaluated
  have cursor : SliceDemandCursor source map required cx ⟨point, frame, intermediate⟩ :=
    .upper canonical site coverage ⟨⟨_, post.pp, post.rel⟩, childFrame,
      by simpa only [RetainedSsaMap.Realizes, canonical.world] using realized⟩
  cases stopped with
  | timeout => exact (nonTimeout rfl).elim
  | definition instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    rw [operands.instruction_decompose mutability view origin post.has] at execution
    cases computed : operands.compute origin with
    | ok value => simp only [computed] at execution; cases execution
    | error actual =>
      simp only [computed] at execution
      obtain ⟨rfl, stateEq⟩ := Res.stop.inj execution
      subst after
      have abortEq : actual = .abort .sliceOob origin := by
        unfold SliceOperands.compute at computed
        dsimp only at computed
        split at computed
        · cases computed
        · exact (Except.error.inj computed).symm
      refine ⟨abortEq, rfl, ?_, coverage, realized, ⟨_, .done _ cursor, ?_⟩⟩
      · rw [operands.source_decompose mutability view origin evaluated, computed]
      · simpa only [Nat.sub_zero] using
          (DemandInstructionStop.definition site.instruction (by
            rw [operands.instruction_decompose mutability view origin post.has, computed]))
  | effect instruction execution => cases site.instruction.symm.trans instruction

end Goose.Lower
