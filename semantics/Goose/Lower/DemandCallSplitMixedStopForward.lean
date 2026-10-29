import Goose.Lower.DemandCallSplitReadStopForward
import Goose.Lower.DemandCallSplitMixedForward

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem CallArgumentsStopped.of_mapList {cfg : Cfg} {env : Env} {arguments : List Arg} {state after : St}
    {stop : Stop} {fuel : Nat}
    (evaluated : mapList (evalArg fuel cfg env) arguments state = .stop stop after)
    (nonTimeout : stop ≠ .timeout) : CallArgumentsStopped cfg env arguments state stop after := by
  induction arguments generalizing state after with
  | nil => simp [mapList, pure_apply] at evaluated
  | cons argument rest ih =>
    simp only [mapList, bind_apply] at evaluated
    cases head : evalArg fuel cfg env argument state with
    | stop reason stopped =>
      simp only [head, Res.stop.injEq] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact .head head nonTimeout
    | ok value middle =>
      simp only [head] at evaluated
      cases tail : mapList (evalArg fuel cfg env) rest middle with
      | stop reason stopped =>
        simp only [tail, Res.stop.injEq] at evaluated
        obtain ⟨rfl, rfl⟩ := evaluated
        exact .tail head (ih tail)
      | ok values final => simp [tail, pure_apply] at evaluated

#print axioms CallArgumentsStopped.of_mapList

theorem accepted_generated_call_split_mixed_stop_forward {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {rest : List Arg} (form : SplitMixedArguments source.rootsEnv.access rest)
    {index : Nat} (sources : ∀ fuel, ArgsSource fuel cfg env rest state)
    (canonical : ∀ fuel, (sources fuel).CallChildren source index)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell} {map : RetainedSsaMap}
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (coverage : map.Covers required) (shrink : cfg.mod.profile = .shrink)
    {stop : Stop} {after : St} (sourceStop : CallArgumentsStopped cfg env rest state stop after)
    (nonTimeout : stop ≠ .timeout)
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (bounded : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩)
    (checked : ∀ cell ∈ slots, cell.Checked source index initial)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (length targetFuel : Nat) (runtime : DemandRuntimePoint),
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ runtime ∧
      DemandInstructionStop cx targetFuel runtime stop after := by
  induction form generalizing index state initial start values slots with
  | nil => cases sourceStop
  | @read place rest readForm tail ih =>
    cases sourceEq : sources 0 with
    | cons head tailSource =>
      cases head with
      | byVal child =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        cases sourceStop with
        | head stopped headNonTimeout =>
          obtain ⟨middle, executed, targetStop⟩ := accepted_generated_call_split_read_stop_forward source found child readForm childCanonical
            occurrence rows coverage split realized input extended stopped nonTimeout
          exact ⟨1, 1, middle, executed, targetStop⟩
        | tail evaluated sourceTail =>
          have normalized := scalar_read_argument_success_fuel readForm evaluated
          obtain ⟨sameState, boundary, aliases, executed, boundaryState, post, nextRows, nextRealized,
            nextBounded, nextChecked, nextInput⟩ :=
            accepted_generated_call_split_read_forward source found child readForm childCanonical occurrence rows coverage split
              realized admitted bounded input extended shrink checked normalized
          cases sameState
          cases boundary with
          | mk point frame nextState =>
            simp only at boundaryState
            subst nextState
            let nextSources := ArgsSource.afterHead sources normalized
            have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
              intro fuel
              exact ArgsSource.afterHead_callChildren source sources canonical normalized fuel
            obtain ⟨length, targetFuel, runtime, tailSteps, targetStop⟩ :=
              ih nextSources nextCanonical sourceTail nextRows nextInput nextBounded nextRealized nextChecked
            exact ⟨2 + length, targetFuel, runtime, executed.append tailSteps, targetStop⟩
  | @literal expression value operation rest literal tail ih =>
    cases sourceEq : sources 0 with
    | cons head tailSource =>
      cases head with
      | byVal child =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        obtain ⟨point, frame, evaluated, executed, post, nextRows, nextRealized, nextBounded, nextChecked, nextInput⟩ :=
          accepted_generated_call_split_scalar_literal_stage source literal found child childCanonical admitted split input bounded realized checked extended
        cases sourceStop with
        | head stopped headNonTimeout => exact (evalArg_success_stop_disjoint evaluated stopped nonTimeout).elim
        | tail sourceEvaluated sourceTail =>
          obtain ⟨_, sameState⟩ := evalArg_success_unique sourceEvaluated evaluated
          subst_vars
          let nextSources := ArgsSource.afterHead sources evaluated
          have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
            intro fuel
            exact ArgsSource.afterHead_callChildren source sources canonical evaluated fuel
          obtain ⟨length, targetFuel, runtime, tailSteps, targetStop⟩ :=
            ih nextSources nextCanonical sourceTail nextRows nextInput nextBounded nextRealized nextChecked
          exact ⟨1 + length, targetFuel, runtime, executed.append tailSteps, targetStop⟩
  | @reference borrow slot mutability element rest type tail ih =>
    cases sourceEq : sources 0 with
    | cons head tailSource =>
      cases head with
      | byRef _ child target =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        have metadata := childCanonical
        obtain ⟨_, _, _, _, roots, _⟩ := metadata
        have accessType := tyPlace_accessType (child.frame.mod_t.trans child.frame.mod_p.symm)
          (child.frame.vars_t.trans child.frame.vars_p.symm) child.typed
        rw [roots, type] at accessType
        have childType : child.ty = .slice mutability element := (Option.some.inj accessType).symm
        obtain ⟨location, consumed, point, frame, cell, evaluated, executed, post, nextRows, nextBounded, nextRealized, nextChecked, nextInput⟩ :=
          accepted_generated_call_slice_sequence_stage source found child target childCanonical childType occurrence rows split input bounded realized checked extended
        cases sourceStop with
        | head stopped headNonTimeout => exact (evalArg_success_stop_disjoint evaluated stopped nonTimeout).elim
        | tail sourceEvaluated sourceTail =>
          obtain ⟨_, sameState⟩ := evalArg_success_unique sourceEvaluated evaluated
          subst_vars
          let nextSources := ArgsSource.afterHead sources evaluated
          have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
            intro fuel
            exact ArgsSource.afterHead_callChildren source sources canonical evaluated fuel
          obtain ⟨length, targetFuel, runtime, tailSteps, targetStop⟩ :=
            ih nextSources nextCanonical sourceTail nextRows nextInput nextBounded nextRealized nextChecked
          exact ⟨consumed + length, targetFuel, runtime, executed.append tailSteps, targetStop⟩

#print axioms accepted_generated_call_split_mixed_stop_forward
end Goose.Lower
