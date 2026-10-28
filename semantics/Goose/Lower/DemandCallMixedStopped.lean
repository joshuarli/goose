import Goose.Lower.DemandCallValueSequence
import Goose.Lower.DemandCallReferenceStoppedStage

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

def CallReferenceSupported (access : AccessEnv) (place : Place) : Prop :=
  (∃ ty, access.placeType? place = some ty ∧ ty.refTarget = true) ∨ ∃ global, place = .global global

theorem CallReferenceSupported.target {access : AccessEnv} {place : Place} {ty : Ty} {mutable : Bool}
    (supported : CallReferenceSupported access place) (typeAt : access.placeType? place = some ty)
    (allowed : ty.refTarget = true ∨ (ty.isSlice = true ∧ mutable = true ∧ place.sliceArg = true)) : ty.refTarget = true := by
  rcases supported with ⟨other, otherAt, target⟩ | ⟨global, rfl⟩
  · have same : ty = other := Option.some.inj (typeAt.symm.trans otherAt)
    simpa [same] using target
  · rcases allowed with target | ⟨_, _, impossible⟩
    · exact target
    · simp [Place.sliceArg, Place.derefVar?] at impossible

#print axioms CallReferenceSupported.target

inductive CallMixedStoppedArguments (access : AccessEnv) : List Arg → Prop
  | nil : CallMixedStoppedArguments access []
  | value {expression : Expr} {rest : List Arg} (form : ReadStoppedExpression expression)
      (tail : CallMixedStoppedArguments access rest) : CallMixedStoppedArguments access (.byVal expression :: rest)
  | reference {mutability : Mutability} {place : Place} {rest : List Arg} (form : ScalarReadPlace place)
      (type : CallReferenceSupported access place)
      (tail : CallMixedStoppedArguments access rest) : CallMixedStoppedArguments access (.byRef mutability place :: rest)

theorem accepted_generated_call_mixed_stopped_suffix {cfg : Cfg} {env : Env} {initialState : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (shrink : cfg.mod.profile = .shrink) {rest : List Arg} (form : CallMixedStoppedArguments source.rootsEnv.access rest)
    {index : Nat} {state : St} (sources : ∀ fuel, ArgsSource fuel cfg env rest state)
    (canonical : ∀ fuel, (sources fuel).CallChildren source index)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {initial : GIR.Frame} {start : Pt}
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {fuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    CallValueStoppedPrefix source cx results before loop map index rest ⟨start, initial, state⟩ taken reached stop after := by
  induction form generalizing index state initial start prior taken reached with
  | nil =>
    apply CallValueStoppedPrefix.complete (consumed := 0) (remaining := taken) (boundary := ⟨start, initial, state⟩)
      (values := []) (prior := prior) (by omega) (.zero _) steps (.nil state)
    · simpa using tracked
    · simpa using bounded
    · exact realized
    · simpa using input
  | @value expression rest headForm tailForm ih =>
    cases sourceEq : sources 0 with
    | cons head tail =>
      cases head with
      | byVal child =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        have stage := accepted_generated_call_value_stage_stopped source found child childCanonical selected owned occurrence rows tracked
          coverage admitted bounded realized input extended headForm steps stopped nonTimeout
        cases stage with
        | aborted sourceFuel evaluated =>
          apply CallValueStoppedPrefix.aborted
          exact .head (fuel := sourceFuel + 1) (by simpa [evalArg] using evaluated) nonTimeout
        | @complete sourceFuel consumed remaining boundary value count executed residual evaluated post =>
          have done : evalArg (sourceFuel + 1) cfg env (.byVal expression) state = .ok value boundary.state := by
            simpa [evalArg] using evaluated
          obtain ⟨aliases, query⟩ := source.callArgumentAlias found shrink
          obtain ⟨nextTracked, nextRealized, nextBounded⟩ :=
            accepted_generated_call_value_finish source found child childCanonical tracked query post
          have nextInput := accepted_generated_call_value_next_input source found child input post
          let nextSources := ArgsSource.afterHead sources done
          have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
            intro fuel
            exact ArgsSource.afterHead_callChildren source sources canonical done fuel
          have next := ih nextSources nextCanonical nextTracked nextBounded nextRealized nextInput residual stopped
          cases next with
          | aborted trace => exact .aborted (.tail done trace)
          | @complete consumedTail remainingTail final values finalPrior tailCount tailExecuted tailResidual trace finalTracked finalBounded finalRealized finalInput =>
            apply CallValueStoppedPrefix.complete (consumed := consumed + consumedTail) (remaining := remainingTail)
              (boundary := final) (values := value :: values) (prior := finalPrior) (by omega)
              (executed.append tailExecuted) tailResidual (.cons done trace)
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalTracked
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
            · exact finalRealized
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput
  | @reference mutability place rest headForm typeFact tailForm ih =>
    cases sourceEq : sources 0 with
    | cons head tail =>
      cases head with
      | byRef _ child allowed =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        obtain ⟨plans, path, world, typing, roots, childContext⟩ := childCanonical
        have accessType := tyPlace_accessType (child.frame.mod_t.trans child.frame.mod_p.symm)
          (child.frame.vars_t.trans child.frame.vars_p.symm) child.typed
        rw [roots] at accessType
        have target : child.ty.refTarget = true := CallReferenceSupported.target typeFact accessType allowed
        have childCanonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext
            source.world source.typingEnv source.rootsEnv (callArgContext source.context index (.byRef mutability place) found) :=
          ⟨plans, path, world, typing, roots, childContext⟩
        obtain ⟨location, consumed, remaining, point, frame, aliases, count, executed, residual,
          done, finalPost, nextTracked, nextRealized, nextBounded, nextInput⟩ :=
          accepted_generated_call_reference_stopped_stage source found child target childCanonical headForm occurrence rows tracked
            bounded realized input extended steps stopped nonTimeout
        let nextSources := ArgsSource.afterHead sources done
        have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
          intro fuel
          exact ArgsSource.afterHead_callChildren source sources canonical done fuel
        have next := ih nextSources nextCanonical nextTracked nextBounded nextRealized nextInput residual stopped
        cases next with
        | aborted trace => exact .aborted (.tail done trace)
        | @complete consumedTail remainingTail final values finalPrior tailCount tailExecuted tailResidual trace finalTracked finalBounded finalRealized finalInput =>
          apply CallValueStoppedPrefix.complete (consumed := consumed + consumedTail) (remaining := remainingTail)
            (boundary := final) (values := .ref location :: values) (prior := finalPrior) (by omega)
            (executed.append tailExecuted) tailResidual (.cons done trace)
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalTracked
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
          · exact finalRealized
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput

theorem accepted_generated_call_mixed_stopped {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (shrink : cfg.mod.profile = .shrink) (form : CallMixedStoppedArguments source.rootsEnv.access arguments)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {fuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    CallValueStoppedPrefix source cx results before loop map 0 arguments ⟨start, initial, state⟩ taken reached stop after := by
  let sources := fun fuel => Classical.choose (source.callArgsCanonical fuel results input.metadata)
  have canonical : ∀ fuel, (sources fuel).CallChildren source 0 := by
    intro fuel
    exact (Classical.choose_spec (source.callArgsCanonical fuel results input.metadata)).2
  have tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take 0)
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).1 [] := by
    simpa [lowerArgs, pure_run] using (GeneratedCallArgumentRows.nil (access := source.rootsEnv.access) (path := source.path) 0)
  apply accepted_generated_call_mixed_stopped_suffix source selected owned occurrence rows coverage admitted extended shrink form sources canonical tracked
  · simpa [lowerArgs, pure_run] using bounded
  · simpa using realized
  · simpa [lowerArgs, pure_run] using input
  · exact steps
  · exact stopped
  · exact nonTimeout

#print axioms accepted_generated_call_mixed_stopped
end Goose.Lower
