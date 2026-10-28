import Goose.Lower.DemandBooleanNext
import Goose.Lower.DemandCallMixedPrefix
import Goose.Lower.DemandCallArgumentCells

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive CallMixedPrefixCells {cfg : Cfg} {env : Env} {initialState : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    (cx : FnCtx) (results : List Ty) (before : LS) (loop : Option LoopCtx) (map : RetainedSsaMap) (callFrame : GIR.Frame)
    (previousValues : List Val) (index : Nat) (rest : List Arg) (start : DemandRuntimePoint) (taken : Nat)
    (reached : DemandRuntimePoint) : Prop
  | interior {required : RetainedSsaMap} (cursor : CallMixedPrefix source cx results before loop map required index rest start taken reached)
      (realized : map.Realizes cfg.mod source.world env reached)
      (progress : (∃ id op, instAt cx.fn reached.point = some (.def id op)) ∨
        ∃ next, ∀ fuel, DemandInstructionStep cx fuel reached next) :
      CallMixedPrefixCells source cx results before loop map callFrame previousValues index rest start taken reached
  | complete {consumed remaining : Nat} {boundary : DemandRuntimePoint} {values : List Val}
      {prior : List (ValueId × RetainedAlias)}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed start boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (trace : CallArgumentsDone cfg env rest start.state values boundary.state)
      (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0
        (arguments.take (index + rest.length))
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).1 prior)
      (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
      (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env boundary)
      (wholePost : Post cfg env cx before callFrame
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2
        boundary.frame boundary.point [])
      (cells : CallArgumentCells
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).1
        (previousValues ++ values)
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size boundary.frame)
      (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2 boundary.frame boundary.point) :
      CallMixedPrefixCells source cx results before loop map callFrame previousValues index rest start taken reached

theorem accepted_generated_call_mixed_prefix_cells_suffix {cfg : Cfg} {env : Env} {initialState : St}
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
    (shrink : cfg.mod.profile = .shrink) {rest : List Arg} (form : CallMixedArguments source.rootsEnv.access rest)
    {index : Nat} {state : St} (sources : ∀ fuel, ArgsSource fuel cfg env rest state)
    (canonical : ∀ fuel, (sources fuel).CallChildren source index)
    {previousValues : List Val} {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {initial callFrame : GIR.Frame} {start : Pt}
    (wholePost : Post cfg env cx before callFrame
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start [])
    (cells : CallArgumentCells (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1
      previousValues (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size initial)
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    :
    CallMixedPrefixCells source cx results before loop map callFrame previousValues index rest ⟨start, initial, state⟩ taken reached := by
  induction form generalizing index state initial start prior previousValues taken reached with
  | nil =>
    apply CallMixedPrefixCells.complete (consumed := 0) (remaining := taken) (boundary := ⟨start, initial, state⟩)
      (values := []) (prior := prior) (by omega) (.zero _) steps (.nil state)
    · simpa using tracked
    · simpa using bounded
    · exact realized
    · simpa using wholePost
    · simpa using cells
    · simpa using input
  | @value expression rest headForm tailForm ih =>
    cases sourceEq : sources 0 with
    | cons head tail =>
      cases head with
      | byVal child =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        have stage := accepted_generated_call_value_stage source found child childCanonical selected owned occurrence rows tracked
          coverage admitted bounded realized input extended headForm steps
        cases stage with
        | interior cursor =>
          have carried := cursor.demanded.carried
          have world : child.world = source.world := childCanonical.2.2.1
          have sourceCarried : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env reached := by
            simpa only [RetainedSsaMap.Realizes, world] using carried
          have current : map.Realizes cfg.mod source.world env reached :=
            ⟨fun cell member => sourceCarried.1 cell (List.mem_append_right prior member), sourceCarried.2⟩
          exact .interior (.interior found child childCanonical cursor) current cursor.progress
        | @complete sourceFuel consumed remaining boundary value count executed residual evaluated post =>
          have done : evalArg (sourceFuel + 1) cfg env (.byVal expression) state = .ok value boundary.state := by
            simpa [evalArg] using evaluated
          obtain ⟨aliases, query⟩ := source.callArgumentAlias found shrink
          obtain ⟨nextTracked, nextRealized, nextBounded⟩ :=
            accepted_generated_call_value_finish source found child childCanonical tracked query post
          have nextInput := accepted_generated_call_value_next_input source found child input post
          have valuePost : Post cfg env cx (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
              (lowerArg (.byVal expression) (lowerEnv cfg.mod env.vars results)
                (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 boundary.frame boundary.point
              [((lowerArg (.byVal expression) (lowerEnv cfg.mod env.vars results)
                (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1, .val value)] := by
            simpa only [lowerArg] using post.post
          have nextCells := cells.next found valuePost
          have nextPost : Post cfg env cx before callFrame
              (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2
              boundary.frame boundary.point [] := by
            have combined := wholePost.comp valuePost
            have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byVal expression] := by
              rw [List.take_add_one, found]
              simp
            rw [takeEq, Goose.Lower.Validation.ReplacementContentFlowSource.lowerArgs_append_run]
            simpa [lowerArgs, lowerArg, bind_run, pure_run] using combined.sub (cells' := []) (by simp)
          let nextSources := ArgsSource.afterHead sources done
          have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
            intro fuel
            exact ArgsSource.afterHead_callChildren source sources canonical done fuel
          have next := ih nextSources nextCanonical nextTracked nextPost nextCells nextBounded nextRealized nextInput residual
          cases next with
          | interior cursor current progress => exact .interior (.next count executed evaluated cursor) current progress
          | @complete consumedTail remainingTail final values finalPrior tailCount tailExecuted tailResidual trace finalTracked finalBounded finalRealized finalPost finalCells finalInput =>
            apply CallMixedPrefixCells.complete (consumed := consumed + consumedTail) (remaining := remainingTail)
              (boundary := final) (values := value :: values) (prior := finalPrior) (by omega)
              (executed.append tailExecuted) tailResidual (.cons done trace)
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalTracked
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
            · exact finalRealized
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPost
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalCells
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
        obtain ⟨location, length, point, frame, aliases, done, traversal, first, tail, finalPost, nextTracked, nextRealized, nextBounded, nextInput⟩ :=
          accepted_generated_call_reference_complete_demand source found child target childCanonical headForm occurrence rows tracked
            bounded realized input extended
        have executed := DemandRuntimePrefix.next ((first 0).runtime) tail
        rcases executed.compare_strict steps with ⟨remaining, count, residual⟩ | ⟨remaining, positive, count, suffix⟩
        ·
          have nextCells := cells.next found finalPost
          have nextPost : Post cfg env cx before callFrame
              (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point [] := by
            have combined := wholePost.comp finalPost
            have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byRef mutability place] := by
              rw [List.take_add_one, found]
              simp
            rw [takeEq, Goose.Lower.Validation.ReplacementContentFlowSource.lowerArgs_append_run]
            simpa [lowerArgs, bind_run, pure_run] using combined.sub (cells' := []) (by simp)
          let nextSources := ArgsSource.afterHead sources done
          have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
            intro fuel
            exact ArgsSource.afterHead_callChildren source sources canonical done fuel
          have next := ih nextSources nextCanonical nextTracked nextPost nextCells nextBounded nextRealized nextInput residual
          cases next with
          | interior cursor current progress => exact .interior (.referenceNext count executed done cursor) current progress
          | @complete consumedTail remainingTail final values finalPrior tailCount tailExecuted tailResidual trace finalTracked finalBounded finalRealized finalPost finalCells finalInput =>
            apply CallMixedPrefixCells.complete (consumed := (length + 1) + consumedTail) (remaining := remainingTail)
              (boundary := final) (values := .ref location :: values) (prior := finalPrior) (by omega)
              (executed.append tailExecuted) tailResidual (.cons done trace)
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalTracked
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
            · exact finalRealized
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPost
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalCells
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput
        · obtain ⟨actualLocation, placed, placeEntry, placeAddressed, addressStep⟩ :=
            accepted_generated_call_reference_demand source found child (Or.inl target) childCanonical headForm occurrence rows tracked
              input.atPoint input.related bounded realized extended
          have locationEq : actualLocation = location := by
            have same := done
            simp [evalArg, bind_apply, placed, pure_apply] at same
            exact same
          subst actualLocation
          have currentDemand := traversal.runtimePrefix_invariant (by omega) steps
          have world : child.world = source.world := childCanonical.2.2.1
          have sourceCarried : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env reached := by
            cases currentDemand.1 with
            | inl current => simpa only [RetainedSsaMap.Realizes, world] using current.operands
            | inr current => simpa only [RetainedSsaMap.Realizes, world] using current.operands
          have current : map.Realizes cfg.mod source.world env reached :=
            ⟨fun cell member => sourceCarried.1 cell (List.mem_append_right prior member), sourceCarried.2⟩
          have progress := traversal.runtimePrefix_next (by omega) steps
          exact .interior (required := required)
            (.referenceInterior found child target childCanonical placeEntry placeAddressed currentDemand.1 currentDemand.2 done executed count suffix)
            current (.inr progress)

theorem accepted_generated_call_mixed_prefix_cells {cfg : Cfg} {env : Env} {state : St}
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
    (shrink : cfg.mod.profile = .shrink) (form : CallMixedArguments source.rootsEnv.access arguments)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    :
    CallMixedPrefixCells source cx results before loop map initial [] 0 arguments ⟨start, initial, state⟩ taken reached := by
  let sources := fun fuel => Classical.choose (source.callArgsCanonical fuel results input.metadata)
  have canonical : ∀ fuel, (sources fuel).CallChildren source 0 := by
    intro fuel
    exact (Classical.choose_spec (source.callArgsCanonical fuel results input.metadata)).2
  have tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take 0)
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).1 [] := by
    simpa [lowerArgs, pure_run] using (GeneratedCallArgumentRows.nil (access := source.rootsEnv.access) (path := source.path) 0)
  apply accepted_generated_call_mixed_prefix_cells_suffix source selected owned occurrence rows coverage admitted extended shrink form sources canonical tracked
  · simpa [lowerArgs, pure_run] using (Post.init input.related input.atPoint)
  · simpa [lowerArgs, pure_run] using CallArgumentCells.empty before.vals.size initial
  · simpa [lowerArgs, pure_run] using bounded
  · simpa using realized
  · simpa [lowerArgs, pure_run] using input
  · exact steps


theorem CallMixedPrefixCells.frontier {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    {source : ExprSource cfg env (.call context arguments origin) state}
    {cx : FnCtx} {results : List Ty} {before : LS} {loop : Option LoopCtx} {map : RetainedSsaMap}
    {initial : GIR.Frame} {start : Pt} {taken : Nat} {reached : DemandRuntimePoint}
    (outcome : CallMixedPrefixCells source cx results before loop map initial [] 0 arguments ⟨start, initial, state⟩ taken reached)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    (∃ required, CallMixedPrefix source cx results before loop map required 0 arguments ⟨start, initial, state⟩ taken reached ∧
      map.Realizes cfg.mod source.world env reached ∧
      ((∃ id op, instAt cx.fn reached.point = some (.def id op)) ∨
        ∃ next, ∀ fuel, DemandInstructionStep cx fuel reached next)) ∨
    ∃ (sourceFuel consumed remaining : Nat) (boundary : DemandRuntimePoint) (values : List Val),
      consumed + remaining = taken ∧
      DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧
      mapList (evalArg sourceFuel cfg env) arguments state = .ok values boundary.state ∧
      map.Realizes cfg.mod source.world env boundary ∧
      Post cfg env cx before initial (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2
        boundary.frame boundary.point [] ∧
      mapList (getVal boundary.frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 boundary.state =
        .ok values boundary.state ∧
      instAt cx.fn boundary.point = some (.def (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1
        (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin))) := by
  cases outcome with
  | interior cursor current progress => exact Or.inl ⟨_, cursor, current, progress⟩
  | @complete consumed remaining boundary values prior count executed residual trace tracked bounded realized wholePost cells input =>
    obtain ⟨sourceFuel, evaluated⟩ := trace.fuel
    have read := cells.read boundary.state
    have point : (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2.pp = some boundary.point := by
      simpa using input.atPoint
    let le := lowerEnv cfg.mod env.vars results
    obtain ⟨ids, middle, afterCall, argsRun, definition, tail⟩ := lowerExpr_call_split
      (show lowerExpr (.call context arguments origin) le before =
        ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
    have afterExtended : ExtT afterCall cx.fn.blocks := by
      rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
      · exact extended.of_adv (adv_emitTerm term)
      · exact extended
    have sameIds : ids = (lowerArgs arguments le before).1 := by rw [argsRun]
    have sameMiddle : middle = (lowerArgs arguments le before).2 := by rw [argsRun]
    subst ids
    subst middle
    have instruction := (emitDef_facts definition point afterExtended).2.2.2.2
    have current : map.Realizes cfg.mod source.world env boundary :=
      ⟨fun cell member => realized.1 cell (List.mem_append_right prior member), realized.2⟩
    exact Or.inr ⟨sourceFuel, consumed, remaining, boundary, values, count, executed, residual, evaluated,
      current, by simpa using wholePost, by simpa using read, instruction⟩

#print axioms CallMixedPrefixCells.frontier

#print axioms accepted_generated_call_mixed_prefix_cells
end Goose.Lower
