import Goose.Lower.Validation.SourceCanonicalRootFloorsContracts
import Goose.Lower.Validation.SourceCanonicalRootFloorsNativeFlow

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem call_floor (calleeId : ContextId) (arguments : List Arg) (origin : OriginId)
    (children : ArgumentsFloor arguments) : ExpressionFloor (.call calleeId arguments origin) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  obtain ⟨context, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt,
    arity, argumentsSource, resultSource⟩ := tyExpr_call_tables source
  have actualContext : env.mod.contexts[calleeId]? = some context := by
    rw [sourceTables.moduleEq]; exact contextAt
  have actualCallee : env.mod.impls[context.impl]? = some callee := by
    rw [sourceTables.moduleEq]; exact calleeAt
  have projection : ∃ argumentRoots rootsMiddle,
      rpArgs env arguments rootsBefore = .ok (argumentRoots, rootsMiddle) ∧
      sourceCallRoots env calleeId argumentRoots = sourceRoots := by
    simp only [rpExpr] at replayed
    obtain ⟨argumentRoots, middle, argumentsReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    exact ⟨argumentRoots, middle, argumentsReplay, sourceCallRoots_agrees env calleeId argumentRoots _ _ sourceRoots replayed⟩
  obtain ⟨argumentRoots, rootsMiddle, argumentsReplay, projected⟩ := projection
  simp only [lowerExpr] at run
  obtain ⟨values, argumentsAfter, argumentsRun, run⟩ := bind_eq.mp run
  obtain ⟨returned, emitted, emittedRun, run⟩ := bind_eq.mp run
  change (if (lowerEnv typing.mod typing.vars returnTypes).mod.noReturn calleeId then
      (fun le state => (returned, (emitTerm .unreachable le state).2))
    else (fun _ state => (returned, state))) (lowerEnv typing.mod typing.vars returnTypes) emitted =
      (value, after) at run
  by_cases stopped : (lowerEnv typing.mod typing.vars returnTypes).mod.noReturn calleeId = true
  · simp only [stopped, ite_true] at run
    have stateEq := (Prod.mk.inj run).2
    rw [← stateEq] at live
    cases current : emitted.cur with
    | none => simp [emitTerm_none _ _ current, current] at live
    | some block => simp [emitTerm_run _ _ current] at live
  · simp only [stopped, ite_false] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    have argumentsLive := (dead_emitDef _).live_before emittedRun live
    have suffix := advB_emitDef _ _ _ _ _ emittedRun
    have locations : ∀ (index : Nat) (argument : Arg), arguments[index]? = some argument →
        ∃ childPath, DemandNodeAt root childPath (argumentSourceNode argument) := by
      intro index argument present
      refine ⟨path ++ [index], location.snoc index ?_⟩
      cases argument <;> simp [DemandNode.child?, DemandNode.children, present, argumentSourceNode]
    have floors := children tables sourceTables valid locations arity argumentsSource argumentsReplay
      argumentsRun generated argumentsLive (continuation.of_advance suffix) (projects.of_advance suffix)
    rw [← projected]
    simp only [sourceCallRoots, actualContext, actualCallee]
    cases resultShape : callee.results.toList with
    | nil => exact List.nil_subset _
    | cons result rest =>
      cases rest with
      | cons _ _ => exact List.nil_subset _
      | nil =>
        cases declaredShape : context.resultRoots with
        | nil => exact List.nil_subset _
        | cons declared rest =>
          cases rest with
          | cons _ _ => exact List.nil_subset _
          | nil =>
            by_cases reference : result.isRefLike = true
            · simp only [reference, ite_true]
              have declarations := tables.callees calleeId context callee actualContext actualCallee
                result resultShape reference
              simp only [declaredShape, List.getElem?_cons_zero, Option.getD_some] at declarations
              have emittedGenerated := generated.lowerArgs arguments argumentsRun
              obtain ⟨block, blockMember, definition⟩ := emitted_definition_native emittedGenerated emittedRun live continuation
              exact emitted_call_mapped_canonical_floor emittedGenerated emittedRun live continuation
                (tables.definitions _ blockMember _ _ definition) tables.rootUniverse _ tables.rootCount
                argumentRoots declared declarations floors
            · simp only [reference, ite_false]
              exact List.nil_subset _

end Goose.Lower.Validation.SourceCanonicalRootFloors
