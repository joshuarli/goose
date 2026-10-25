import Goose.Lower.Validation.SourceReplacementLexicalWritersStorePhysics
import Goose.Lower.Validation.SourceReplacementLexicalWritersPhysics
import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsAssignShape

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource SummaryPreservation

theorem assignment_store_tracked_local_impossible (facts : SourceReadyFunction)
    {typing : TEnv} (tables : SourceRootTables typing facts.source)
    {place : Place} {expression : Expr} {origin : OriginId} {loop : Option LoopCtx}
    {scope start finish : Nat} {output : TEnv}
    (source : tyStmt typing scope (.assign place expression origin) start = .ok (output,finish))
    {results : List Ty} {before : LS} (generated : GeneratedBuilderState before)
    (native : NativeRows facts.types
      (lowerStmt loop (.assign place expression origin) (lowerEnv typing.mod typing.vars results) before).2)
    (continuation : NativeBuilderContinuation facts.func
      (lowerStmt loop (.assign place expression origin) (lowerEnv typing.mod typing.vars results) before).2)
    (live : (lowerExpr expression (lowerEnv typing.mod typing.vars results)
      (lowerPlace place (lowerEnv typing.mod typing.vars results) before).2).2.cur.isSome = true)
    (reference : valRefLike facts.types
      (lowerExpr expression (lowerEnv typing.mod typing.vars results)
        (lowerPlace place (lowerEnv typing.mod typing.vars results) before).2).1 = true)
    {tracked : VarId}
    (upper : rootsAt facts.upper.vals (lowerPlace place (lowerEnv typing.mod typing.vars results) before).1 = [.local tracked]) :
    False := by
  let env := lowerEnv typing.mod typing.vars results
  let addressed := lowerPlace place env before
  let lowered := lowerExpr expression env addressed.2
  obtain ⟨info, childStart, placeTyped, valueTyped, shape, _⟩ := tyStmt_assign_children source
  have valueNative : NativeRows facts.types lowered.2 := native.of_prefix
    (types_emitEffect (.store addressed.1 lowered.1 (some origin)) env lowered.2 _ _ rfl)
  have placeNative : NativeRows facts.types addressed.2 := valueNative.of_prefix
    (types_lowerExpr expression env addressed.2 _ _ rfl)
  have placeGenerated := generated.lowerPlace place (env := env) rfl
  have valueType : facts.types[lowered.1]? = some (some (.data info.ty)) :=
    valueNative.expression placeGenerated valueTyped rfl live
  change valRefLike facts.types lowered.1 = true at reference
  have sourceReference : info.ty.isRefLike = true := by
    simpa only [valRefLike, valueType, VTy.refLike] using reference
  rcases mutation_assign_source_cases tables placeTyped shape with scalar | ⟨parameter, localVar, placeEq, variableAt, formal⟩
  · rw [scalar] at sourceReference
    cases sourceReference
  · have placeLive := (dead_lowerExpr expression).live_before (le := env) rfl live
    have placeContinuation := (continuation.of_advance
      (advB_emitEffect (.store addressed.1 lowered.1 (some origin)) env lowered.2 _ _ rfl)).of_advance
      (advB_lowerExpr expression env addressed.2 _ _ rfl)
    obtain ⟨mode, typeAt⟩ := placeNative.place generated placeTyped rfl placeLive
    change facts.types[addressed.1]? = some (some (.data (.ref mode info.ty))) at typeAt
    have nativeReference : valRefLike facts.types addressed.1 = true := by
      simp [valRefLike, typeAt, VTy.refLike, Ty.isRefLike]
    have seed := facts.sourceSlotSeeds tables parameter localVar
      (by simpa only [tables.variablesEq] using variableAt) formal
    have actualRun : lowerExpr (.read (.var parameter)) env before = (addressed.1,addressed.2) := by
      simpa only [addressed, placeEq, lowerPlace] using (show lowerPlace place env before = addressed from rfl)
    have floor := readVar_parameter_native_floor facts.native generated.live actualRun placeLive placeContinuation nativeReference seed
    have impossible := facts.below addressed.1 floor
    rw [upper] at impossible
    simp at impossible

#print axioms assignment_store_tracked_local_impossible

end Goose.Lower.Validation.SourceReplacementLexicalWriters
