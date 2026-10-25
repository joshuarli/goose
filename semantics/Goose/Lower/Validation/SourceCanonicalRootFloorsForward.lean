import Goose.Lower.Validation.SourceCanonicalRootFloorsFacts

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR ProvenanceConvergence ReplacementContentFlowSource

theorem SourceCanonicalTables.emitted_forward_floor {env : PEnv} {func : Func}
    (tables : SourceCanonicalTables env func) {localEnv : LEnv} {before after : LS}
    {input value : ValueId} {op : Op} (generated : GeneratedBuilderState before)
    (run : emitDef op localEnv before = (value, after)) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) (forward : RootForward op input) :
    rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals input ⊆
    rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals value := by
  obtain ⟨block, member, definition⟩ := emitted_definition_native generated run live continuation
  exact emitted_forward_canonical_floor generated run live continuation
    (tables.definitions _ member _ _ definition) forward tables.rootUniverse _ tables.rootCount

private theorem pure_floor {env : LEnv} {before after : LS} {input value : ValueId} {provenance : Prov}
    (run : (pure input : B ValueId) env before = (value, after)) :
    rootsAt provenance.vals input ⊆ rootsAt provenance.vals value := by
  obtain ⟨rfl, _⟩ := pure_eq.mp run
  exact fun _ member => member

theorem SourceCanonicalTables.freezeTo_floor {env : PEnv} {func : Func}
    (tables : SourceCanonicalTables env func) {localEnv : LEnv} {before after : LS}
    {input value : ValueId} {mode : Mutability} (generated : GeneratedBuilderState before)
    (run : freezeTo mode input localEnv before = (value, after)) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) :
    rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals input ⊆
    rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals value := by
  simp only [freezeTo] at run
  obtain ⟨type, middle, typeRun, run⟩ := bind_eq.mp run
  have same := valTy_run input localEnv before
  rw [typeRun] at same
  dsimp only at same
  subst middle
  split at run
  · exact tables.emitted_forward_floor generated run live continuation (.refFreeze input)
  · exact pure_floor run

theorem SourceCanonicalTables.borrowTo_floor {env : PEnv} {func : Func}
    (tables : SourceCanonicalTables env func) {localEnv : LEnv} {before after : LS}
    {input value : ValueId} {mode : Mutability} (generated : GeneratedBuilderState before)
    (run : borrowTo mode input localEnv before = (value, after)) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) :
    rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals input ⊆
    rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals value := by
  simp only [borrowTo] at run
  obtain ⟨queriedEnv, queriedState, queried, run⟩ := bind_eq.mp run
  simp only [read_apply, Prod.mk.injEq] at queried
  obtain ⟨rfl, rfl⟩ := queried
  obtain ⟨type, middle, typeRun, run⟩ := bind_eq.mp run
  have same := valTy_run input localEnv before
  rw [typeRun] at same
  dsimp only at same
  subst middle
  let owner := match type with
    | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) => true
    | _ => false
  change (if mode == .mutable && localEnv.mod.profile == .shrink && owner then
    emitDef (.ownerBorrow input) else freezeTo mode input) localEnv before = (value, after) at run
  by_cases enabled : (mode == .mutable && localEnv.mod.profile == .shrink && owner) = true
  · simp only [enabled, ite_true] at run
    exact tables.emitted_forward_floor generated run live continuation (.ownerBorrow input)
  · simp only [enabled] at run
    exact tables.freezeTo_floor generated run live continuation

end Goose.Lower.Validation.SourceCanonicalRootFloors
