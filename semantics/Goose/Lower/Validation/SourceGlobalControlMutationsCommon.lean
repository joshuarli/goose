import Goose.Lower.Validation.SourceGlobalControlLeaves

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem _root_.Goose.Lower.Validation.SourceRootTables.global_native_place_owner {typingEnv : TEnv} {env : PEnv}
    {vt : Array (Option VTy)} {returnTypes : List Ty} {place : Place} {info : PlaceInfo} {start finish : Nat}
    {before after : LS} {value : ValueId} (tables : SourceRootTables typingEnv env)
    (native : NativeRows vt after) (generated : GeneratedBuilderState before)
    (typed : tyPlace typingEnv place start = .ok (info, finish))
    (run : lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) before = (value, after))
    (live : after.cur.isSome = true) : ownerTy vt value = some info.ty := by
  apply native.place_ownerTy (results := returnTypes) generated typed _ live
  simpa only [← tables.moduleEq, ← tables.variablesEq] using run

theorem _root_.Goose.Lower.Validation.SourceRootTables.global_native_place_row {typingEnv : TEnv} {env : PEnv}
    {vt : Array (Option VTy)} {returnTypes : List Ty} {place : Place} {info : PlaceInfo} {start finish : Nat}
    {before after : LS} {value : ValueId} (tables : SourceRootTables typingEnv env)
    (native : NativeRows vt after) (generated : GeneratedBuilderState before)
    (typed : tyPlace typingEnv place start = .ok (info, finish))
    (run : lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) before = (value, after))
    (live : after.cur.isSome = true) : ∃ mutability, vt[value]? = some (some (.data (.ref mutability info.ty))) := by
  apply native.place (results := returnTypes) generated typed _ live
  simpa only [← tables.moduleEq, ← tables.variablesEq] using run

end Goose.Lower.Validation.SummaryPreservation
