import Goose.Lower.Coerce

namespace Goose.Lower.CoerceChecks

open Goose.Core Goose.GIR

def sourceModule : Core.Module :=
  { files := #["coerce.goose"], types := #[], globals := #[], impls := #[],
    contexts := #[], entry := 0, origins := #[] }

def before (source : Ty) : LS :=
  { blocks := #[⟨[(0, .data source)], #[]⟩], vals := #[some (.data source)],
    cur := some 0, stack := [] }

def lowered (source target : Ty) : ValueId × LS :=
  (do let result ← coerceTo target 0
      emitTerm (.ret [result] none)
      pure result) (lowerEnv sourceModule #[] []) (before source)

def fn (source target : Ty) : Func :=
  { name := "coerce", params := [source], results := [target], slots := #[], scopes := #[],
    blocks := finishBlocks (lowered source target).2.blocks, summary := .unknown, org := none }

def frame (value : Val) : GIR.Frame :=
  ⟨0, [], ({} : Std.HashMap Nat RVal).insert 0 (.val value), 0⟩

def castResult (source target : Ty) (value : Val) : Res Val :=
  runAt ⟨⟨.release, lower sourceModule⟩, fn source target⟩ (0, 0) (frame value) 8 St.initial

#guard (lowered (.ref .mutable (.int .i64)) (.ref .readOnly (.int .i64))).1 == 1
#guard (lowered (.slice .mutable (.int .i64)) (.slice .readOnly (.int .i64))).1 == 2
#guard (lowered (.int .i64) (.int .i64)).1 == 0

#guard match castResult (.ref .mutable (.int .i64)) (.ref .readOnly (.int .i64))
    (.ref ⟨.global 0, []⟩) with
  | .ok (.ref ⟨.global 0, []⟩) state => state.trace.isEmpty && state.nextScope == 0
  | _ => false
#guard match castResult (.slice .mutable (.int .i64)) (.slice .readOnly (.int .i64))
    (.slice ⟨.global 0, []⟩ 4 9) with
  | .ok (.slice ⟨.global 0, []⟩ 4 9) state => state.trace.isEmpty && state.nextScope == 0
  | _ => false

end Goose.Lower.CoerceChecks
