import Goose.GIR.Validate

namespace Goose.GIR.AdmittedSlotSymbolsChecks

open Goose.Core

private def function : Func :=
  { name := "slot-bounds"
    params := [.ref .readOnly (.int .i64)]
    results := []
    slots := #[⟨.ref .readOnly (.int .i64), .immutable, 0, 0⟩]
    scopes := #[none]
    blocks := #[⟨[(0, .data (.ref .readOnly (.int .i64)))], [.term (.ret [] none)]⟩]
    summary := .unknown
    org := none }

private def module : Module :=
  { files := #[], globals := #[], funcs := #[function], entry := 0, origins := #[] }

private def accepts (rows : Option (Array (SlotId × List RootRef))) : Bool :=
  (checkSymbols module "slot-bounds" { function with roots.slots := rows }).toBool

#guard accepts none
#guard accepts (some #[])
#guard accepts (some #[(0, [.local 0, .param 0])])
#guard !accepts (some #[(1, [])])
#guard !accepts (some #[(0, [.local 1])])
#guard !accepts (some #[(0, [.param 1])])
#guard !accepts (some #[(0, [.global 0])])

end Goose.GIR.AdmittedSlotSymbolsChecks
