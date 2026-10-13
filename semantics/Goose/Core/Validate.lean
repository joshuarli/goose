import Goose.Core.Roots

/-!
`validate`: the independent check that a module is safe to run.

It trusts nothing the exporter wrote beyond the program text itself. Typing,
writes and call mutability are checked once per implementation and global
(`Goose.Core.Typing`); root annotations, block values, results, call roots
and effect summaries are checked once per context (`Goose.Core.Roots`), so two
contexts sharing an implementation are each judged against their own
annotation.
-/

namespace Goose.Core

/-- The entry context takes no arguments and returns nothing. -/
def checkEntry (m : Module) : V Unit := do
  let some ctx := m.contexts[m.entry]? | reject .type "the entry context is outside the context table"
  let some impl := m.impls[ctx.impl]? | reject .type "the entry context names a missing implementation"
  unless impl.params.isEmpty && impl.results.isEmpty do
    reject .type s!"the entry {impl.name} must take no parameters and return nothing"

def validate (m : Module) : V Unit := do
  checkStructTables m
  checkEntry m
  forAll (List.range m.globals.size) fun g =>
    match m.globals[g]? with
    | some gl => checkGlobal m g gl
    | none => pure ()
  forAll m.impls.toList (checkImpl m)
  forAll m.contexts.toList (checkContext m)
  forAll (List.range m.globals.size) (checkInitRoots m)

end Goose.Core
