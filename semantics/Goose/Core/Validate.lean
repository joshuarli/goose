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
  checkEntry m
  for h : g in [0:m.globals.size] do
    checkGlobal m g m.globals[g]
  for impl in m.impls do
    checkImpl m impl
  for ctx in m.contexts do
    checkContext m ctx

end Goose.Core
