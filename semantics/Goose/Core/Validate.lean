import Goose.Core.Demand
import Goose.Core.Origins

namespace Goose.Core

/-- The entry context takes no arguments and returns nothing. -/
def checkEntry (m : Module) : V Unit := do
  let some ctx := m.contexts[m.entry]? | reject .type "the entry context is outside the context table"
  let some impl := m.impls[ctx.impl]? | reject .type "the entry context names a missing implementation"
  unless impl.params.isEmpty && impl.results.isEmpty do
    reject .type s!"the entry {impl.name} must take no parameters and return nothing"

def checkImplementationContexts (m : Module) : V Unit :=
  forAll (List.range m.impls.size) fun i =>
    unless m.contexts.toList.any (fun ctx => ctx.impl == i) do
      reject .root s!"implementation {i} has no context"

def checkOrigins (m : Module) : V Unit :=
  forAll m.origins.toList fun origin =>
    match checkOriginRecord m.files.size origin with
    | .ok () => pure ()
    | .error message => reject .type message

def validate (m : Module) : V Unit := do
  checkStructTables m
  checkEntry m
  checkImplementationContexts m
  forAll (List.range m.globals.size) fun g =>
    match m.globals[g]? with
    | some gl => checkGlobal m g gl
    | none => pure ()
  forAll m.impls.toList (checkImpl m)
  forAll m.contexts.toList (checkContext m)
  forAll (List.range m.globals.size) (checkInitRoots m)
  checkModuleDemand m
  checkOrigins m

end Goose.Core
