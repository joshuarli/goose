import Goose.Lower.DemandWhileMixedBlock
import Goose.GIR.Validate

namespace Goose.Lower.DemandWhileMixedChecks
open Goose.Core Goose.GIR

def condition : Expr := .read (.global 0)
def iteration : Core.Block := .mk 3 [.assign (.global 0) (.bool false) 1] none
def inner : Core.Block := .mk 2 [] none
def outer : Core.Block := .mk 1 [.ifS (.bool true) inner none 3] none
def body : Core.Block := .mk 0 [.ifS (.bool true) outer none 4, .while condition iteration 2] none
def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body, summary := .unknown }
def module (profile : ArtifactProfile) : Core.Module :=
  { profile, files := #["while-demand.goose"], types := #[],
    globals := #[⟨"again", .bool, .mutable, .bool true, 0⟩], impls := #[implementation],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "global"⟩, ⟨0, 2, "assign"⟩, ⟨0, 3, "while"⟩, ⟨0, 4, "if"⟩, ⟨0, 5, "if"⟩] }

theorem supported (cfg : Cfg) (env : Env) : WhileMixedStatements cfg env body.stmts := by
  change WhileMixedStatements cfg env ([.ifS (.bool true) outer none 4] ++ [.while condition iteration 2])
  apply WhileMixedStatements.recursive
  · apply RecursiveIfStatements.conditional (.scalar (.boolean true)) outer 4
    · intro outerState
      change RecursiveIfStatements cfg _ [.ifS (.bool true) inner none 3]
      apply RecursiveIfStatements.conditional (.scalar (.boolean true)) inner 3
      · intro innerState
        exact .nil _
      · rfl
      · exact .nil _
    · rfl
    · exact .nil _
  · apply WhileMixedStatements.loop condition iteration 2 (.scalar (.globalRead 0))
    · intro middle
      simpa [iteration, Core.Block.stmts] using (RecursiveIfStatements.scalar
        (ScalarAssignmentStatements.assignment (.global 0) (.boolean false) 1 .nil)
        (RecursiveIfStatements.nil _))
    · rfl
    · exact .nil

#guard [ArtifactProfile.pilot, .shrink].all fun profile =>
  match Core.validate (module profile), GIR.validate (lower (module profile)) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 50 profile (module artifact), GIR.run 100 profile (lower (module artifact)) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

#print axioms supported
end Goose.Lower.DemandWhileMixedChecks
