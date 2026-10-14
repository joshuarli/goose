import Goose.Lower.LoopPrepare
import Goose.Core.Validate
import Goose.GIR.Validate
import Goose.Proofs.Lower

namespace Goose.Lower.LoopPrepareChecks

open Goose.Core Goose.GIR

def breakingBody : Core.Block :=
  .mk 1 [.letS 0 (.lit .i64 9) 0, .print [.expr (.read (.var 0))] 0, .brk 0] none

def source : Core.Module :=
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"x", .int .i64, .immutable, 1, 0⟩],
      body := .mk 0 [.while (.bool true) breakingBody 0] none, summary := .unknown }
  { files := #["break.goose"], types := #[.int .i64], globals := #[], impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0, origins := #[⟨0, 1, "break"⟩] }

theorem concrete_breaking_block (n : Nat) (profile : NumProfile)
    (env : Env) (loop : LoopCtx) (hdepth : loop.depth ≤ env.scopes.length) :
    (execBlock (n + 1) ⟨profile, source⟩ env [] breakingBody >>= prepareLoopFlow env (some loop)) =
      preparedCoreLoopBlock n ⟨profile, source⟩ env (some loop) 1
        breakingBody.stmts none [] :=
  prepareLoopFlow_execBlock n ⟨profile, source⟩ env (some loop) 1 breakingBody.stmts none [] hdepth

#guard match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 30 profile source, GIR.run 100 profile (lower source) with
  | .done .returned "9\n", .done .returned "9\n" => true
  | _, _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  match Core.runModule 30 ⟨profile, source⟩ St.initial,
      GIR.runModule 100 ⟨profile, lower source⟩ St.initial with
  | .ok () coreState, .ok () girState => coreState.store.roots.isEmpty && girState.store.roots.isEmpty
  | _, _ => false

end Goose.Lower.LoopPrepareChecks
