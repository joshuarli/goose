import Goose.Construct.Targets

namespace Goose.Construct.TargetChecks

private def summary (needs escapes : List Nat) : SummaryAnn :=
  .known ⟨[], [], [], [], [], [], needs, escapes, false, false⟩

private def implementation (name : String) (body : Block) (needs escapes : List Nat) : Impl :=
  ⟨name, #[], #[⟨.int .i64, .register, none⟩], #[], body, summary needs escapes⟩

private def valid : Module := {
  files := #[]
  types := #[.int .i64]
  globals := #[]
  impls := #[
    implementation "target" (.mk 0 [.retForward (.call 1 [] 0) 0] none) [] [],
    implementation "intermediate" (.mk 0 [.retForward (.call 2 [] 0) 0] none) [0] [0],
    implementation "helper" (.mk 0 [.returnFrom 0 [.lit .i64 7] 0] none) [0] [0]]
  contexts := #[⟨0, "target", [], [[]], []⟩, ⟨1, "intermediate", [], [[]], []⟩,
    ⟨2, "helper", [], [[]], []⟩]
  entry := 0
  origins := #[]
  structs := #[]
  targets := #[⟨0, []⟩] }

private def accepts (module : Module) : Bool :=
  match checkTargetAvailability module with
  | .ok _ => true
  | .error _ => false

#guard accepts valid
#guard !accepts { valid with entry := 1 }
#guard !accepts { valid with entry := 2 }
#guard !accepts { valid with
  impls := valid.impls.set! 2 { valid.impls[2] with summary := summary [] [] } }
#guard !accepts { valid with
  impls := valid.impls.set! 1 { valid.impls[1] with summary := summary [] [] } }
#guard !accepts { valid with targets := #[⟨1, []⟩] }
#guard !accepts { valid with
  impls := valid.impls.set! 0 { valid.impls[0] with summary := summary [0] [] } }

private def recursive : Module := { valid with
  impls := valid.impls.set! 0 { valid.impls[0] with
    body := .mk 0 [.expr (.call 0 [] 0) 0, .retForward (.call 1 [] 0) 0] none } }

#guard accepts recursive
#guard !accepts { valid with
  targets := #[⟨0, [1]⟩]
  impls := valid.impls.set! 1 { valid.impls[1] with
    results := #[⟨.int .u64, .register, none⟩] } }

end Goose.Construct.TargetChecks
