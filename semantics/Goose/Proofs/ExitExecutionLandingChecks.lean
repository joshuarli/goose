import Goose.Proofs.ExitExecutionChecks

set_option Elab.async false

namespace Goose.Proofs.ExitExecutionLandingChecks
open Goose.Construct

private def array : Ty := .varr (.int .u8)
def nestedNamedExit (forward : Bool) : Module :=
  let entry : Impl := ⟨"entry", #[], #[],
    #[⟨"first", array, .immutable, 0, 0⟩, ⟨"second", .int .i64, .immutable, 0, 0⟩],
    .mk 0 [.receive [0, 1] (.call 1 [] 0) 0,
      .print [.view (.of (.global 0)), .view (.of (.var 0)), .expr (.read (.var 1))] 0] none,
    .known ⟨[.global 0], [], [], [], [], [], [], [], false, true⟩⟩
  let target : Impl := ⟨"target", #[], #[⟨array, .value, some 0⟩, ⟨.int .i64, .register, none⟩],
    #[⟨"named", array, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.bytes array [65] 0) 0, .expr (.call 2 [] 0) 0]
      (some (.values [.resultLocal 0 0, .lit .i64 8])),
    .known ⟨[], [], [], [], [], [0], [], [], false, true⟩⟩
  let helper : Impl := ⟨"helper", #[], #[], #[⟨"local", array, .immutable, 1, 0⟩],
    .mk 0 [.ifS (.bool true) (.mk 1 [.letS 0 (.bytes array [88] 0) 0,
      .print [.text "before"] 0, .expr (.call 3 [] 0) 0] none) none 0] none,
    .known ⟨[], [], [], [], [], [], [0], [0], false, true⟩⟩
  let returning := if forward then Stmt.returnFromForward 0 (.call 4 [] 0) 0
    else .returnFrom 0 [.bytes array [66] 0, .lit .i64 7] 0
  let helper2 : Impl := ⟨"helper2", #[], #[], #[⟨"local", array, .immutable, 1, 0⟩],
    .mk 0 [.ifS (.bool true) (.mk 1 [.letS 0 (.bytes array [89] 0) 0, returning] none) none 0] none,
    .known ⟨[], [], [], [], [], [], [0], [0], false, false⟩⟩
  let leaf : Impl := ⟨"leaf", #[], #[⟨array, .value, none⟩, ⟨.int .i64, .register, none⟩], #[],
    .mk 0 [] (some (.values [.bytes array [66] 0, .lit .i64 7])),
    .known ⟨[], [], [], [], [], [0], [], [], false, false⟩⟩
  ⟨#["nested-named-exit.goose"], #[.int .u8, array, .int .i64],
    #[⟨"outside", array, .immutable, .bytes array [67] 0, 0⟩], #[entry, target, helper, helper2, leaf],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "target", [], [[], []], []⟩,
      ⟨2, "helper", [], [], []⟩, ⟨3, "helper2", [], [], []⟩, ⟨4, "leaf", [], [[], []], []⟩],
    0, #[⟨0, 17, "call"⟩], #[], #[⟨1, []⟩]⟩


def expectedEvents : List Goose.Core.ConstructionEvent :=
  [.begin 0, .write 0 0, .publish 0,
    .begin 1, .write 1 0,
    .begin 2, .write 2 0, .publish 2,
    .begin 3, .write 3 0, .publish 3,
    .begin 4, .write 4 0, .abandon 1, .relocate 4 .exitValue, .publish 4]

theorem nestedNamedExit_validated (forward : Bool) :
    validate (nestedNamedExit forward) = .ok () := by
  cases forward <;> cbv

set_option maxRecDepth 2048 in
theorem nestedNamedExit_execution (forward : Bool) (profile : Goose.Core.NumProfile) :
    ExitExecutionChecks.returnedObservation (eval 400 profile (nestedNamedExit forward)) =
      some ("before\nCB7\n".toUTF8.data.toList, expectedEvents) := by
  cases forward <;> cases profile <;> cbv

def outsideObservation (forward : Bool) (profile : Goose.Core.NumProfile) :=
  let final := Goose.Proofs.Exit.stepState (runModule 400 ⟨profile, nestedNamedExit forward⟩ .initial)
  (final.objects.map Prod.fst, final.activations.map (·.act),
    final.construction.storage[0]?.map (fun storage => (storage.bytes.data.toList, storage.publishedCount)))

set_option maxRecDepth 2048 in
theorem nestedNamedExit_outside_storage (forward : Bool) (profile : Goose.Core.NumProfile) :
    outsideObservation forward profile = ([Goose.Core.RootInst.global 0], [], some ([1, 0, 0, 0, 67], 1)) := by
  cases forward <;> cases profile <;> cbv

#print axioms nestedNamedExit_validated
#print axioms nestedNamedExit_execution
#print axioms nestedNamedExit_outside_storage

end Goose.Proofs.ExitExecutionLandingChecks
