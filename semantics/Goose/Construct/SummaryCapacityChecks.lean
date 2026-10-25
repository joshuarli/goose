import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Construct.SummaryCapacityChecks

private def array : Ty := .varr (.int .u8)

private def moduleOf (ty : Ty) (expression : Expr) (aborts : Bool := false) : Module :=
  ⟨#["summary-capacity.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"result", ty, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 expression 0] none,
      .known ⟨[], [], [], [], [], [], [], [], aborts, false⟩⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

private def breaking (expression : Expr) : Expr :=
  .blockE (.mk 1 [.breakValue expression 0] none) 0

private def branching (expression : Expr) : Expr :=
  breaking (.ifE (.bool true)
    (.mk 2 [.breakValue expression 0] none)
    (.mk 3 [] (some expression)) 0)

theorem direct_bounded_validated :
    validate (moduleOf array (.bytes array [65] 0)) = .ok () := by cbv

theorem breaking_omitted_capacity_rejected :
    validate (moduleOf array (breaking (.bytes array [65] 0))) =
      .error ⟨.summary, "entry may abort, which its summary omits"⟩ := by cbv

theorem breaking_capacity_declared :
    validate (moduleOf array (breaking (.bytes array [65] 0)) true) = .ok () := by cbv

theorem branching_omitted_capacity_rejected :
    validate (moduleOf array (branching (.bytes array [65] 0))) =
      .error ⟨.summary, "entry may abort, which its summary omits"⟩ := by cbv

private def packedBreak : Module :=
  let first := Expr.ifE (.bool true)
    (.mk 2 [.breakValue (.values [.bytes array [65] 0, .bytes array [66] 0]) 0] none)
    (.mk 3 [] (some (.bytes array [67] 0))) 0
  let producer := breaking (.values [first, .bytes array [66] 0])
  let module := moduleOf array (.bytes array [65] 0)
  let entry : Impl := ⟨"entry", #[], #[],
    #[⟨"first", array, .immutable, 0, 0⟩, ⟨"second", array, .immutable, 0, 0⟩],
    .mk 0 [.receive [0, 1] (.call 1 [] 0) 0] none,
    .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩
  let implementation : Impl := ⟨"producer", #[],
    #[⟨array, .value, none⟩, ⟨array, .value, none⟩], #[],
    .mk 0 [] (some producer), .known ⟨[], [], [], [], [], [0, 1], [], [], false, false⟩⟩
  { module with
    impls := #[entry, implementation]
    contexts := #[⟨0, "entry", [], [], []⟩, ⟨1, "producer", [], [[], []], []⟩] }

theorem packed_break_omitted_capacity_rejected :
    validate packedBreak = .error ⟨.summary, "producer may abort, which its summary omits"⟩ := by cbv

theorem breaking_overflow_rejected :
    validate (moduleOf (.limited (.int .u8) 1) (breaking (.bytes array [65, 66] 0))) =
      .error ⟨.summary, "entry may abort, which its summary omits"⟩ := by cbv

theorem breaking_overflow_declared :
    validate (moduleOf (.limited (.int .u8) 1) (breaking (.bytes array [65, 66] 0)) true) =
      .ok () := by cbv

theorem branching_oversized_literal_rejected :
    validate (moduleOf (.limited (.int .u8) 1)
      (branching (.bytes (.limited (.int .u8) 1) [65, 66] 0))) =
      .error ⟨.summary, "entry may abort, which its summary omits"⟩ := by cbv

theorem branching_oversized_literal_declared :
    validate (moduleOf (.limited (.int .u8) 1)
      (branching (.bytes (.limited (.int .u8) 1) [65, 66] 0)) true) = .ok () := by cbv

private def unboundedSource (expression : Expr) : Module :=
  let module := moduleOf array (branching expression)
  { module with
    globals := #[⟨"source", .grow (.int .u8), .mutable,
      .arrLit (.grow (.int .u8)) [] 0, 0⟩]
    impls := module.impls.map fun implementation => { implementation with
      summary := .known ⟨[.global 0], [], [], [], [], [], [], [], false, false⟩ } }

theorem branching_unbounded_copy_rejected :
    validate (unboundedSource (.copy array (.global 0) 0)) =
      .error ⟨.summary, "entry may abort, which its summary omits"⟩ := by cbv

theorem branching_unbounded_string_rejected :
    validate (unboundedSource (.str array [.view (.of (.global 0))] 0)) =
      .error ⟨.summary, "entry may abort, which its summary omits"⟩ := by cbv

private def outcome (profile : Goose.Core.NumProfile) (module : Module) : Option Goose.Core.Outcome :=
  match eval 100 profile module with
  | .done result _ _ => some result
  | _ => none

theorem breaking_bounded_execution :
    outcome .release (moduleOf array (breaking (.bytes array [65] 0))) = some .returned ∧
    outcome .debug (moduleOf array (breaking (.bytes array [65] 0))) = some .returned := by cbv

theorem breaking_overflow_execution :
    outcome .release (moduleOf (.limited (.int .u8) 1) (breaking (.bytes array [65, 66] 0)) true) =
      some (.aborted .capacity 0) ∧
    outcome .debug (moduleOf (.limited (.int .u8) 1) (breaking (.bytes array [65, 66] 0)) true) =
      some (.aborted .capacity 0) := by cbv

end Goose.Construct.SummaryCapacityChecks
