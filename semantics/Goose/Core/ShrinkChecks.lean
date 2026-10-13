import Goose.Core.Run
import Goose.Core.Writer
import Goose.Core.Guarantees

namespace Goose.Core.ShrinkChecks

def returned (out : String) : String := "[\"done\",[\"returned\"]," ++ Run.quote out ++ "]"
def aborted (kind out : String) : String :=
  "[\"done\",[\"aborted\"," ++ Run.quote kind ++ ",3]," ++ Run.quote out ++ "]"

def roundtrip (bytes : String) : Bool :=
  match Decode.decodeBytes bytes.toUTF8 with
  | .error _ => false
  | .ok m => Writer.module m == bytes.trimAscii.toString

def runs (bytes expected : String) : Bool :=
  [NumProfile.release, .debug].all fun profile =>
    Run.runBytes { profile, fuel := 1000 } bytes.toUTF8 == (expected, 0)

def rejects (bytes rule : String) : Bool :=
  match Decode.decodeBytes bytes.toUTF8 with
  | .error _ => false
  | .ok m => match validate m with
    | .ok () => false
    | .error r => r.rule.tag == rule

#guard runs (include_str "../../../test/semantics/golden/shrink_last_use.core.json") (returned "2\n1\n")
#guard rejects (include_str "../../../test/semantics/golden/shrink_live_slice.core.json") "V-SHRINK"
#guard rejects (include_str "../../../test/semantics/golden/shrink_loop_alias.core.json") "V-SHRINK"
#guard rejects (include_str "../../../test/semantics/golden/shrink_retained_destination.core.json") "V-SHRINK"
#guard runs (include_str "../../../test/semantics/golden/shrink_loaded_scalar.core.json") (returned "30\n")
#guard runs (include_str "../../../test/semantics/golden/limited_kept_reference.core.json") (returned "20\n30\n2\n")
#guard runs (include_str "../../../test/semantics/golden/limited_capacity.core.json") (aborted "capacity" "2\n")
#guard runs (include_str "../../../test/semantics/golden/shrink_pop_empty.core.json") (aborted "pop_empty" "")
#guard runs (include_str "../../../test/semantics/golden/shrink_pop_negative.core.json") (aborted "pop_n_range" "")
#guard runs (include_str "../../../test/semantics/golden/shrink_pop_excess.core.json") (aborted "pop_n_range" "")
#guard runs (include_str "../../../test/semantics/golden/shrink_resize_negative.core.json") (aborted "resize_negative" "")
#guard runs (include_str "../../../test/semantics/golden/shrink_resize_fill.core.json") (aborted "resize_fill" "")
#guard runs (include_str "../../../test/semantics/golden/shrink_resize_equal_fill.core.json") (returned "fill\n2\n")
#guard runs (include_str "../../../test/semantics/golden/shrink_count_order.core.json") (returned "count\n2\n")
#guard runs (include_str "../../../test/semantics/golden/shrink_replace.core.json") (returned "rhs\n1\n42\n")
#guard rejects (include_str "../../../test/semantics/golden/shrink_replace_dependency.core.json") "V-WHOLE"
#guard runs (include_str "../../../test/semantics/golden/shrink_replace_abort.core.json") (aborted "user_abort" "rhs\n")
#guard runs (include_str "../../../test/semantics/golden/shrink_by_value_iteration.core.json") (returned "10\n0\n")
#guard rejects (include_str "../../../test/semantics/golden/shrink_call_live.core.json") "V-SHRINK"
#guard runs (include_str "../../../test/semantics/golden/shrink_call_last_use.core.json") (returned "2\n1\n")
#guard rejects (include_str "../../../test/semantics/golden/shrink_summary_omission.core.json") "V-SUMMARY"
#guard rejects (include_str "../../../test/semantics/golden/shrink_retained_argument.core.json") "V-SHRINK"
#guard runs (include_str "../../../test/semantics/golden/limited_visible_index.core.json")
  "[\"done\",[\"aborted\",\"index_oob\",2],\"\"]"
#guard runs (include_str "../../../test/semantics/golden/limited_unwritten_index.core.json")
  "[\"done\",[\"aborted\",\"index_oob\",2],\"\"]"
#guard (Run.validateBytes (include_str "../../../test/semantics/golden/shrink_missing_push_origin.core.json").toUTF8).2 = 2
#guard (Run.validateBytes (include_str "../../../test/semantics/golden/shrink_six_field_summary.core.json").toUTF8).2 = 2

#guard runs (include_str "../../../test/semantics/golden/shrink_let_pop.core.json") (returned "1\n")
#guard rejects (include_str "../../../test/semantics/golden/shrink_let_replace.core.json") "V-MUT"
#guard runs (include_str "../../../test/semantics/golden/shrink_let_reference_replace.core.json") (returned "1\n")
#guard runs (include_str "../../../test/semantics/golden/shrink_whole_header.core.json") (returned "1\n")
#guard runs (include_str "../../../test/semantics/golden/shrink_future_reference.core.json") (returned "10\n")
#guard rejects (include_str "../../../test/semantics/golden/shrink_rebind_is_not_kill.core.json") "V-SHRINK"
#guard rejects (include_str "../../../test/semantics/golden/shrink_retained_index_run.core.json") "V-SHRINK"
#guard rejects (include_str "../../../test/semantics/golden/shrink_retained_slice_run.core.json") "V-SHRINK"
#guard rejects (include_str "../../../test/semantics/golden/shrink_retained_iteration.core.json") "V-SHRINK"
#guard runs (include_str "../../../test/semantics/golden/shrink_resize_fill_before_negative.core.json") (aborted "resize_negative" "fill\n")
#guard runs (include_str "../../../test/semantics/golden/shrink_resize_u64_negative.core.json") (aborted "resize_negative" "")
#guard runs (include_str "../../../test/semantics/golden/limited_resize_reuses_slot.core.json") (returned "20\n40\n2\n")
#guard runs (include_str "../../../test/semantics/golden/limited_resize_capacity.core.json") (aborted "capacity" "")
#guard runs (include_str "../../../test/semantics/golden/limited_resize_fill_before_capacity.core.json") (aborted "capacity" "fill\n")
#guard match Decode.decodeBytes (include_str "../../../test/semantics/golden/shrink_live_slice.core.json").toUTF8 with
  | .error _ => false
  | .ok m => (stageRejections m).any (fun r => r.rule == .shrink)
#guard match Decode.decodeBytes (include_str "../../../test/semantics/golden/shrink_last_use.core.json").toUTF8 with
  | .error _ => false
  | .ok m => match deriveModuleDemand m with
    | .error _ => false
    | .ok plans => plans.size == m.contexts.size + m.globals.size &&
      plans.toList.any (fun plan => plan.toList.any (fun point => point.phase == .mutation && point.active.contains 1 && !point.future.contains 1))
#guard roundtrip (include_str "../../../test/semantics/golden/shrink_last_use.core.json")
#guard roundtrip (include_str "../../../test/semantics/golden/shrink_call_last_use.core.json")
#guard roundtrip (include_str "../../../test/semantics/golden/limited_resize_reuses_slot.core.json")
#guard roundtrip (include_str "../../../test/semantics/golden/shrink_let_reference_replace.core.json")
#guard roundtrip (include_str "../../../test/semantics/golden/first.core.json")

#guard runs (include_str "../../../test/semantics/golden/limited_resize_large.core.json") (aborted "capacity" "")

#guard runs (include_str "../../../test/semantics/golden/shrink_loop_local_last_use.core.json") (returned "10\n1\n")

def clearedBeforeAbort : Bool :=
  match Decode.decodeBytes (include_str "../../../test/semantics/golden/shrink_replace_abort.core.json").toUTF8 with
  | .error _ => false
  | .ok m =>
    match m.impls[0]? with
    | none => false
    | some impl =>
      match impl.body.stmts[1]? with
      | none => false
      | some stmt =>
        let root := RootInst.local 0 0 0
        let state : St := ⟨Store.empty.introduce root (.resizable (.int .i64) #[.int .i64 10, .int .i64 20]), "", 1, 1⟩
        match execStmt 100 ⟨.release, m⟩ ⟨impl.vars, 0, [(0, 0)], 0⟩ stmt state with
        | .stop (.abort .userAbort 2) stopped =>
          stopped.trace == "rhs\n" && (match stopped.store.length ⟨root, []⟩ with | .ok 0 => true | _ => false)
        | _ => false

#guard clearedBeforeAbort

end Goose.Core.ShrinkChecks
