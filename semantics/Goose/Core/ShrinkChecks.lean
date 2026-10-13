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

def emptyArrayAliasModule : Module :=
  let ownerElem := Ty.arr .bool 0
  let aliasElem := Ty.arr (.int .i64) 0
  let ownerTy := Ty.growshrink ownerElem
  let helper : Impl := {
    name := "shrinkWithEmptyAlias"
    params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩]
    results := #[]
    vars := #[
      ⟨"values", .ref .mutable ownerTy, .immutable, 0, 0⟩,
      ⟨"alias", .ref .mutable aliasElem, .immutable, 0, 0⟩]
    body := .mk 0 [
      .clear (.deref (.read (.var 0))) 0,
      .print [.expr (.len (.of (.deref (.read (.var 1)))))] 0] none
    summary := .unknown }
  let main : Impl := {
    name := "main"
    params := #[]
    results := #[]
    vars := #[
      ⟨"values", ownerTy, .mutable, 0, 0⟩,
      ⟨"empty", aliasElem, .mutable, 0, 0⟩]
    body := .mk 0 [
      .letS 0 (.arrLit ownerTy []) 0,
      .letS 1 (.arrLit aliasElem []) 0,
      .expr (.call 1 [.byRef .mutable (.var 0), .byRef .mutable (.var 1)] 0) 0] none
    summary := .unknown }
  { files := #["shrink_empty_array_alias.goose"]
    types := #[]
    globals := #[]
    impls := #[main, helper]
    contexts := #[
      ⟨0, "main()", [], [], []⟩,
      ⟨1, "shrinkWithEmptyAlias", [(0, [.param 0]), (1, [.param 1])], [], []⟩]
    entry := 0
    origins := #[⟨0, 1, "stmt"⟩]
    profile := .shrink }

def clearRequestMatchesOwner : Bool :=
  match DemandNode.expectedPoints emptyArrayAliasModule 1 with
  | .error _ => false
  | .ok expected =>
    match expected.find? (fun point => point.path == [0] && point.phase == .mutation) with
    | none => false
    | some point =>
      match demandAccess? emptyArrayAliasModule 1 with
      | none => false
      | some access =>
        let place := Place.deref (.read (.var 0))
        match access.owner place with
        | .error _ => false
        | .ok owner => point.node.isDirectShrink && point.shrinkOwners == [owner]

def wholeReplacementReferenceAliasModule : Module :=
  let elem := Ty.int .i64
  let ownerTy := Ty.growshrink elem
  let main : Impl := {
    name := "wholeReplacementReferenceAlias"
    params := #[]
    results := #[]
    vars := #[
      ⟨"values", ownerTy, .mutable, 0, 0⟩,
      ⟨"slot", .ref .mutable elem, .immutable, 0, 0⟩]
    body := .mk 0 [
      .letS 0 (.arrLit ownerTy [.lit .i64 10]) 0,
      .letS 1 (.ref .mutable (.elem (.of (.var 0)) (.lit .i64 0) 0)) 0,
      .assignWhole (.var 0)
        (.arrLit ownerTy [.read (.deref (.read (.var 1)))]) 0] none
    summary := .unknown }
  { files := #["whole_replacement_reference_alias.goose"]
    types := #[]
    globals := #[]
    impls := #[main]
    contexts := #[⟨0, "main()", [(1, [.local 0])], [], []⟩]
    entry := 0
    origins := #[⟨0, 1, "stmt"⟩]
    profile := .shrink }

def wholeReplacementReferenceAliasIsLive : Bool :=
  match DemandNode.expectedPoints wholeReplacementReferenceAliasModule 0 with
  | .error _ => false
  | .ok expected =>
    match expected.find? (fun point => point.path == [2] && point.phase == .mutation) with
    | none => false
    | some point => point.frame.future.contains 1

#guard runs (include_str "../../../test/semantics/golden/shrink_last_use.core.json") (returned "2\n1\n")
#guard match validate emptyArrayAliasModule with
  | .error rejection => rejection.rule == .shrink
  | .ok _ => false
#guard clearRequestMatchesOwner
#guard wholeReplacementReferenceAliasIsLive
#guard match validate wholeReplacementReferenceAliasModule with
  | .error rejection => rejection.rule == .shrink
  | .ok _ => false
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

#guard rejects (include_str "../../../test/semantics/golden/limited_let_mutable_borrow.core.json") "V-MUT"
#guard runs (include_str "../../../test/semantics/golden/grow_let_reference_replace.core.json") (returned "1\n")
#guard rejects (include_str "../../../test/semantics/golden/shrink_wrapper_rebind_omission.core.json") "V-SUMMARY"
#guard rejects (include_str "../../../test/semantics/golden/shrink_whole_transitive_rebind.core.json") "V-WHOLE"

#guard [.popN (.var 0) (.lit .i64 0) 0,
  .resize (.var 0) (.lit .i64 0) none 0, .clear (.var 0) 0,
  .assignWhole (.var 0) (.arrLit (.growshrink (.int .i64)) []) 0].all fun stmt =>
    stmtsStop (fun _ => false) [stmt, .abort "stop" 0]

end Goose.Core.ShrinkChecks
