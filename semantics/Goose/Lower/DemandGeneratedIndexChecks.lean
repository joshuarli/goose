import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.DemandRetainedRows
import Goose.Evidence.Execution

namespace Goose.Lower.DemandGeneratedIndexChecks

open Goose.Core Goose.GIR Goose.Proofs.Lower

private def indexBlock : Core.Block := .mk 0 [.clear (.global 0) 0] (some (.lit .i64 0))
private def indexExpression : Expr := .blockE indexBlock
private def ownerView : View := .of (.global 0)
private def elementPlace : Place := .elem ownerView indexExpression 0
private def indexedExpression : Expr := .read elementPlace
private def indexedGlobal : Core.Global := ⟨"indexed", .int .i64, .mutable, indexedExpression, 0⟩
private def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }

private def sourceModule (limited : Bool) : Core.Module :=
  let owner := if limited then Ty.limited (.int .i64) 1 else Ty.growshrink (.int .i64)
  { files := #["retained.goose"], types := #[],
    globals := #[⟨"owner", owner, .mutable, .arrLit owner [.lit .i64 9], 0⟩, indexedGlobal],
    impls := #[implementation], contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

private def source : Core.Module := sourceModule true
private def function : Func := (lowerGlobal source indexedGlobal).init
private def environment : LEnv := lowerEnv source #[] [.int .i64]
private def root : DemandNode := .expression indexedExpression
private def indexBefore : LS := (lowerView ownerView environment startLS).2
private def clearBefore : LS :=
  (lowerStmts none (indexBlock.stmts.take 0) environment
    (demandBlockStatementsBefore environment indexBefore [] indexBlock)).2
private def valueBefore : LS := demandBlockValueBefore environment indexBefore none [] indexBlock

#guard match Core.validate source with
  | .ok () => true
  | .error _ => false

#guard match Core.validate (sourceModule false) with
  | .error rejection => rejection.rule == .shrink
  | .ok () => false

private theorem rootOccurrence :
    GeneratedDemandOccurrence source function environment root [] (.expression indexedExpression) startLS :=
  .globalRoot (globalId := 1) (by rfl)

private theorem placeOccurrence :
    GeneratedDemandOccurrence source function environment root [0] (.place elementPlace) startLS :=
  .first rootOccurrence (.expressionPlace rfl)

private theorem viewOccurrence :
    GeneratedDemandOccurrence source function environment root [0, 0] (.view ownerView) startLS :=
  .first placeOccurrence (.placeView rfl)

private theorem addressOccurrence :
    GeneratedDemandOccurrence source function environment root [0, 0, 0] (.place (.global 0)) startLS :=
  .first viewOccurrence (.viewPlace rfl)

private theorem indexOccurrence :
    GeneratedDemandOccurrence source function environment root [0, 1] (.expression indexExpression) indexBefore :=
  .index placeOccurrence

private theorem blockOccurrence :
    GeneratedDemandOccurrence source function environment root [0, 1, 0] (.block none [] true indexBlock) indexBefore :=
  .first indexOccurrence (.expressionBlock indexBlock)

private theorem clearOccurrence :
    GeneratedDemandOccurrence source function environment root [0, 1, 0, 0]
      (.statement none (.clear (.global 0) 0)) clearBefore :=
  .blockStatement blockOccurrence (index := 0) (by rfl)

private theorem clearAddressOccurrence :
    GeneratedDemandOccurrence source function environment root [0, 1, 0, 0, 0]
      (.place (.global 0)) clearBefore :=
  .clearPlace clearOccurrence

private theorem valueOccurrence :
    GeneratedDemandOccurrence source function environment root [0, 1, 0, 1]
      (.expression (.lit .i64 0)) valueBefore :=
  .blockValue blockOccurrence (by rfl)

private def access : AccessEnv := (⟨source, initImpl, initContext, []⟩ : PEnv).access
private def empty : RetainedSsaMap := ⟨[], []⟩
private def sampledAlias : RetainedAlias := ⟨.slice .readOnly (.int .i64), [.global 0], .operand [0, 0]⟩
private def sampledRows : RetainedSsaMap := ⟨[], [(1, sampledAlias)]⟩

private theorem rootRows : GeneratedDemandRows source access rootOccurrence empty := .globalRoot (globalId := 1) (globalAt := by rfl) rfl
private theorem placeRows : GeneratedDemandRows source access placeOccurrence empty := .first (first := .expressionPlace rfl) rootRows
private theorem viewRows : GeneratedDemandRows source access viewOccurrence empty := .first (first := .placeView rfl) placeRows
private theorem addressRows : GeneratedDemandRows source access addressOccurrence empty := .first (first := .viewPlace rfl) viewRows

private theorem indexRows : GeneratedDemandRows source access indexOccurrence sampledRows := by
  exact .index (aliases := [sampledAlias]) placeRows (by cbv)

private theorem blockRows : GeneratedDemandRows source access blockOccurrence sampledRows := .first (first := .expressionBlock indexBlock) indexRows
private theorem clearRows : GeneratedDemandRows source access clearOccurrence sampledRows := .blockStatement (statementAt := by rfl) blockRows
private theorem clearAddressRows : GeneratedDemandRows source access clearAddressOccurrence sampledRows := .clearPlace clearRows
private theorem valueRows : GeneratedDemandRows source access valueOccurrence sampledRows := .blockValue (valueAt := by rfl) blockRows

private theorem rootExtended : ExtT (lowerExpr indexedExpression environment startLS).2 function.blocks :=
  generated_global_expression_extended source indexedGlobal

private theorem placeExtended : ExtT (lowerPlace elementPlace environment startLS).2 function.blocks :=
  generated_read_place_extended rootExtended

private theorem viewExtended : ExtT (lowerView ownerView environment startLS).2 function.blocks :=
  generated_index_view_extended placeExtended

private theorem addressExtended : ExtT (lowerPlace (.global 0) environment startLS).2 function.blocks :=
  generated_view_place_extended viewExtended

private theorem blockExtended : ExtT (lowerBlock none [] true indexBlock environment indexBefore).2 function.blocks :=
  generated_index_expression_extended placeExtended

private theorem clearExtended : ExtT (lowerStmt none (.clear (.global 0) 0) environment clearBefore).2 function.blocks :=
  generated_block_statement_extended (index := 0) (by rfl) (point := (0, 3)) (by cbv) blockExtended

private theorem clearAddressExtended : ExtT (lowerPlace (.global 0) environment clearBefore).2 function.blocks :=
  generated_clear_place_extended clearExtended

private theorem valueExtended : ExtT (lowerExpr (.lit .i64 0) environment valueBefore).2 function.blocks := by
  simpa only [valueBefore, indexBlock, Core.Block.value, lowerBlockValue, ite_true] using generated_block_value_extended blockExtended

theorem generated_address :
    GeneratedDemandInstruction source access function empty ⟨[0, 0, 0], .place, .entry⟩ (0, 0) (.def 0 (.globalAddr 0)) := by
  exact .globalAddress_auto addressOccurrence addressRows (by cbv) addressExtended

theorem generated_snapshot :
    GeneratedDemandInstruction source access function empty ⟨[0, 0], .view, .exit⟩ (0, 1) (.def 1 (.snapshot .owner 0)) := by
  exact .snapshot_auto viewOccurrence viewRows (by cbv) viewExtended

theorem generated_index_entry :
    GeneratedDemandInstruction source access function sampledRows ⟨[0, 1, 0], .block, .entry⟩ (0, 2) (.eff (.enter 0)) := by
  exact .blockEnter_auto blockOccurrence blockRows (by cbv) blockExtended

theorem generated_clear_address :
    GeneratedDemandInstruction source access function sampledRows ⟨[0, 1, 0, 0, 0], .place, .entry⟩ (0, 3) (.def 2 (.globalAddr 0)) := by
  exact .globalAddress_auto clearAddressOccurrence clearAddressRows (by cbv) clearAddressExtended

theorem generated_clear :
    GeneratedDemandInstruction source access function sampledRows ⟨[0, 1, 0, 0, 0], .place, .exit⟩ (0, 4) (.eff (.clear 2 (some 0))) := by
  exact .clear_auto clearOccurrence clearRows (by cbv) clearExtended

theorem generated_index_value :
    GeneratedDemandInstruction source access function sampledRows ⟨[0, 1, 0, 1], .expression, .entry⟩ (0, 5) (.def 3 (.constInt .i64 0)) := by
  exact .literal_auto valueOccurrence valueRows (by cbv) valueExtended

theorem generated_index_leave :
    GeneratedDemandInstruction source access function sampledRows ⟨[0, 1, 0, 1], .expression, .exit⟩ (0, 6) (.eff (.leave 0)) := by
  exact .blockLeave_auto blockOccurrence blockRows (by cbv) blockExtended

theorem generated_index_check :
    GeneratedDemandInstruction source access function sampledRows ⟨[0, 1], .expression, .exit⟩ (0, 7)
      (.def 4 (.indexChecked 1 3 (some 0))) := by
  exact .indexChecked_auto placeOccurrence indexRows (by cbv) placeExtended

theorem generated_load :
    GeneratedDemandInstruction source access function empty ⟨[0], .place, .exit⟩ (0, 8) (.def 5 (.load 4)) := by
  exact .load_auto rootOccurrence rootRows (by cbv) rootExtended

theorem generated_return :
    GeneratedDemandInstruction source access function empty ⟨[], .expression, .exit⟩ (0, 9) (.term (.ret [5] (some 0))) := by
  exact .globalReturn_auto (globalId := 1) (by rfl) rootRows (by cbv)

theorem empty_map_cannot_cover_index_rhs : ¬ empty.Covers sampledRows := by
  intro coverage
  have missing := coverage.2 (1, sampledAlias) (by simp [sampledRows])
  cases missing

private def instructions : List Inst :=
  [.def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0), .eff (.enter 0),
    .def 2 (.globalAddr 0), .eff (.clear 2 (some 0)), .def 3 (.constInt .i64 0),
    .eff (.leave 0), .def 4 (.indexChecked 1 3 (some 0)), .def 5 (.load 4), .term (.ret [5] (some 0))]

private theorem functionCode : function.blocks = #[⟨[], instructions⟩] := by cbv

private theorem step_inside {point next : Pt} (inside : point.1 = 0 ∧ point.2 ≤ 9)
    (step : Evidence.ControlStep function point next) : next.1 = 0 ∧ next.2 ≤ 9 := by
  rcases point with ⟨block, position⟩
  obtain ⟨rfl, bounded⟩ := inside
  cases step with
  | definition instruction =>
    have beforeReturn : position < 9 := by
      by_cases early : position < 9
      · exact early
      · have equal : position = 9 := by omega
        subst position
        rw [generated_return.instruction] at instruction
        cases instruction
    exact ⟨rfl, by omega⟩
  | effect instruction =>
    have beforeReturn : position < 9 := by
      by_cases early : position < 9
      · exact early
      · have equal : position = 9 := by omega
        subst position
        rw [generated_return.instruction] at instruction
        cases instruction
    exact ⟨rfl, by omega⟩
  | @branch term target instruction successor =>
    have blockAt : function.blocks[0]? = some ⟨[], instructions⟩ := by rw [functionCode]; rfl
    have lookup : instructions[position]? = some (.term term) := by
      simpa only [instAt, blockAt, Option.bind_some] using instruction
    have member := List.mem_of_getElem? lookup
    have returned : term = Term.ret [5] (some 0) := by simpa [instructions] using member
    subst term
    simp only [Term.successors, List.not_mem_nil] at successor

private theorem path_inside {first last : Pt} (path : Evidence.ControlPath function [] first last)
    (inside : first.1 = 0 ∧ first.2 ≤ 9) : last.1 = 0 ∧ last.2 ≤ 9 := by
  induction path with
  | refl => exact inside
  | next step unwritten rest induction => exact induction (step_inside inside step)

theorem runtime_point_has_generated_instruction {configuration : GCfg} {point : Pt} {frame : Frame} {state : St}
    (reached : Evidence.RuntimePoint configuration function point frame state) :
    ∃ (required : RetainedSsaMap) (label : DemandSourceLabel) (inst : Inst),
      GeneratedDemandInstruction source access function required label point inst := by
  obtain ⟨block, bounded⟩ := path_inside reached.control_path ⟨rfl, by decide⟩
  rcases point with ⟨blockId, position⟩
  have zero : blockId = 0 := block
  subst blockId
  have positions : position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 ∨ position = 4 ∨
      position = 5 ∨ position = 6 ∨ position = 7 ∨ position = 8 ∨ position = 9 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, generated_address⟩
  · exact ⟨_, _, _, generated_snapshot⟩
  · exact ⟨_, _, _, generated_index_entry⟩
  · exact ⟨_, _, _, generated_clear_address⟩
  · exact ⟨_, _, _, generated_clear⟩
  · exact ⟨_, _, _, generated_index_value⟩
  · exact ⟨_, _, _, generated_index_leave⟩
  · exact ⟨_, _, _, generated_index_check⟩
  · exact ⟨_, _, _, generated_load⟩
  · exact ⟨_, _, _, generated_return⟩


end Goose.Lower.DemandGeneratedIndexChecks
