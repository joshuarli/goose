import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.DemandRetainedRows
import Goose.Evidence.Execution

namespace Goose.Lower.DemandGeneratedIndexChecks

open Goose.Core Goose.GIR Goose.Proofs.Lower

def retainedIndexBlock : Core.Block := .mk 0 [.clear (.global 0) 0] (some (.lit .i64 0))
def retainedIndexExpression : Expr := .blockE retainedIndexBlock
def retainedOwnerView : View := .of (.global 0)
def retainedElementPlace : Place := .elem retainedOwnerView retainedIndexExpression 0
def retainedIndexedExpression : Expr := .read retainedElementPlace
def retainedIndexedGlobal : Core.Global := ⟨"indexed", .int .i64, .mutable, retainedIndexedExpression, 0⟩
private def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }

def retainedIndexModule (limited : Bool) : Core.Module :=
  let owner := if limited then Ty.limited (.int .i64) 1 else Ty.growshrink (.int .i64)
  { files := #["retained.goose"], types := #[],
    globals := #[⟨"owner", owner, .mutable, .arrLit owner [.lit .i64 9], 0⟩, retainedIndexedGlobal],
    impls := #[implementation], contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

def retainedIndexSource : Core.Module := retainedIndexModule true
def retainedIndexFunction : Func := (lowerGlobal retainedIndexSource retainedIndexedGlobal).init
def retainedIndexEnvironment : LEnv := lowerEnv retainedIndexSource #[] [.int .i64]
def retainedIndexRoot : DemandNode := .expression retainedIndexedExpression
def retainedIndexBefore : LS := (lowerView retainedOwnerView retainedIndexEnvironment startLS).2
private def clearBefore : LS :=
  (lowerStmts none (retainedIndexBlock.stmts.take 0) retainedIndexEnvironment
    (demandBlockStatementsBefore retainedIndexEnvironment retainedIndexBefore [] retainedIndexBlock)).2
private def valueBefore : LS := demandBlockValueBefore retainedIndexEnvironment retainedIndexBefore none [] retainedIndexBlock

#guard match Core.validate retainedIndexSource with
  | .ok () => true
  | .error _ => false

#guard match Core.validate (retainedIndexModule false) with
  | .error rejection => rejection.rule == .shrink
  | .ok () => false

private theorem rootOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [] (.expression retainedIndexedExpression) startLS :=
  .globalRoot (globalId := 1) (by rfl)

theorem retainedPlaceOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [0] (.place retainedElementPlace) startLS :=
  .first rootOccurrence (.expressionPlace rfl)

private theorem viewOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [0, 0] (.view retainedOwnerView) startLS :=
  .first retainedPlaceOccurrence (.placeView rfl)

private theorem addressOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [0, 0, 0] (.place (.global 0)) startLS :=
  .first viewOccurrence (.viewPlace rfl)

private theorem indexOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [0, 1] (.expression retainedIndexExpression) retainedIndexBefore :=
  .index retainedPlaceOccurrence

theorem retainedBlockOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [0, 1, 0] (.block none [] true retainedIndexBlock) retainedIndexBefore :=
  .first indexOccurrence (.expressionBlock retainedIndexBlock)

private theorem clearOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [0, 1, 0, 0]
      (.statement none (.clear (.global 0) 0)) clearBefore :=
  .blockStatement retainedBlockOccurrence (index := 0) (by rfl)

private theorem clearAddressOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [0, 1, 0, 0, 0]
      (.place (.global 0)) clearBefore :=
  .clearPlace clearOccurrence

private theorem valueOccurrence :
    GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot [0, 1, 0, 1]
      (.expression (.lit .i64 0)) valueBefore :=
  .blockValue retainedBlockOccurrence (by rfl)

def retainedIndexAccess : AccessEnv := (⟨retainedIndexSource, initImpl, initContext, []⟩ : PEnv).access
def retainedEmptyRows : RetainedSsaMap := ⟨[], []⟩
def retainedSampleAlias : RetainedAlias := ⟨.slice .readOnly (.int .i64), [.global 0], .operand [0, 0]⟩
def retainedSampleRows : RetainedSsaMap := ⟨[], [(1, retainedSampleAlias)]⟩

private theorem rootRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess rootOccurrence retainedEmptyRows := .globalRoot (globalId := 1) (globalAt := by rfl) rfl
theorem retainedPlaceRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess retainedPlaceOccurrence retainedEmptyRows := .first (first := .expressionPlace rfl) rootRows
private theorem viewRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess viewOccurrence retainedEmptyRows := .first (first := .placeView rfl) retainedPlaceRows
private theorem addressRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess addressOccurrence retainedEmptyRows := .first (first := .viewPlace rfl) viewRows

private theorem indexRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess indexOccurrence retainedSampleRows := by
  exact .index (aliases := [retainedSampleAlias]) retainedPlaceRows (by cbv)

theorem retainedBlockRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess retainedBlockOccurrence retainedSampleRows := .first (first := .expressionBlock retainedIndexBlock) indexRows
private theorem clearRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess clearOccurrence retainedSampleRows := .blockStatement (statementAt := by rfl) retainedBlockRows
private theorem clearAddressRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess clearAddressOccurrence retainedSampleRows := .clearPlace clearRows
private theorem valueRows : GeneratedDemandRows retainedIndexSource retainedIndexAccess valueOccurrence retainedSampleRows := .blockValue (valueAt := by rfl) retainedBlockRows

private theorem rootExtended : ExtT (lowerExpr retainedIndexedExpression retainedIndexEnvironment startLS).2 retainedIndexFunction.blocks :=
  generated_global_expression_extended retainedIndexSource retainedIndexedGlobal

private theorem placeExtended : ExtT (lowerPlace retainedElementPlace retainedIndexEnvironment startLS).2 retainedIndexFunction.blocks :=
  generated_read_place_extended rootExtended

theorem retainedViewExtended : ExtT (lowerView retainedOwnerView retainedIndexEnvironment startLS).2 retainedIndexFunction.blocks :=
  generated_index_view_extended placeExtended

private theorem addressExtended : ExtT (lowerPlace (.global 0) retainedIndexEnvironment startLS).2 retainedIndexFunction.blocks :=
  generated_view_place_extended retainedViewExtended

theorem retainedBlockExtended : ExtT (lowerBlock none [] true retainedIndexBlock retainedIndexEnvironment retainedIndexBefore).2 retainedIndexFunction.blocks :=
  generated_index_expression_extended placeExtended

private theorem clearExtended : ExtT (lowerStmt none (.clear (.global 0) 0) retainedIndexEnvironment clearBefore).2 retainedIndexFunction.blocks :=
  generated_block_statement_extended (index := 0) (by rfl) (point := (0, 3)) (by cbv) retainedBlockExtended

private theorem clearAddressExtended : ExtT (lowerPlace (.global 0) retainedIndexEnvironment clearBefore).2 retainedIndexFunction.blocks :=
  generated_clear_place_extended clearExtended

private theorem valueExtended : ExtT (lowerExpr (.lit .i64 0) retainedIndexEnvironment valueBefore).2 retainedIndexFunction.blocks := by
  simpa only [valueBefore, retainedIndexBlock, Core.Block.value, lowerBlockValue, ite_true] using generated_block_value_extended retainedBlockExtended

theorem generated_address :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedEmptyRows ⟨[0, 0, 0], .place, .entry⟩ (0, 0) (.def 0 (.globalAddr 0)) := by
  exact .globalAddress_auto addressOccurrence addressRows (by cbv) addressExtended

theorem generated_snapshot :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedEmptyRows ⟨[0, 0], .view, .exit⟩ (0, 1) (.def 1 (.snapshot .owner 0)) := by
  exact .snapshot_auto viewOccurrence viewRows (by cbv) retainedViewExtended

theorem generated_index_entry :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedSampleRows ⟨[0, 1, 0], .block, .entry⟩ (0, 2) (.eff (.enter 0)) := by
  exact .blockEnter_auto retainedBlockOccurrence retainedBlockRows (by cbv) retainedBlockExtended

theorem generated_clear_address :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedSampleRows ⟨[0, 1, 0, 0, 0], .place, .entry⟩ (0, 3) (.def 2 (.globalAddr 0)) := by
  exact .globalAddress_auto clearAddressOccurrence clearAddressRows (by cbv) clearAddressExtended

theorem generated_clear :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedSampleRows ⟨[0, 1, 0, 0, 0], .place, .exit⟩ (0, 4) (.eff (.clear 2 (some 0))) := by
  exact .clear_auto clearOccurrence clearRows (by cbv) clearExtended

theorem generated_index_value :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedSampleRows ⟨[0, 1, 0, 1], .expression, .entry⟩ (0, 5) (.def 3 (.constInt .i64 0)) := by
  exact .literal_auto valueOccurrence valueRows (by cbv) valueExtended

theorem generated_index_leave :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedSampleRows ⟨[0, 1, 0, 1], .expression, .exit⟩ (0, 6) (.eff (.leave 0)) := by
  exact .blockLeave_auto retainedBlockOccurrence retainedBlockRows (by cbv) retainedBlockExtended

theorem generated_index_check :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedSampleRows ⟨[0, 1], .expression, .exit⟩ (0, 7)
      (.def 4 (.indexChecked 1 3 (some 0))) := by
  exact .indexChecked_auto retainedPlaceOccurrence indexRows (by cbv) placeExtended

theorem generated_load :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedEmptyRows ⟨[0], .place, .exit⟩ (0, 8) (.def 5 (.load 4)) := by
  exact .load_auto rootOccurrence rootRows (by cbv) rootExtended

theorem generated_return :
    GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction retainedEmptyRows ⟨[], .expression, .exit⟩ (0, 9) (.term (.ret [5] (some 0))) := by
  exact .globalReturn_auto (globalId := 1) (by rfl) rootRows (by cbv)

theorem empty_map_cannot_cover_index_rhs : ¬ retainedEmptyRows.Covers retainedSampleRows := by
  intro coverage
  have missing := coverage.2 (1, retainedSampleAlias) (by simp [retainedSampleRows])
  cases missing

private def instructions : List Inst :=
  [.def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0), .eff (.enter 0),
    .def 2 (.globalAddr 0), .eff (.clear 2 (some 0)), .def 3 (.constInt .i64 0),
    .eff (.leave 0), .def 4 (.indexChecked 1 3 (some 0)), .def 5 (.load 4), .term (.ret [5] (some 0))]

private theorem functionCode : retainedIndexFunction.blocks = #[⟨[], instructions⟩] := by cbv

private theorem step_inside {point next : Pt} (inside : point.1 = 0 ∧ point.2 ≤ 9)
    (step : Evidence.ControlStep retainedIndexFunction point next) : next.1 = 0 ∧ next.2 ≤ 9 := by
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
    have blockAt : retainedIndexFunction.blocks[0]? = some ⟨[], instructions⟩ := by rw [functionCode]; rfl
    have lookup : instructions[position]? = some (.term term) := by
      simpa only [instAt, blockAt, Option.bind_some] using instruction
    have member := List.mem_of_getElem? lookup
    have returned : term = Term.ret [5] (some 0) := by simpa [instructions] using member
    subst term
    simp only [Term.successors, List.not_mem_nil] at successor

private theorem path_inside {first last : Pt} (path : Evidence.ControlPath retainedIndexFunction [] first last)
    (inside : first.1 = 0 ∧ first.2 ≤ 9) : last.1 = 0 ∧ last.2 ≤ 9 := by
  induction path with
  | refl => exact inside
  | next step unwritten rest induction => exact induction (step_inside inside step)

theorem runtime_point_has_generated_instruction {configuration : GCfg} {point : Pt} {frame : Frame} {state : St}
    (reached : Evidence.RuntimePoint configuration retainedIndexFunction point frame state) :
    ∃ (required : RetainedSsaMap) (label : DemandSourceLabel) (inst : Inst),
      GeneratedDemandInstruction retainedIndexSource retainedIndexAccess retainedIndexFunction required label point inst := by
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
