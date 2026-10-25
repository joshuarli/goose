import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites
import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.SummaryPreservationStoppedGraph

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem accessChildPresent {root parent child : DemandNode}
    (present : ∃ path, DemandNodeAt root path parent) (index : Nat)
    (selected : parent.child? index = some child) : ∃ path, DemandNodeAt root path child := by
  obtain ⟨path, found⟩ := present
  exact ⟨path ++ [index], found.snoc index selected⟩

theorem accessChildNode {parent child : DemandNode} (index : Nat)
    (selected : parent.child? index = some child) : DemandNodeAt parent [index] child :=
  .child selected (.here child)

theorem accessOperandPlace {env : PEnv} {root : DemandNode} {func : Func} {upper : Prov}
    {place : Place} {path : List Nat} {before after : RState} {roots : List RootRef} {value : ValueId}
    (node : DemandNodeAt root path (.place place))
    (source : rpPlace env place before = .ok (roots, after))
    (bounded : value < upper.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
    OperandOccurrence env root func upper value :=
  ⟨path, .place place, before, roots, after, node, .place rfl source, bounded, refined⟩

theorem accessOperandView {env : PEnv} {root : DemandNode} {func : Func} {upper : Prov}
    {view : View} {path : List Nat} {before after : RState} {roots : List RootRef} {value : ValueId}
    (node : DemandNodeAt root path (.view view))
    (source : rpView env view before = .ok (roots, after))
    (bounded : value < upper.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
    OperandOccurrence env root func upper value :=
  ⟨path, .view view, before, roots, after, node, .view rfl source, bounded, refined⟩

theorem accessOperandExpression {env : PEnv} {root : DemandNode} {func : Func} {upper : Prov}
    {expression : Expr} {path : List Nat} {before after : RState} {roots : List RootRef} {value : ValueId}
    (node : DemandNodeAt root path (.expression expression))
    (source : rpExpr env expression before = .ok (roots, after))
    (bounded : value < upper.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
    OperandOccurrence env root func upper value :=
  ⟨path, .expression expression, before, roots, after, node, .expression rfl source, bounded, refined⟩

theorem accessEmitDefinition {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {le : LEnv} {before after : LS}
    {op : Op} {value : ValueId} (run : emitDef op le before = (value, after))
    (valid : before.cur.isSome = true → InstructionOccurrences env root func types upper (.def value op)) :
    OccurrenceLedger env root func types upper before after := by
  cases current : before.cur with
  | none => exact .of_blocks ((stopped_emitDef op) le before value after run current).2.1
  | some block =>
    have resultEq : value = before.vals.size := by
      rw [emitDef_run op le current] at run
      exact (congrArg Prod.fst run).symm
    exact emitsOnly_emitDef run (by simpa only [resultEq] using valid (by simp [current]))

theorem accessRootsGrowth {module : GIR.Module} {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {before after : LS} {old next : Prov}
    (first : ReplayBuilder module results types func target le scopeCount slots before old)
    (last : ReplayBuilder module results types func target le scopeCount slots after next)
    (growth : before.vals.size ≤ after.vals.size) : old.vals.size ≤ next.vals.size := by
  rw [first.roots.valueSize, last.roots.valueSize]
  exact growth

end Goose.Lower.Validation.ReplacementContentFlowSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem accessEmitCurrent {le : LEnv} {before after : LS} {op : Op} {value : ValueId}
    (run : emitDef op le before = (value, after)) : after.cur = before.cur := by
  cases current : before.cur with
  | none => rw [emitDef_none op le current] at run; cases run; exact current
  | some block => rw [emitDef_run op le current] at run; cases run; exact current

theorem accessDefinitionNoOperands {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {value : ValueId} {op : Op}
    (empty : GIR.ReplacementContentFlow.Model.accessOperands (.def value op) = [])
    (notLoad : ∀ address, op ≠ .load address)
    (notCall : ∀ callee args origin, op ≠ .call callee args origin) :
    InstructionOccurrences env root func types upper (.def value op) := by
  refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
  · simp only [empty, List.not_mem_nil, false_implies, implies_true]
  · intro found address same
    cases same
    exact (notLoad address rfl).elim
  · intro found callee args origin same
    cases same
    exact (notCall callee args origin rfl).elim
  · simp only [empty, List.not_mem_nil, false_implies, implies_true]

end Goose.Lower.Validation.ReplacementContentFlowSource
