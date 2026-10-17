import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceContracts
import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

namespace InstructionOccurrences

theorem of_def {env : PEnv} {root : DemandNode} {func : Func} {types : Array (Option VTy)}
    {upper : Prov} {result : ValueId} {op : Op}
    (operands : ∀ value ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def result op),
      OperandOccurrence env root func upper value)
    (noLoad : ∀ address, op ≠ .load address)
    (noCall : ∀ callee arguments origin, op ≠ .call callee arguments origin)
    (consumed : ∀ value ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def result op),
      ∀ mutability payload, types[value]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func types upper value) :
    InstructionOccurrences env root func types upper (.def result op) := by
  refine ⟨fun value member _ => operands value member, ?_, ?_, no_store (by intro address value origin same; cases same), consumed⟩
  · intro value address same _
    exact False.elim (noLoad address (Inst.def.inj same).2)
  · intro value callee arguments origin same
    exact False.elim (noCall callee arguments origin (Inst.def.inj same).2)

theorem term (env : PEnv) (root : DemandNode) (func : Func) (types : Array (Option VTy))
    (upper : Prov) (term : Term) : InstructionOccurrences env root func types upper (.term term) := by
  simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands]

theorem constUnit (env : PEnv) (root : DemandNode) (func : Func) (types : Array (Option VTy))
    (upper : Prov) (value : ValueId) : InstructionOccurrences env root func types upper (.def value .constUnit) := by
  simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses]

end InstructionOccurrences

theorem expression_operand_occurrence {env : PEnv} {root : DemandNode} {func : Func}
    {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {state : LS} {upper : Prov} {expression : Expr} {before after : RState}
    {roots : List RootRef} {value : ValueId} {type : VTy} {path : List Nat}
    (source : DemandNodeAt root path (.expression expression))
    (replayed : rpExpr env expression before = .ok (roots, after))
    (ready : ReplayBuilder module results types func target le scopeCount slots state upper)
    (typedValue : ReplayValue func upper state value roots type) :
    OperandOccurrence env root func upper value :=
  ⟨path, .expression expression, before, roots, after, source, .expression rfl replayed,
    by simpa only [ready.roots.valueSize] using typedValue.bound, typedValue.refined⟩

theorem OccurrenceLedger.replay_retained {env : PEnv} {root : DemandNode} {func : Func}
    {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {initial middle final : LS} {before after : Prov}
    (ledger : OccurrenceLedger env root func types before initial middle)
    (beforeReady : ReplayBuilder module results types func target le scopeCount slots middle before)
    (afterReady : ReplayBuilder module results types func target le scopeCount slots final after)
    (growth : middle.vals.size ≤ final.vals.size)
    (retained : ∀ old, old < before.vals.size → rootsAt after.vals old = rootsAt before.vals old) :
    OccurrenceLedger env root func types after initial middle :=
  ledger.retained (by simpa only [beforeReady.roots.valueSize, afterReady.roots.valueSize] using growth) retained

theorem occurrence_emitDef_live {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op}
    (run : Goose.Lower.emitDef op le before = (value, after))
    (valid : before.cur.isSome = true → InstructionOccurrences env root func types upper (.def before.vals.size op)) :
    OccurrenceLedger env root func types upper before after := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    cases run
    exact .refl _ _
  | some block => exact emitsOnly_emitDef run (valid (by simp [current]))

theorem OccurrenceLedger.emitDef {env : PEnv} {root : DemandNode} {func : Func}
    {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {initial before after : LS} {upper next : Prov} {value : ValueId} {op : Op}
    (ledger : OccurrenceLedger env root func types upper initial before)
    (beforeReady : ReplayBuilder module results types func target le scopeCount slots before upper)
    (afterReady : ReplayBuilder module results types func target le scopeCount slots after next)
    (run : Goose.Lower.emitDef op le before = (value, after))
    (retained : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old)
    (operands : before.cur.isSome = true →
      ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def before.vals.size op),
        OperandOccurrence env root func upper operand)
    (noLoad : ∀ address, op ≠ .load address)
    (noCall : ∀ callee arguments origin, op ≠ .call callee arguments origin)
    (consumed : before.cur.isSome = true →
      ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def before.vals.size op),
        ∀ mutability payload, types[operand]? = some (some (.data (.ref mutability payload))) →
          ConsumedReferenceOccurrence env root func types upper operand) :
    OccurrenceLedger env root func types next initial after := by
  have growth := (advB_emitDef op le before value after run).vals
  have ghostGrowth : upper.vals.size ≤ next.vals.size := by
    simpa only [beforeReady.roots.valueSize, afterReady.roots.valueSize] using growth
  have previous := ledger.replay_retained beforeReady afterReady growth retained
  have emitted : OccurrenceLedger env root func types next before after := by
    apply occurrence_emitDef_live run
    intro live
    refine InstructionOccurrences.of_def ?_ noLoad noCall ?_
    · intro operand member
      exact (operands live operand member).retained ghostGrowth retained
    · intro operand member mutability payload typed
      exact (consumed live operand member mutability payload typed).retained ghostGrowth retained
  exact previous.trans emitted

theorem OccurrenceSitesBuilder.emitDef_replay {env : PEnv} {siteRoot : DemandNode} {targets : List BlockId}
    {func : Func} {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {before after : LS} {upper next : Prov} {value : ValueId} {op : Op}
    (sites : OccurrenceSitesBuilder env siteRoot targets le before func types upper)
    (beforeReady : ReplayBuilder module results types func target le scopeCount slots before upper)
    (afterReady : ReplayBuilder module results types func target le scopeCount slots after next)
    (run : Goose.Lower.emitDef op le before = (value, after))
    (retained : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) :
    OccurrenceSitesBuilder env siteRoot targets le after func types next :=
  sites.emitDef run (by simpa only [beforeReady.roots.valueSize, afterReady.roots.valueSize]
    using (advB_emitDef op le before value after run).vals) retained

theorem OccurrenceLedger.emitDef_sites {env : PEnv} {root siteRoot : DemandNode} {targets : List BlockId}
    {func : Func} {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {initial before after : LS} {upper next : Prov} {value : ValueId} {op : Op}
    (ledger : OccurrenceLedger env root func types upper initial before)
    (sites : OccurrenceSitesBuilder env siteRoot targets le before func types upper)
    (beforeReady : ReplayBuilder module results types func target le scopeCount slots before upper)
    (afterReady : ReplayBuilder module results types func target le scopeCount slots after next)
    (run : Goose.Lower.emitDef op le before = (value, after))
    (retained : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old)
    (operands : before.cur.isSome = true →
      ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def before.vals.size op),
        OperandOccurrence env root func upper operand)
    (noLoad : ∀ address, op ≠ .load address)
    (noCall : ∀ callee arguments origin, op ≠ .call callee arguments origin)
    (consumed : before.cur.isSome = true →
      ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def before.vals.size op),
        ∀ mutability payload, types[operand]? = some (some (.data (.ref mutability payload))) →
          ConsumedReferenceOccurrence env root func types upper operand) :
    OccurrenceLedger env root func types next initial after ∧
      OccurrenceSitesBuilder env siteRoot targets le after func types next :=
  ⟨ledger.emitDef beforeReady afterReady run retained operands noLoad noCall consumed,
    sites.emitDef_replay beforeReady afterReady run retained⟩

#print axioms OccurrenceLedger.emitDef_sites

#print axioms OccurrenceLedger.emitDef

#print axioms expression_operand_occurrence
#print axioms OccurrenceLedger.replay_retained
#print axioms occurrence_emitDef_live

end Goose.Lower.Validation.ReplacementContentFlowSource
