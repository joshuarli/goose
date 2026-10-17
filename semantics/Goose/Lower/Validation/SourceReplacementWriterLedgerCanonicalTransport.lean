import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalSites
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlSteps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeSteps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSiteTargets
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsBasic
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorageCoercions
import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageActions
import Goose.Lower.GeneratedTargetFramesControl

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR
open Goose.Lower.Validation.ReplacementContentFlowSource
open Goose.Lower.Validation.SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}
  {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)}
  {old next : Prov}

theorem CanonicalOccurrenceSitesBuilder.of_action
    {action : B α} {result : α}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (emitted : EmitsOnlyRun NotReplacement action) (typed : TypeRun action)
    (framed : GeneratedTargetFrameRun none action) (run : action le before = (result, after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types next :=
  checked.of_emits (emitted le before result after run) (typed le before result after run)
    (.of_run framed run) growth retained

theorem CanonicalOccurrenceSitesBuilder.ghost_retained
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types next :=
  checked.of_emits (.refl _ _) (.refl _) (.of_blocks rfl) growth retained

theorem CanonicalOccurrenceSitesBuilder.emitEffect
    {effect : Effect} {result : Unit}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (ordinary : NotReplacement (.eff effect)) (run : emitEffect effect le before = (result, after)) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types old :=
  checked.mutationEffect ordinary run (Nat.le_refl _) (fun _ _ => rfl)

theorem CanonicalOccurrenceSitesBuilder.emitTerm
    {term : Term} {result : Unit}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target)
    (run : emitTerm term le before = (result, after)) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types old :=
  checked.of_emits (emitsOnly_emitTerm term trivial le before result after run)
    (types_emitTerm term le before result after run) (.emitTerm run allowed) (Nat.le_refl _) (fun _ _ => rfl)

theorem CanonicalOccurrenceSitesBuilder.of_blocks
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (blocks : after.blocks = before.blocks) (values : after.vals = before.vals) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types old :=
  checked.of_emits (.of_blocks blocks) (by intro value type row; simpa only [values] using row)
    (.of_blocks blocks) (Nat.le_refl _) (fun _ _ => rfl)

theorem CanonicalOccurrenceSitesBuilder.fork
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (condition : ValueId) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.fork condition le before).2 func types old :=
  checked.of_action (emitsOnly_fork _ (fun _ => trivial) condition) (types_fork condition)
    (generatedTargetFrame_fork none condition) rfl (Nat.le_refl _) (fun _ _ => rfl)

theorem CanonicalOccurrenceSitesBuilder.setCur
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (current : Option BlockId) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.setCur current le before).2 func types old :=
  checked.of_blocks rfl rfl

theorem CanonicalOccurrenceSitesBuilder.joinArms
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (yes no : Option BlockId) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.joinArms yes no le before).2 func types old :=
  checked.of_action (emitsOnly_joinArms (fun _ => trivial) yes no) (types_joinArms yes no)
    (generatedTargetFrame_joinArms none yes no) rfl (Nat.le_refl _) (fun _ _ => rfl)

theorem CanonicalOccurrenceSitesBuilder.joinValue
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (yes no : Option BlockId) (yesValue noValue : ValueId) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.joinValue yes yesValue no noValue le before).2 func types old :=
  checked.of_action (emitsOnly_joinValue NotReplacement (fun _ => by simp [NotReplacement]) yes no yesValue noValue)
    (types_joinValue yes yesValue no noValue)
    (generatedTargetFrame_joinValue none yes no yesValue noValue) rfl (Nat.le_refl _) (fun _ _ => rfl)

theorem CanonicalOccurrenceSitesBuilder.newBlock
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (parameters : List VTy) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.newBlock parameters le before).2 func types old :=
  checked.of_action (emitsOnly_newBlock _ parameters) (types_newBlock parameters)
    (generatedTargetFrame_newBlock none parameters) rfl (Nat.le_refl _) (fun _ _ => rfl)

theorem CanonicalOccurrenceSitesBuilder.recordValueRootRecipe
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (value : ValueId) (scope : ScopeId) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.recordValueRootRecipe value scope le before).2 func types old := by
  have blocks : (Goose.Lower.recordValueRootRecipe value scope le before).2.blocks = before.blocks := by
    rw [Goose.Lower.recordValueRootRecipe_run]
  have values : (Goose.Lower.recordValueRootRecipe value scope le before).2.vals = before.vals := by
    rw [Goose.Lower.recordValueRootRecipe_run]
  exact checked.of_blocks blocks values

def CanonicalSiteOccurrences.weaken {fewer : List BlockId}
    (site : CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root targets le before func types old
      block position owner value origin)
    (included : ∀ target ∈ fewer, target ∈ targets) :
    CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root fewer le before func types old
      block position owner value origin where
  site := site.site.weaken included
  source := by
    cases site.source with
    | inl baseline => exact .inl baseline
    | inr source => exact .inr (by simpa [SiteOccurrences.weaken, ReservedReplacementSiteAt.weaken] using source)

def CanonicalSiteOccurrences.reserve
    (site : CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root targets le before func types old
      block position owner value origin)
    (target : BlockId) (fresh : before.blocks.size ≤ target) :
    CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root (target :: targets) le before func types old
      block position owner value origin where
  site := site.site.reserve target fresh
  source := by
    cases site.source with
    | inl baseline => exact .inl baseline
    | inr source => exact .inr (by simpa [SiteOccurrences.reserve, ReservedReplacementSiteAt.reserve] using source)

def CanonicalSiteOccurrences.access_eq {other : PEnv}
    (site : CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root targets le before func types old
      block position owner value origin)
    (same : env.access = other.access) :
    CanonicalSiteOccurrences ownerRoot ownerInitial baseline other root targets le before func types old
      block position owner value origin where
  site := site.site.access_eq same
  source := by
    cases site.source with
    | inl baseline => exact .inl baseline
    | inr source => exact .inr source

theorem CanonicalSiteAuthority.weaken {fewer : List BlockId} {inst : Inst}
    (valid : CanonicalSiteAuthority ownerRoot ownerInitial baseline env root targets le before func types old block position inst)
    (included : ∀ target ∈ fewer, target ∈ targets) :
    CanonicalSiteAuthority ownerRoot ownerInitial baseline env root fewer le before func types old block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.weaken included⟩
  | _ => exact valid

theorem CanonicalSiteAuthority.reserve {inst : Inst}
    (valid : CanonicalSiteAuthority ownerRoot ownerInitial baseline env root targets le before func types old block position inst)
    (target : BlockId) (fresh : before.blocks.size ≤ target) :
    CanonicalSiteAuthority ownerRoot ownerInitial baseline env root (target :: targets) le before func types old block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.reserve target fresh⟩
  | _ => exact valid

theorem CanonicalSiteAuthority.access_eq {other : PEnv} {inst : Inst}
    (valid : CanonicalSiteAuthority ownerRoot ownerInitial baseline env root targets le before func types old block position inst)
    (same : env.access = other.access) :
    CanonicalSiteAuthority ownerRoot ownerInitial baseline other root targets le before func types old block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.access_eq same⟩
  | _ => exact valid

theorem CanonicalOccurrenceSitesBuilder.weaken {fewer : List BlockId}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (included : ∀ target ∈ fewer, target ∈ targets) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root fewer le before func types old :=
  fun block body row position inst lookup => (checked block body row position inst lookup).weaken included

theorem CanonicalOccurrenceSitesBuilder.reserve
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (target : BlockId) (fresh : before.blocks.size ≤ target) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root (target :: targets) le before func types old :=
  fun block body row position inst lookup => (checked block body row position inst lookup).reserve target fresh

theorem CanonicalOccurrenceSitesBuilder.access_eq {other : PEnv}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (same : env.access = other.access) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline other root targets le before func types old :=
  fun block body row position inst lookup => (checked block body row position inst lookup).access_eq same

theorem canonical_occurrenceSites_initSlots
    (bindings : List (SlotId × ValueId × OriginId))
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.initSlots bindings le before).2 func types old := by
  induction bindings generalizing before with
  | nil => exact checked
  | cons binding rest ih =>
    exact ih (checked.emitEffect (effect := .slotInit binding.1 binding.2.1 (some binding.2.2)) trivial rfl)

theorem CanonicalOccurrenceSitesBuilder.emitDef_replay {module : GIR.Module}
    {results : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {slots : Array (List RootRef)} {value : ValueId} {op : Op}
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (beforeReady : ReplayBuilder module results types func target le scopeCount slots before old)
    (afterReady : ReplayBuilder module results types func target le scopeCount slots after next)
    (run : Goose.Lower.emitDef op le before = (value, after))
    (retained : ∀ oldValue, oldValue < old.vals.size → rootsAt next.vals oldValue = rootsAt old.vals oldValue) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types next := by
  exact sites.emitDef run (by
    simpa only [beforeReady.roots.valueSize, afterReady.roots.valueSize] using
      (advB_emitDef op le before value after run).vals) retained

end Goose.Lower.Validation.SourceReplacementWriterLedger

namespace Goose.Lower.Validation.ReplacementContentFlowSource.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation
open Goose.Lower.Validation.SourceReplacementWriterLedger

theorem occurrenceCoerceSlot_canonicalSites {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {env : PEnv} {root siteRoot : DemandNode} {targets : List BlockId}
    {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {effect : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {state : LS} {upper : Prov} {block : BlockId} {value : ValueId}
    {path : List Nat} {node : DemandNode} {start finish : RState}
    {sourceRoots : List RootRef} {origin : OriginId}
    (slotId : SlotId)
    (ready : ReplayBuilder module results types func effect le scopeCount slots state upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot targets le state func types upper)
    (source : DemandNodeAt root path node)
    (replay : SourceNodeRoots env.access node start sourceRoots finish)
    (current : state.cur = some block) (valueBound : value < state.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : origin < le.mod.origins.size)
    (native : NativeRows types (coerceSlot slotId value origin le state).2) :
    ∃ next, ReplayBuilder module results types func effect le scopeCount slots (coerceSlot slotId value origin le state).2 next ∧
      GIR.RootsRefine func (rootsAt next.vals (coerceSlot slotId value origin le state).1) sourceRoots ∧
      (coerceSlot slotId value origin le state).2.cur = some block ∧
      (coerceSlot slotId value origin le state).1 < (coerceSlot slotId value origin le state).2.vals.size ∧
      (∀ oldValue, oldValue < upper.vals.size → rootsAt next.vals oldValue = rootsAt upper.vals oldValue) ∧
      OccurrenceLedger env root func types next state (coerceSlot slotId value origin le state).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot targets le
        (coerceSlot slotId value origin le state).2 func types next := by
  obtain ⟨next, nextReady, nextRefined, nextCurrent, nextBound, retained, ledger, _⟩ :=
    occurrenceCoerceSlot slotId origin ready sites.toOld source replay current valueBound refined originBound native
  refine ⟨next, nextReady, nextRefined, nextCurrent, nextBound, retained, ledger, ?_⟩
  have growth : upper.vals.size ≤ next.vals.size := by
    simpa only [coerceSlot, bind_run, read_apply, ready.roots.valueSize, nextReady.roots.valueSize] using
      (advB_coerceSlot slotId value origin le state _ _ rfl).vals
  have emitted : EmitsOnlyRun NotReplacement (coerceSlot slotId value origin) := by
    intro environment initial result final run
    exact (neutral_coerceSlot slotId value origin environment initial result final run).map
      (fun instruction _ neutral => by
        cases instruction with
        | eff effect => cases effect <;> simp_all [NeutralInstruction, WriterInstruction, NotReplacement]
        | _ => simp [NotReplacement])
  exact sites.of_action emitted (types_coerceSlot slotId value origin)
    (generatedTargetFrame_coerceSlot none slotId value origin) rfl growth retained

theorem occurrenceCoerceResult_canonicalSites {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {env : PEnv} {root siteRoot : DemandNode} {targets : List BlockId}
    {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {effect : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {state : LS} {upper : Prov} {block : BlockId} {value : ValueId}
    {path : List Nat} {node : DemandNode} {start finish : RState}
    {sourceRoots : List RootRef} {origin : OriginId}
    (ready : ReplayBuilder module results types func effect le scopeCount slots state upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot targets le state func types upper)
    (source : DemandNodeAt root path node)
    (replay : SourceNodeRoots env.access node start sourceRoots finish)
    (current : state.cur = some block) (valueBound : value < state.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : origin < le.mod.origins.size)
    (native : NativeRows types (coerceResult value origin le state).2) :
    ∃ next, ReplayBuilder module results types func effect le scopeCount slots (coerceResult value origin le state).2 next ∧
      GIR.RootsRefine func (rootsAt next.vals (coerceResult value origin le state).1) sourceRoots ∧
      (coerceResult value origin le state).2.cur = some block ∧
      (coerceResult value origin le state).1 < (coerceResult value origin le state).2.vals.size ∧
      (∀ oldValue, oldValue < upper.vals.size → rootsAt next.vals oldValue = rootsAt upper.vals oldValue) ∧
      OccurrenceLedger env root func types next state (coerceResult value origin le state).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot targets le
        (coerceResult value origin le state).2 func types next := by
  obtain ⟨next, nextReady, nextRefined, nextCurrent, nextBound, retained, ledger, _⟩ :=
    occurrenceCoerceResult origin ready sites.toOld source replay current valueBound refined originBound native
  refine ⟨next, nextReady, nextRefined, nextCurrent, nextBound, retained, ledger, ?_⟩
  have growth : upper.vals.size ≤ next.vals.size := by
    simpa only [coerceResult, bind_run, read_apply, ready.roots.valueSize, nextReady.roots.valueSize] using
      (advB_coerceResult value origin le state _ _ rfl).vals
  have emitted : EmitsOnlyRun NotReplacement (coerceResult value origin) := by
    intro environment initial result final run
    exact (neutral_coerceResult value origin environment initial result final run).map
      (fun instruction _ neutral => by
        cases instruction with
        | eff effect => cases effect <;> simp_all [NeutralInstruction, WriterInstruction, NotReplacement]
        | _ => simp [NotReplacement])
  exact sites.of_action emitted (types_coerceResult value origin)
    (generatedTargetFrame_coerceResult none value origin) rfl growth retained

end Goose.Lower.Validation.ReplacementContentFlowSource.ReplayBuilder

namespace Goose.Lower.Validation.ReplacementContentFlowSource.OccurrenceLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation
open Goose.Lower.Validation.SourceReplacementWriterLedger

theorem emitDef_canonicalSites {env : PEnv} {root siteRoot : DemandNode} {targets : List BlockId}
    {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {func : Func} {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {initial before after : LS} {upper next : Prov} {value : ValueId} {op : Op}
    (ledger : OccurrenceLedger env root func types upper initial before)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot targets le before func types upper)
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
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot targets le after func types next := by
  refine ⟨ledger.emitDef beforeReady afterReady run retained operands noLoad noCall consumed, ?_⟩
  exact sites.emitDef_replay beforeReady afterReady run retained

end Goose.Lower.Validation.ReplacementContentFlowSource.OccurrenceLedger

#print axioms Goose.Lower.Validation.SourceReplacementWriterLedger.CanonicalOccurrenceSitesBuilder.of_action
#print axioms Goose.Lower.Validation.SourceReplacementWriterLedger.CanonicalOccurrenceSitesBuilder.emitEffect
#print axioms Goose.Lower.Validation.SourceReplacementWriterLedger.CanonicalOccurrenceSitesBuilder.joinArms
#print axioms Goose.Lower.Validation.SourceReplacementWriterLedger.canonical_occurrenceSites_initSlots
#print axioms Goose.Lower.Validation.ReplacementContentFlowSource.ReplayBuilder.occurrenceCoerceSlot_canonicalSites
#print axioms Goose.Lower.Validation.ReplacementContentFlowSource.OccurrenceLedger.emitDef_canonicalSites
