import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessKernel
import Goose.Lower.Validation.SummaryPreservationReplayReferences

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem accessBorrowEmits {property : Inst → Prop} {le : LEnv} {before after : LS}
    {mutability : Mutability} {address result : ValueId}
    (run : borrowTo mutability address le before = (result, after))
    (freeze : ∀ value, property (.def value (.refFreeze address)))
    (borrow : ∀ value, property (.def value (.ownerBorrow address))) : EmitsOnly property before after := by
  rcases borrowTo_cases run with frozen | borrowed
  · rcases freezeTo_cases frozen with same | emitted
    · exact same.2.symm ▸ .refl _ _
    · exact emitsOnly_emitDef emitted (freeze _)
  · exact emitsOnly_emitDef borrowed (borrow _)

theorem borrowReferenceOccurrence {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial : LS} {upper : Prov}
    {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}
    (mutability : Mutability) (targetType : Ty) (address : ValueId) (sourceRoots : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots initial upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets le initial func vt upper)
    (input : initial.cur.isSome = true → address < initial.vals.size ∧
      GIR.RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (borrowTo mutability address le initial).2 next ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        ReplayValue func next (borrowTo mutability address le initial).2
          (borrowTo mutability address le initial).1 sourceRoots (.data (.ref mutability targetType))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func vt next initial (borrowTo mutability address le initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets le
        (borrowTo mutability address le initial).2 func vt next := by
  obtain ⟨next, completed, returned, retained⟩ :=
    ready.borrowReference mutability targetType address sourceRoots input
  have growth := accessRootsGrowth ready completed
    (advB_borrowTo mutability address le initial _ _ rfl).vals
  have emitted : OccurrenceLedger env root func vt next initial (borrowTo mutability address le initial).2 :=
    accessBorrowEmits rfl
      (fun _ => by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
      (fun _ => by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
  have withoutReplacement : EmitsOnly NotReplacement initial (borrowTo mutability address le initial).2 :=
    accessBorrowEmits rfl (fun _ => trivial) (fun _ => trivial)
  exact ⟨next, completed, returned, retained, emitted,
    sites.of_emits withoutReplacement (types_borrowTo mutability address le initial _ _ rfl)
      (.of_run (generatedTargetFrame_borrowTo none mutability address) rfl) growth retained⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
