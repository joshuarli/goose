import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReadLocal
import Goose.Lower.Validation.ValueBounds

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem accessLoadLedger {env : PEnv} {root : DemandNode} {func : Func} {types : Array (Option VTy)}
    {upper : Prov} {le : LEnv} {initial final : LS} {result address : ValueId} {place : Place}
    {path : List Nat} {before addressed after : RState} {placeRoots valueRoots : List RootRef}
    (run : emitDef (.load address) le initial = (result, final))
    (node : DemandNodeAt root path (.expression (.read place)))
    (placeReplay : rpPlace env place before = .ok (placeRoots, addressed))
    (valueReplay : rpExpr env (.read place) before = .ok (valueRoots, after))
    (facts : initial.cur.isSome = true → address < upper.vals.size ∧ result < upper.vals.size ∧
      GIR.RootsRefine func (rootsAt upper.vals address) placeRoots ∧
      GIR.RootsRefine func (rootsAt upper.vals result) valueRoots)
    (physical : initial.cur.isSome = true → valRefLike types result = true →
      ReadAddressPhysical env place (rootsAt upper.vals address)) :
    OccurrenceLedger env root func types upper initial final := by
  apply accessEmitDefinition run
  intro live
  obtain ⟨addressBound, valueBound, addressRefined, valueRefined⟩ := facts live
  refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
  · intro value member reference
    simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
    subst value
    exact accessOperandPlace (node.snoc 0 rfl) placeReplay addressBound addressRefined
  · intro value pointer same reference
    cases same
    exact ⟨env, path, place, before, placeRoots, addressed, valueRoots, after,
      rfl, node, placeReplay, valueReplay, addressBound, valueBound, addressRefined, valueRefined, physical live reference⟩
  · intro value callee args origin same; cases same
  · intro value member mutability payload typed
    simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
    subst value
    exact .place _ env _ _ _ _ _ rfl (node.snoc 0 rfl) placeReplay addressBound addressRefined

theorem accessLocalReadLedgerRaw {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {le : LEnv} {initial : LS} {index : VarId}
    {path : List Nat} {before : RState} {sourceRoots : List RootRef}
    (node : DemandNodeAt root path (.expression (.read (.var index))))
    (source : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true →
      ∃ after, rpExpr env (.read (.var index)) before = .ok (sourceRoots, after))
    (returned : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true →
      (lowerExpr (.read (.var index)) le initial).1 < upper.vals.size ∧
      GIR.RootsRefine func (rootsAt upper.vals (lowerExpr (.read (.var index)) le initial).1) sourceRoots)
    (origins : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true →
      ∃ placeRoots placeAfter, rpPlace env (.var index) before = .ok (placeRoots, placeAfter) ∧
        (lowerPlace (.var index) le initial).1 < upper.vals.size ∧
        GIR.RootsRefine func (rootsAt upper.vals (lowerPlace (.var index) le initial).1) placeRoots)
    (physical : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true →
      rootsAt upper.vals (lowerPlace (.var index) le initial).1 = [.local index]) :
    OccurrenceLedger env root func types upper initial (lowerExpr (.read (.var index)) le initial).2 := by
  let addressed := lowerPlace (.var index) le initial
  have first : OccurrenceLedger env root func types upper initial addressed.2 :=
    emitsOnly_emitDef (rfl : emitDef (.slotAddr index) le initial = addressed)
      (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
  let loaded := emitDef (.load addressed.1) le addressed.2
  have run : emitDef (.load addressed.1) le addressed.2 =
      ((lowerExpr (.read (.var index)) le initial).1, loaded.2) := by
    rw [ReplayBuilder.readValue_eq]
  refine first.trans ((accessEmitDefinition run ?_).trans
    (.of_blocks (ReplayBuilder.readBlocks_eq (.var index) le initial)))
  intro active
  have live : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true :=
    by
      rw [ReplayBuilder.readCurrent_eq]
      exact (congrArg Option.isSome (accessEmitCurrent run)).trans active
  obtain ⟨placeRoots, placeAfter, placeReplay, addressBound, addressRefined⟩ := origins live
  obtain ⟨valueBound, valueRefined⟩ := returned live
  obtain ⟨after, replay⟩ := source live
  refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
  · intro value member reference
    simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
    subst value
    exact accessOperandPlace (node.snoc 0 rfl) placeReplay addressBound addressRefined
  · intro value address same reference
    cases same
    exact ⟨env, path, .var index, before, placeRoots, placeAfter, sourceRoots, after,
      rfl, node, placeReplay, replay, addressBound, valueBound, addressRefined, valueRefined, .local index rfl (physical live)⟩
  · intro value callee args origin same; cases same
  · intro value member mutability payload typed
    simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
    subst value
    exact .place _ env _ _ _ _ _ rfl (node.snoc 0 rfl) placeReplay addressBound addressRefined

theorem accessNestedReadSites {module : GIR.Module} {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial : LS} {old next : Prov}
    {env : PEnv} {siteRoot : DemandNode} {siteTargets : List BlockId} {index : VarId}
    (ready : ReplayBuilder module results types func target le scopeCount slots initial old)
    (completed : ReplayBuilder module results types func target le scopeCount slots
      (lowerExpr (.read (.deref (.read (.var index)))) le initial).2 next)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets le initial func types old)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    OccurrenceSitesBuilder env siteRoot siteTargets le
      (lowerExpr (.read (.deref (.read (.var index)))) le initial).2 func types next := by
  let addressed := lowerPlace (.var index) le initial
  let loaded := lowerExpr (.read (.var index)) le initial
  have emitted : EmitsOnly NotReplacement initial (lowerExpr (.read (.deref (.read (.var index)))) le initial).2 :=
    (((emitsOnly_emitDef (rfl : emitDef (.slotAddr index) le initial = addressed) trivial).trans
      (emitsOnly_emitDef (rfl : emitDef (.load addressed.1) le addressed.2 = _) trivial)).trans
      (.of_blocks (ReplayBuilder.readBlocks_eq (.var index) le initial))).trans
      (emitsOnly_emitDef (rfl : emitDef (.load loaded.1) le loaded.2 =
        lowerExpr (.read (.deref (.read (.var index)))) le initial) trivial)
  exact sites.of_emits emitted (types_lowerExpr (.read (.deref (.read (.var index)))) le initial _ _ rfl)
    (.of_run (generatedTargetFrame_lowerExpr none (.read (.deref (.read (.var index))))) rfl)
    (accessRootsGrowth ready completed (advB_lowerExpr (.read (.deref (.read (.var index)))) le initial _ _ rfl).vals) retained

#print axioms accessLoadLedger
#print axioms accessLocalReadLedgerRaw
#print axioms accessNestedReadSites

end Goose.Lower.Validation.ReplacementContentFlowSource
