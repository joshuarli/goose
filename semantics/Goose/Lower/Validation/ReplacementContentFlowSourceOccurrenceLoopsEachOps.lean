import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsRangeSteps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessKernel
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlConsumedReferences

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

structure ViewOccurrenceSource (env : PEnv) (root : DemandNode) (roots : List RootRef) where
  path : List Nat
  view : View
  before : RState
  after : RState
  source : DemandNodeAt root path (.view view)
  replay : rpView env view before = .ok (roots, after)

theorem ViewOccurrenceSource.operand {env : PEnv} {root : DemandNode} {roots : List RootRef}
    {func : Func} {upper : Prov} {value : ValueId}
    (source : ViewOccurrenceSource env root roots) (bound : value < upper.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
    OperandOccurrence env root func upper value :=
  accessOperandView source.source source.replay bound refined

theorem ViewOccurrenceSource.consumedPlace {env : PEnv} {root : DemandNode} {roots : List RootRef}
    {func : Func} {types : Array (Option VTy)} {upper : Prov} {value : ValueId} {place : Place}
    (source : ViewOccurrenceSource env root roots) (shape : source.view = .of place)
    (bound : value < upper.vals.size) (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
    ConsumedReferenceOccurrence env root func types upper value := by
  have replay := source.replay
  rw [shape] at replay
  simp only [rpView] at replay
  obtain ⟨placeRoots, placeAfter, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨_, readAfter, reads, returned⟩ := (st_bind_ok _ _ _ _).mp tail
  have rootsEq := congrArg Prod.fst ((st_pure_ok _ _ _).mp returned)
  dsimp only at rootsEq
  subst placeRoots
  have location : DemandNodeAt root source.path (.view (.of place)) := by
    simpa only [shape] using source.source
  exact .place value env (source.path ++ [0]) place source.before roots placeAfter rfl
    (sourcePath_append location (accessChildNode 0 rfl)) placeReplay bound refined

theorem native_scalar_definition {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {types : Array (Option VTy)}
    (native : NativeRows types after) (run : emitDef op le before = (value, after))
    (live : before.cur.isSome = true)
    (scalar : ∀ result, op.resultTy (tyEnv le before) = .ok result → result.refLike = false) :
    valRefLike types value = false := by
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    let result := (op.resultTy (tyEnv le before)).toOption.getD (.data .unit)
    have row : types[before.vals.size]? = some (some result) := native _ _ (by simp [result])
    have resultScalar : result.refLike = false := by
      cases checked : op.resultTy (tyEnv le before) with
      | error message => simp [result, checked, Except.toOption, VTy.refLike, Ty.isRefLike]
      | ok type => simpa [result, checked, Except.toOption] using scalar type checked
    simpa only [valRefLike, row] using resultScalar

theorem native_viewLen_scalar {le : LEnv} {before after : LS} {value view : ValueId}
    {types : Array (Option VTy)} (native : NativeRows types after)
    (run : emitDef (.viewLen view) le before = (value, after)) (live : before.cur.isSome = true) :
    valRefLike types value = false := by
  apply native_scalar_definition native run live
  intro result checked
  cases source : (tyEnv le before).viewTy view with
  | error message => simp [Op.resultTy, source, bind, Except.bind] at checked
  | ok info =>
    have same : .data (.int .i64) = result := by
      simpa [Op.resultTy, source, bind, Except.bind, pure, Except.pure] using checked
    subst result
    rfl

theorem native_arrayLen_scalar {le : LEnv} {before after : LS} {value owner : ValueId}
    {types : Array (Option VTy)} (native : NativeRows types after)
    (run : emitDef (.arrayLen owner) le before = (value, after)) (live : before.cur.isSome = true) :
    valRefLike types value = false := by
  apply native_scalar_definition native run live
  intro result checked
  cases source : (tyEnv le before).refTy owner with
  | error message => simp [Op.resultTy, source, bind, Except.bind] at checked
  | ok info =>
    simp only [Op.resultTy, source, bind, Except.bind, pure, Except.pure] at checked
    split at checked
    · cases checked
      rfl
    · cases checked

theorem occurrenceLedger_borrowTo {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {le : LEnv} {before after : LS}
    {value result : ValueId} {mutability : Mutability}
    (run : borrowTo mutability value le before = (result, after)) :
    OccurrenceLedger env root func types upper before after := by
  rcases borrowTo_ref_cases run with same | frozen | borrowed
  · exact .of_blocks (congrArg LS.blocks same.2)
  · apply accessEmitDefinition frozen
    intro live
    exact accessDefinitionNoOperands rfl (by intros; intro same; cases same) (by intros; intro same; cases same)
  · apply accessEmitDefinition borrowed
    intro live
    exact accessDefinitionNoOperands rfl (by intros; intro same; cases same) (by intros; intro same; cases same)

theorem occurrenceSites_borrowTo {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}
    {value result : ValueId} {mutability : Mutability}
    (sites : OccurrenceSitesBuilder env root targets le before func types old)
    (run : borrowTo mutability value le before = (result, after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    OccurrenceSitesBuilder env root targets le after func types next := by
  rcases borrowTo_ref_cases run with same | frozen | borrowed
  · rw [same.2]
    exact sites.ghost_retained growth retained
  · exact sites.emitDef frozen growth retained
  · exact sites.emitDef borrowed growth retained

#print axioms native_scalar_definition
#print axioms occurrenceLedger_borrowTo

end Goose.Lower.Validation.ReplacementContentFlowSource
