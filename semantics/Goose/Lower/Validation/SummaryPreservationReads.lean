import Goose.Lower.Validation.SummaryPreservationProvenance

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rootsOfDef_load_slot {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {result address : ValueId} {slot : SlotId}
    (addressRoots : rootsAt provenance.vals address = [.local slot]) :
    rootsOfDef res vt func provenance result (.load address) =
      if valRefLike vt result then rootsAt provenance.slots slot else [] := by
  simp only [rootsOfDef, addressRoots]
  split
  · rename_i refLike
    cases typeRow : vt[result]? with
    | none => simp [typeRow, unionRoots]
    | some maybeType =>
      cases maybeType with
      | none => simp [typeRow, unionRoots]
      | some valueType =>
        cases valueType with
        | view mu ty => simp [typeRow, unionRoots]
        | data ty => cases ty <;> simp [typeRow, unionRoots]
  · rfl

theorem readRoots_variable_load {env : PEnv} {varId : VarId} {localVar : LocalVar}
    {sourceRoots : List RootRef} {start finish : RState}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func}
    {provenance : Prov} {result address : ValueId}
    (varIdRow : env.impl.vars[varId]? = some localVar)
    (source : readRoots env (.var varId) start = .ok (sourceRoots, finish))
    (resultType : vt[result]? = some (some (.data localVar.ty)))
    (addressRoots : rootsAt provenance.vals address = [.local varId])
    (slotRoots : rootsAt provenance.slots varId = (env.ann varId).getD []) :
    rootsOfDef res vt func provenance result (.load address) = sourceRoots := by
  rw [rootsOfDef_load_slot addressRoots]
  have reference : valRefLike vt result = localVar.ty.isRefLike := by
    simp [valRefLike, resultType, VTy.refLike]
  rw [reference]
  by_cases refLike : localVar.ty.isRefLike = true
  · cases annotation : env.ann varId with
    | none =>
      simp only [readRoots, varIdRow, refLike, ite_true, annotation] at source
      change Except.error _ = Except.ok _ at source
      cases source
    | some roots =>
      simp only [readRoots, varIdRow, refLike, ite_true, annotation] at source
      have pair := (st_pure_ok _ _ _).mp source
      have same : sourceRoots = roots := congrArg Prod.fst pair
      rw [if_pos refLike, slotRoots, annotation, Option.getD_some, same]
  · simp only [readRoots, varIdRow, refLike, ite_false] at source
    have pair := (st_pure_ok _ _ _).mp source
    have same : sourceRoots = [] := congrArg Prod.fst pair
    simp [refLike, same]

end Goose.Lower.Validation.SummaryPreservation
