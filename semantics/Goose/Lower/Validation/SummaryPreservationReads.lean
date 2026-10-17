import Goose.Lower.Validation.SummaryPreservationProvenance
import Goose.Lower.Validation.SummaryPreservationRootBounds

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

theorem readRoots_variable_eq {env : PEnv} {varId : VarId} {localVar : LocalVar}
    {sourceRoots : List RootRef} {start finish : RState}
    (varIdRow : env.impl.vars[varId]? = some localVar)
    (source : readRoots env (.var varId) start = .ok (sourceRoots, finish)) :
    sourceRoots = if localVar.ty.isRefLike then (env.ann varId).getD [] else [] := by
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
      simp [refLike, annotation, same]
  · simp only [readRoots, varIdRow, refLike, ite_false] at source
    have pair := (st_pure_ok _ _ _).mp source
    have same : sourceRoots = [] := congrArg Prod.fst pair
    simp [refLike, same]

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
  rw [reference, slotRoots]
  exact (readRoots_variable_eq varIdRow source).symm

theorem readRoots_variable_load_represent {env : PEnv} {varId : VarId} {localVar : LocalVar}
    {sourceRoots : List RootRef} {start finish : RState}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func}
    {provenance : Prov} {result address : ValueId}
    (varIdRow : env.impl.vars[varId]? = some localVar)
    (source : readRoots env (.var varId) start = .ok (sourceRoots, finish))
    (resultType : vt[result]? = some (some (.data localVar.ty)))
    (addressRoots : rootsAt provenance.vals address = [.local varId])
    (slotRoots : RootsRepresent func (rootsAt provenance.slots varId) (env.ann varId |>.getD [])) :
    RootsRepresent func (rootsOfDef res vt func provenance result (.load address)) sourceRoots := by
  rw [rootsOfDef_load_slot addressRoots]
  have reference : valRefLike vt result = localVar.ty.isRefLike := by
    simp [valRefLike, resultType, VTy.refLike]
  rw [reference, readRoots_variable_eq varIdRow source]
  by_cases refLike : localVar.ty.isRefLike = true
  · simpa only [refLike, ite_true] using slotRoots
  · simpa [refLike] using rootsRepresent_empty func []


theorem readRoots_variable_annotation {env : PEnv} {varId : VarId} {localVar : LocalVar}
    {sourceRoots : List RootRef} {start finish : RState}
    (checked : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (variableRow : env.impl.vars[varId]? = some localVar)
    (source : readRoots env (.var varId) start = .ok (sourceRoots, finish)) :
    sourceRoots = (env.ann varId).getD [] := by
  rw [readRoots_variable_eq variableRow source]
  by_cases reference : localVar.ty.isRefLike = true
  · simp [reference]
  · have missing : env.ann varId = none := by
      unfold PEnv.ann
      cases annotation : env.ctx.varRoots.find? (·.1 == varId) with
      | none => rfl
      | some entry =>
        have entryVar : entry.1 = varId := eq_of_beq
          (List.find?_some (p := fun entry : VarId × List RootRef => entry.1 == varId)
            (a := entry) annotation)
        obtain ⟨declaredVar, declaredLookup, refLike, _⟩ :=
          Core.Declarative.annotationRows_sound env.mod env.impl env.ctx checked entry.1 entry.2
            (List.mem_of_find?_eq_some annotation)
        rw [entryVar, variableRow] at declaredLookup
        cases declaredLookup
        exact False.elim (reference refLike)
    simp [reference, missing]

theorem readRoots_variable_load_represent_of_annotations {env : PEnv}
    {varId : VarId} {localVar : LocalVar} {sourceRoots : List RootRef} {start finish : RState}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func}
    {provenance : Prov} {result address : ValueId}
    (checked : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (variableRow : env.impl.vars[varId]? = some localVar)
    (source : readRoots env (.var varId) start = .ok (sourceRoots, finish))
    (addressRoots : rootsAt provenance.vals address = [.local varId])
    (slotRoots : RootsRepresent func (rootsAt provenance.slots varId) (env.ann varId |>.getD [])) :
    RootsRepresent func (rootsOfDef res vt func provenance result (.load address)) sourceRoots := by
  rw [rootsOfDef_load_slot addressRoots]
  split
  · rw [readRoots_variable_annotation checked variableRow source]
    exact slotRoots
  · exact rootsRepresent_empty func sourceRoots


theorem readRoots_variable_state {env : PEnv} {varId : VarId} {localVar : LocalVar}
    {roots : List RootRef} {start finish : RState}
    (variableRow : env.impl.vars[varId]? = some localVar)
    (source : readRoots env (.var varId) start = .ok (roots, finish)) : finish = start := by
  by_cases reference : localVar.ty.isRefLike = true
  · cases annotation : env.ann varId with
    | none =>
      simp only [readRoots, variableRow, reference, ite_true, annotation] at source
      cases source
    | some roots =>
      simp only [readRoots, variableRow, reference, ite_true, annotation] at source
      exact congrArg Prod.snd ((st_pure_ok _ _ _).mp source)
  · simp only [readRoots, variableRow, reference, ite_false] at source
    exact congrArg Prod.snd ((st_pure_ok _ _ _).mp source)

theorem rpExpr_read_variable {env : PEnv} {varId : VarId} {start : RState} :
    rpExpr env (.read (.var varId)) start = readRoots env (.var varId) start := rfl

end Goose.Lower.Validation.SummaryPreservation
