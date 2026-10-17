import Goose.Lower.Validation.SummaryPreservationRefinedReads

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rootsOfDef_load_refSlice_parameter {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {provenance : Prov}
    {result address : ValueId} {index : Nat} {ty : Ty} {mu : Mutability} {element : Ty}
    (addressRoots : rootsAt provenance.vals address = [.param index])
    (parameter : func.params[index]? = some ty) (reference : ty.isRefSlice = true)
    (resultType : vt[result]? = some (some (.data (.slice mu element)))) :
    rootsOfDef res vt func provenance result (.load address) =
      unionRoots [] (((func.roots.contents.find? (·.1 == index)).map (·.2)).getD []) := by
  simp [rootsOfDef, valRefLike, resultType, VTy.refLike, Ty.isRefLike, addressRoots,
    parameter, reference]


theorem lowerContext_parameter_type {module : Core.Module} {ctx : Context} {impl : Impl}
    {index : Nat} {param : Param} {localVar : LocalVar}
    (parameter : impl.params[index]? = some param)
    (variableRow : impl.vars[param.var]? = some localVar) :
    (lowerContextAt module ctx impl).params[index]? = some localVar.ty := by
  simp [lowerContextAt, lowerImpl, List.getElem?_map, Array.getElem?_toList,
    parameter, tyOfVar, variableRow]


theorem readRoots_refSlice_parameter_load {env : PEnv} {index : Nat} {param : Param}
    {localVar : LocalVar} {sourceRoots : List RootRef} {start finish : RState}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {provenance : Prov}
    {result address : ValueId} {mu : Mutability} {element : Ty}
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (source : readRoots env (.deref (.read (.var param.var))) start = .ok (sourceRoots, finish))
    (addressRoots : rootsAt provenance.vals address = [.param index])
    (resultType : vt[result]? = some (some (.data (.slice mu element)))) :
    rootsOfDef res vt (lowerContextAt env.mod env.ctx env.impl) provenance result (.load address) =
      unionRoots [] sourceRoots := by
  have sliceVariable : env.isRefSliceVar param.var = true := by
    simp [PEnv.isRefSliceVar, variableRow, reference]
  cases contents : env.cont param.var with
  | none =>
    simp only [readRoots, sliceVariable, ite_true, contents] at source
    change Except.error _ = Except.ok _ at source
    cases source
  | some roots =>
    have pair := (st_pure_ok _ _ _).mp (show (pure roots : P (List RootRef)) start =
      .ok (sourceRoots, finish) by simpa only [readRoots, sliceVariable, ite_true, contents] using source)
    have rootsEq : sourceRoots = roots := congrArg Prod.fst pair
    rw [rootsOfDef_load_refSlice_parameter addressRoots
      (lowerContext_parameter_type parameter variableRow) reference resultType]
    change unionRoots [] ((((lowerContextRootInfo env.ctx env.impl).contents.find?
      (·.1 == index)).map (·.2)).getD []) = unionRoots [] sourceRoots
    have annotation : (env.ctx.contentRoots.find? (·.1 == param.var)).map (·.2) = some roots := contents
    rw [lowerContextRootInfo_contents_eq parameter annotation]
    simp [rootsEq]


theorem readRoots_refSlice_parameter_refines {env : PEnv} {index : Nat} {param : Param}
    {localVar : LocalVar} {sourceRoots : List RootRef} {start finish : RState}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {provenance : Prov}
    {result address : ValueId} {mu : Mutability} {element : Ty}
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (source : readRoots env (.deref (.read (.var param.var))) start = .ok (sourceRoots, finish))
    (addressRoots : rootsAt provenance.vals address = [.param index])
    (resultType : vt[result]? = some (some (.data (.slice mu element)))) :
    RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsOfDef res vt (lowerContextAt env.mod env.ctx env.impl) provenance result (.load address))
      sourceRoots := by
  rw [readRoots_refSlice_parameter_load parameter variableRow reference source addressRoots resultType]
  intro root member
  exact Or.inl ((mem_unionRoots_iff.mp member).elim (fun impossible => nomatch impossible) id)

end Goose.Lower.Validation.SummaryPreservation
