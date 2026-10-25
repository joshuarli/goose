import Goose.Lower.Validation.ReplacementContentFlowSourceRoots
import Goose.Lower.Validation.SummaryPreservationContentReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open SummaryPreservation

theorem start_contents (func : Func) (types : Array (Option VTy)) :
    (start func types).contents = func.params.toArray.mapIdx (fun index type =>
      if type.isRefSlice then .known [.contents index] else .known []) := by
  cases entry : func.blocks[0]? <;> simp [start, entry]

theorem start_parameter_content {func : Func} {types : Array (Option VTy)}
    {index : Nat} {type : Ty} (parameter : func.params[index]? = some type)
    (reference : type.isRefSlice = true) :
    content func (start func types) (.known [.param index]) = .known [.contents index] := by
  simp [content, Roots.bind, Roots.join, parameter, reference, flowAt, start_contents,
    Array.getElem?_mapIdx, List.getElem?_toArray]

theorem readRoots_initial_parameter_content {env : PEnv} {index : Nat} {param : Param}
    {localVar : LocalVar} {sourceRoots : List RootRef} {before after : RState}
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (source : readRoots env (.deref (.read (.var param.var))) before = .ok (sourceRoots, after)) :
    let func := lowerContextAt env.mod env.ctx env.impl
    ∃ actual, normalize func
        (content func (start func (func.valueTypes (lower env.mod))) (.known [.param index])) = some actual ∧
      ∀ root ∈ actual, root ∈ sourceRoots.flatMap func.expandParameterRoot := by
  dsimp only
  rw [start_parameter_content (lowerContext_parameter_type parameter variableRow) reference]
  have sliceVariable : env.isRefSliceVar param.var = true := by
    simp [PEnv.isRefSliceVar, variableRow, reference]
  cases contents : env.cont param.var with
  | none =>
    simp only [readRoots, sliceVariable, ite_true, contents] at source
    change Except.error _ = Except.ok _ at source
    cases source
  | some roots =>
    have pureSource : (pure roots : P (List RootRef)) before = .ok (sourceRoots, after) := by
      simpa only [readRoots, sliceVariable, ite_true, contents] using source
    have rootsEq : sourceRoots = roots := congrArg Prod.fst ((st_pure_ok _ _ _).mp pureSource)
    subst sourceRoots
    exact lowerContextAt_contents_normalized parameter contents

#print axioms readRoots_initial_parameter_content
#print axioms start_contents
#print axioms start_parameter_content

end Goose.Lower.Validation.ReplacementContentFlowSource
