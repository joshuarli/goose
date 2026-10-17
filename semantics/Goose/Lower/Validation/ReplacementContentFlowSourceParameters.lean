import Goose.GIR.ReplacementContentFlowProofsSupport
import Goose.Lower.Validation.ReplacementContentFlowSourceTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem readRoots_initial_parameter_value {env : PEnv} {context : ContextId}
    {index : Nat} {param : Param} {localVar : LocalVar} {entry : GIR.Block} {value : ValueId}
    {sourceRoots : List RootRef} {before after : RState}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (entryRow : (lowerContextAt env.mod env.ctx env.impl).blocks[0]? = some entry)
    (entryParameter : entry.params[index]? = some (value, .data localVar.ty))
    (source : readRoots env (.var param.var) before = .ok (sourceRoots, after)) :
    let func := lowerContextAt env.mod env.ctx env.impl
    ∃ actual, normalize func (flowAt (start func (func.valueTypes (lower env.mod))).values value) =
        some actual ∧ ∀ root ∈ actual, root ∈ sourceRoots := by
  dsimp only
  have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? entryRow)
  have parameterMember := List.mem_of_getElem? entryParameter
  have dense : (((lowerContextAt env.mod env.ctx env.impl).blocks.toList.flatMap GIR.Block.defs).Perm
      (List.range (lowerContextAt env.mod env.ctx env.impl).numValues)) :=
    lowerImpl_dense_definitions env.mod env.impl
  have initial := start_parameter ((lowerContextAt env.mod env.ctx env.impl).valueTypes (lower env.mod))
    entryRow (Func.parameter_ids_distinct_of_dense dense member) index value (.data localVar.ty)
    entryParameter (Func.parameter_ids_bounded_of_dense dense entry member _ parameterMember)
  have recorded := accepted_context_parameter_type accepted contextRow implementationRow member parameterMember
  have refValue : valRefLike ((lowerContextAt env.mod env.ctx env.impl).valueTypes (lower env.mod)) value = true := by
    simp only [valRefLike, recorded, VTy.refLike, reference]
  rw [initial]
  simp only [refValue, ite_true]
  cases annotation : env.ann param.var with
  | none =>
    simp only [readRoots, variableRow, reference, ite_true, annotation] at source
    change Except.error _ = Except.ok _ at source
    cases source
  | some roots =>
    have pureSource : (pure roots : P (List RootRef)) before = .ok (sourceRoots, after) := by
      simpa only [readRoots, variableRow, reference, ite_true, annotation] using source
    have same : sourceRoots = roots := congrArg Prod.fst ((st_pure_ok _ _ _).mp pureSource)
    subst sourceRoots
    exact lowerContextAt_parameter_normalized parameter annotation

#print axioms readRoots_initial_parameter_value

end Goose.Lower.Validation.ReplacementContentFlowSource
