import Goose.Lower.Validation.SourceCanonicalRootFloorsReadNative
import Goose.Lower.Validation.SourceCanonicalRootFloorsReadRecipes
import Goose.Lower.Validation.SourceRootShape

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem read_canonical_floor {env : PEnv} {typing : TEnv} {func : Func} {root : DemandNode}
    (tables : SourceCanonicalTables env func) (sourceTables : SourceRootTables typing env)
    {place : Place} {type : Ty} {start finish : Nat}
    (source : tyExpr typing (.read place) start = .ok (type, finish))
    {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef}
    (replayed : rpExpr env (.read place) rootsBefore = .ok (sourceRoots, rootsAfter))
    {returnTypes : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr (.read place) (lowerEnv typing.mod typing.vars returnTypes) before = (value, after))
    (generated : GeneratedBuilderState before) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) (projects : RecipeMetadataProjects env root func after) :
    sourceRoots ⊆ rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals value := by
  by_cases resultReference : type.isRefLike = true
  · have projected : sourceReadRoots env place = sourceRoots := by
      have reading := replayed
      simp only [rpExpr] at reading
      obtain ⟨_, _, _, reading⟩ := (st_bind_ok _ _ _ _).mp reading
      obtain ⟨_, _, _, reading⟩ := (st_bind_ok _ _ _ _).mp reading
      exact sourceReadRoots_agrees env place _ _ sourceRoots reading
    rw [← projected]
    clear projected replayed
    cases place with
    | var slot =>
        cases variableAt : env.impl.vars[slot]? with
        | none => simp [sourceReadRoots, variableAt]
        | some localVar =>
            cases variableReference : localVar.ty.isRefLike with
            | false => simp [sourceReadRoots, variableAt, variableReference]
            | true =>
                by_cases sliceReference : localVar.ty.isRefSlice = true
                · have reference : (typing.vars[slot]?).any (·.ty.isRefSlice) = true := by
                    rw [← sourceTables.variablesEq]
                    simp [variableAt, sliceReference]
                  have recorded := lowerExpr_readVar_typed_recipe source run live generated reference resultReference
                  obtain ⟨roots, row⟩ := projects.covered (value, .refSliceVar slot) recorded
                  have floor := projects.refSliceVar_canonical_floor recorded (tables.valueRows value roots row)
                    (resultRoots (lower env.mod) (lower env.mod).implTypes)
                    (func.valueTypes (lower env.mod)) (lower env.mod).rootCount
                  simpa only [sourceReadRoots, variableAt, Option.any_some, variableReference, ite_true] using floor
                · have ordinary : localVar.ty.isRefSlice = false := by
                    cases shape : localVar.ty.isRefSlice <;> simp_all
                  simpa only [sourceReadRoots, variableAt, Option.any_some, variableReference, ite_true] using
                    tables.readVar_annotation_floor variableAt variableReference ordinary generated run live continuation
    | deref expression =>
        cases expression <;> try exact List.nil_subset _
        case read owner =>
          cases owner <;> try exact List.nil_subset _
          case var slot =>
            cases variableAt : env.impl.vars[slot]? with
            | none => simp [sourceReadRoots, PEnv.isRefSliceVar, variableAt]
            | some localVar =>
                cases reference : localVar.ty.isRefSlice with
                | false => simp [sourceReadRoots, PEnv.isRefSliceVar, variableAt, reference]
                | true =>
                    cases contents : env.cont slot with
                    | none => simp [sourceReadRoots, PEnv.isRefSliceVar, variableAt, reference, contents]
                    | some roots =>
                        simpa only [sourceReadRoots, PEnv.isRefSliceVar, variableAt, reference, ite_true,
                          contents, Option.getD_some] using
                          tables.read_parameter_contents_floor variableAt reference contents generated run live continuation
    | _ => exact List.nil_subset _
  · have nonref : type.isRefLike = false := by
      cases reference : type.isRefLike <;> simp_all
    rw [source_expression_nonref_roots_empty (.read place) sourceTables source nonref replayed]
    exact List.nil_subset _

end Goose.Lower.Validation.SourceCanonicalRootFloors
