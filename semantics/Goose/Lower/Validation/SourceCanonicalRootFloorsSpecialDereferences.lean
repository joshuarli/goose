import Goose.Lower.Validation.SourceCanonicalRootFloorsReads

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem special_dereference_canonical_floor {env : PEnv} {typing : TEnv} {func : Func}
    {root : DemandNode} (tables : SourceCanonicalTables env func)
    (sourceTables : SourceRootTables typing env) {expression : Expr} {specialType : Ty}
    (special : sliceRefTy typing expression = some specialType)
    {info : PlaceInfo} {start finish : Nat}
    (source : tyPlace typing (.deref expression) start = .ok (info, finish))
    {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef}
    (replayed : rpPlace env (.deref expression) rootsBefore = .ok (sourceRoots, rootsAfter))
    {returnTypes : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace (.deref expression) (lowerEnv typing.mod typing.vars returnTypes) before = (value, after))
    (generated : GeneratedBuilderState before) (live : after.cur.isSome = true)
    (projects : RecipeMetadataProjects env root func after) :
    sourceRoots ⊆ rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals value := by
  have original := special
  cases expression <;> try simp [sliceRefTy] at special
  case read place =>
    cases place <;> try simp [sliceRefTy] at special
    case var slot =>
      obtain ⟨localVar, variableAt, variableType, _⟩ := sliceRefTy_variable_row original
      have reference : localVar.ty.isRefSlice = true := by
        rw [variableType]
        exact sliceRefTy_isRefSlice original
      have recordedReference : ((lowerEnv typing.mod typing.vars returnTypes).vars[slot]?).any
          (·.ty.isRefSlice) = true := by simp [lowerEnv, variableAt, reference]
      obtain ⟨mode, typed⟩ := lowerPlace_generated_typed _ source run live generated
      have recorded := lowerExpr_readVar_recipe (show lowerExpr (.read (.var slot))
        (lowerEnv typing.mod typing.vars returnTypes) before = (value, after) from run)
        live recordedReference typed (show (Ty.ref mode info.ty).isRefLike = true from rfl)
      obtain ⟨roots, row⟩ := projects.covered (value, .refSliceVar slot) recorded
      have floor := projects.refSliceVar_canonical_floor recorded (tables.valueRows value roots row)
        (resultRoots (lower env.mod) (lower env.mod).implTypes)
        (func.valueTypes (lower env.mod)) (lower env.mod).rootCount
      have projected : sourceReadRoots env (.var slot) = sourceRoots := by
        simp only [rpPlace, rpExpr] at replayed
        obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
        obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
        exact sourceReadRoots_agrees env (.var slot) _ _ sourceRoots replayed
      rw [← projected]
      have replayVariable : env.impl.vars[slot]? = some localVar := by
        rw [sourceTables.variablesEq]
        exact variableAt
      have localReference : localVar.ty.isRefLike = true := by
        have implication : ∀ type : Ty, type.isRefSlice = true → type.isRefLike = true := by
          intro type
          cases type <;> simp [Ty.isRefSlice, Ty.isRefLike]
        exact implication localVar.ty reference

      simpa only [sourceReadRoots, replayVariable, Option.any_some, localReference, ite_true] using floor

end Goose.Lower.Validation.SourceCanonicalRootFloors
