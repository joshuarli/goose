import Goose.Lower.Validation.PermissionSourceInductionContracts
import Goose.Lower.Validation.PermissionPreservationEachStatementSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permission_source_forEach {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (slot : VarId) (index : Option VarId) (view : View) (byRef : Bool)
    (body : Core.Block) (origin : OriginId)
    (viewChild : PermissionStorageViewChild env func results view)
    (bodyChild : ∀ env, PermissionSourceBlock env func results body) :
    PermissionSourceStatement env func results scope (.forEach slot index view byRef body origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  refine permissionInstructions_forEach_source source tables generated floor viewChild ?_ run
  intro type childStart childFinish typed input output value pre loop generated frames floor transfer lowered
  exact bodyChild {env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible}
    (tables.retained rfl rfl) typed (loop := loop) (pre := pre) (want := false)
    generated frames floor transfer lowered

#print axioms permission_source_forEach

end Goose.Lower.Validation
