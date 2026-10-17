import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts
import Goose.Lower.Validation.SourceValueTypeShapesTables

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

 theorem lower_canonical_globalStorage_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (func : Func)
    (index : Nat) (type : Ty) (kind : VarKind)
    (row : ((lower module).tyEnv func).globals[index]? = some (type, kind)) :
    type.isRefLike = false := by
  change ((module.globals.map (lowerGlobal module)).map fun global => (global.ty, global.kind))[index]? = some (type, kind) at row
  rw [Array.getElem?_map, Array.getElem?_map] at row
  cases source : module.globals[index]? with
  | none => simp [source] at row
  | some global =>
    simp only [source, Option.map_some, Option.some.injEq, Prod.mk.injEq] at row
    rw [← row.1]
    exact ((validate_modOk module accepted).glob index global source).ty.2

theorem lower_canonical_flatFields_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (func : Func)
    (index : Nat) (descriptor : StructDef)
    (row : ((lower module).tyEnv func).structs[index]? = some descriptor)
    (fieldIndex : Nat) (field : StructField) (fieldAt : descriptor.fields[fieldIndex]? = some field) :
    field.ty.flat = true := by
  apply shape_checkStructTables_fields (validate_modOk module accepted).structTables descriptor _ field _
  · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)
  · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? fieldAt)

#print axioms lower_canonical_globalStorage_of_accepted
#print axioms lower_canonical_flatFields_of_accepted

end Goose.Lower.Validation
