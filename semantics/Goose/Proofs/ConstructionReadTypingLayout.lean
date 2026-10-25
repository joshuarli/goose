import Goose.Construct.Layout

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

mutual
def LayoutConforms (layout : LayoutEnv) : Ty → Prop
  | .int _ | .bool | .unit => True
  | .arr element _ | .varr element | .grow element | .growshrink element | .limited element _ |
      .slice _ element | .ref _ element => LayoutConforms layout element
  | .structT id fields => layout.structType? id = some (.structT id fields) ∧ LayoutFieldsConforms layout fields
  | .tuple fields => LayoutFieldsConforms layout fields

def LayoutFieldsConforms (layout : LayoutEnv) : TyList → Prop
  | .nil => True
  | .cons ty rest => LayoutConforms layout ty ∧ LayoutFieldsConforms layout rest
end

theorem layoutFieldsConforms_iff (layout : LayoutEnv) (fields : TyList) :
    LayoutFieldsConforms layout fields ↔ ∀ ty ∈ fields.toList, LayoutConforms layout ty := by
  cases fields with
  | nil => simp [LayoutFieldsConforms, TyList.toList]
  | cons ty rest => simp [LayoutFieldsConforms, TyList.toList, layoutFieldsConforms_iff layout rest]
termination_by sizeOf fields

theorem LayoutFieldsConforms.selected (layout : LayoutEnv) (fields : TyList)
    (conforms : LayoutFieldsConforms layout fields) (index : Nat) (ty : Ty)
    (selected : fields.toList[index]? = some ty) : LayoutConforms layout ty :=
  (layoutFieldsConforms_iff layout fields).mp conforms ty (List.mem_of_getElem? selected)

theorem LayoutConforms.nominal (layout : LayoutEnv) (id : Nat) (fields : TyList)
    (conforms : LayoutConforms layout (.structT id fields)) :
    layout.structType? id = some (.structT id fields) ∧ LayoutFieldsConforms layout fields := conforms

theorem tyList_toList_ofList (types : List Ty) : (TyList.ofList types).toList = types := by
  induction types with
  | nil => rfl
  | cons ty rest ih => simp only [TyList.ofList, TyList.toList, ih]

theorem LayoutConforms.descriptor (layout : LayoutEnv) (id : Nat) (fields : TyList)
    (conforms : LayoutConforms layout (.structT id fields)) :
    ∃ descriptor, layout.structs[id]? = some descriptor ∧
      fields.toList = descriptor.fields.toList.map (·.ty) ∧
      ∀ field ∈ descriptor.fields.toList, LayoutConforms layout field.ty := by
  obtain ⟨nominal, fieldTypes⟩ := conforms
  cases found : layout.structs[id]? with
  | none => simp only [LayoutEnv.structType?, found, Option.map_none, reduceCtorEq] at nominal
  | some descriptor =>
      have same : TyList.ofList (descriptor.fields.toList.map (·.ty)) = fields := by
        simpa only [LayoutEnv.structType?, found, Option.map_some, Option.some.injEq, Ty.structT.injEq,
          true_and] using nominal
      have types : fields.toList = descriptor.fields.toList.map (·.ty) := by
        rw [← same, tyList_toList_ofList]
      refine ⟨descriptor, rfl, types, ?_⟩
      intro field member
      apply (layoutFieldsConforms_iff layout fields).mp fieldTypes field.ty
      rw [types]
      exact List.mem_map.mpr ⟨field, member, rfl⟩

#print axioms LayoutConforms.descriptor
#print axioms LayoutFieldsConforms.selected

end Goose.Proofs.ConstructionAcceptedExecution
