import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.ValueTypeReconstructionPermissionGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure ActualContentsAmbient (le : LEnv) (site : LS) where
  state : LS
  extension : site.Ext state
  types : TypePrefix site state
  authorized : ValueId → Prop
  closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
    (permissionFunc le state) state.vals authorized

def ActualContentsAmbient.before {le : LEnv} {before after : LS}
    (ambient : ActualContentsAmbient le after) (extension : before.Ext after)
    (types : TypePrefix before after) : ActualContentsAmbient le before :=
  ⟨ambient.state, extension.trans ambient.extension, types.trans ambient.types,
    ambient.authorized, ambient.closed⟩

def ActualContentsAmbient.current (le : LEnv) (site : LS) : ActualContentsAmbient le site :=
  ⟨site, .refl site, .refl site,
    fun value => (permissionsAt ((permissionFunc le site).permissionsFromTables
      (le.globals.map (·.2)) le.mod.structs site.vals) value).2 = true,
    contentsClosed_permissions _ _ _ _⟩

theorem ActualContentsAmbient.current_member {le : LEnv} {site : LS} {value : ValueId}
    (allowed : (tyEnv le site).contentsWritable value = some true) :
    (ActualContentsAmbient.current le site).authorized value := by
  rw [tyEnv_contentsWritable] at allowed
  change (permissionsAt _ value).2 = true
  cases row : ((permissionFunc le site).permissionsFromTables
      (le.globals.map (·.2)) le.mod.structs site.vals)[value]? with
  | none => simp [row] at allowed
  | some capability => simpa [permissionsAt, row] using allowed

theorem ActualContentsAmbient.definition {le : LEnv} {site : LS}
    (ambient : ActualContentsAmbient le site) {block : GIR.Block} {value : ValueId} {op : Op}
    (member : block ∈ (permissionFunc le site).blocks.toList)
    (definition : .def value op ∈ block.insts) (allowed : ambient.authorized value) :
    ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le ambient.state) ambient.state.vals ambient.authorized value op := by
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  obtain ⟨next, nextRow, _, suffix, instructions⟩ := permissionFunc_ext_at ambient.extension row
  exact ambient.closed.definitions next (Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextRow)) value op
    (by rw [instructions]; exact List.mem_append_left _ definition) allowed

theorem ActualContentsAmbient.emitted {le : LEnv} {before after : LS}
    (ambient : ActualContentsAmbient le after) {value : ValueId} {op : Op} {current : BlockId}
    (live : before.cur = some current) (bounded : current < before.blocks.size)
    (run : emitDef op le before = (value, after)) (allowed : ambient.authorized value) :
    ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le ambient.state) ambient.state.vals ambient.authorized value op := by
  rw [emitDef_run op le live] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  let body : GIR.Block := ⟨before.blocks[current].params,
    before.blocks[current].insts.toList ++ [.def before.vals.size op]⟩
  have row : (permissionFunc le
      { before with
        vals := before.vals.push (some (((op.resultTy (tyEnv le before)).toOption).getD (.data .unit)))
        blocks := before.blocks.modify current (fun block =>
          { block with insts := block.insts.push (.def before.vals.size op) }) }).blocks[current]? =
      some body := by
    simp [permissionFunc, body, Array.getElem?_modify, Array.getElem?_eq_getElem bounded]
  exact ambient.definition (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)) (by simp [body]) allowed

theorem ActualContentsAmbient.edge {le : LEnv} {site : LS}
    (ambient : ActualContentsAmbient le site) {block destination : GIR.Block} {term : Term}
    {edge : BlockId × List ValueId} {entry : (ValueId × VTy) × ValueId}
    (member : block ∈ (permissionFunc le site).blocks.toList)
    (instruction : .term term ∈ block.insts) (successor : edge ∈ term.permissionEdges)
    (row : (permissionFunc le site).blocks[edge.1]? = some destination)
    (argument : entry ∈ destination.params.zip edge.2) (allowed : ambient.authorized entry.1.1) :
    ambient.authorized entry.2 := by
  obtain ⟨index, sourceRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  obtain ⟨next, nextRow, _, suffix, instructions⟩ := permissionFunc_ext_at ambient.extension sourceRow
  obtain ⟨target, targetRow, parameters, _, _⟩ := permissionFunc_ext_at ambient.extension row
  exact ambient.closed.edges next (Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextRow)) term
    (by rw [instructions]; exact List.mem_append_left _ instruction) edge successor target targetRow entry
    (by rw [parameters]; exact argument) allowed

def ActualContentsExtraction (le : LEnv) (first : Nat) (site : LS) (value : ValueId) : Prop :=
  ∀ ambient : ActualContentsAmbient le site, ambient.authorized value →
    FreshContentsEvidence le first site value

theorem ActualContentsExtraction.current {le : LEnv} {first : Nat} {site : LS} {value : ValueId}
    (extract : ActualContentsExtraction le first site value)
    (allowed : (tyEnv le site).contentsWritable value = some true) :
    FreshContentsEvidence le first site value :=
  extract (.current le site) (ActualContentsAmbient.current_member allowed)

end Goose.Lower.Validation
