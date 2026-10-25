import Goose.Lower.Validation.ReplacementClosure
import Goose.Lower.Validation.FreshRunSource
import Goose.Lower.Validation.ProvenanceConvergenceFinite

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive StaticOwnerPlace : RootRef → Place → Prop
  | slot (slot) : StaticOwnerPlace (.local slot) (.var slot)
  | global (global) : StaticOwnerPlace (.global global) (.global global)
  | field {root place} (field) : StaticOwnerPlace root place → StaticOwnerPlace root (.field place field)

theorem staticOwner_emitDef_current {env : LEnv} {before after : LS} {value : ValueId} {op : Op}
    (run : emitDef op env before = (value, after)) : after.cur = before.cur := by
  cases current : before.cur with
  | none => rw [emitDef_none _ _ current] at run; cases run; exact current
  | some index => rw [emitDef_run _ _ current] at run; cases run; exact current

theorem staticOwner_lowerPlace_current {root : RootRef} {place : Place}
    (source : StaticOwnerPlace root place) {env : LEnv} {before after : LS} {value : ValueId}
    (run : lowerPlace place env before = (value, after)) : after.cur = before.cur := by
  induction source generalizing before after value with
  | slot slot => exact staticOwner_emitDef_current run
  | global global => exact staticOwner_emitDef_current run
  | field field child ih =>
    obtain ⟨address, middle, first, next⟩ := bind_eq.mp run
    exact (staticOwner_emitDef_current next).trans (ih first)

theorem emitted_root_of_closed {env : LEnv} {before captured state : LS}
    {func : Func} {results : Array (List RootRef)} {types : Array (Option VTy)} {provenance : Prov}
    {value : ValueId} {op : Op} {root : RootRef} {index : BlockId}
    (current : before.cur = some index) (live : LiveBound before)
    (run : emitDef op env before = (value, captured)) (extension : captured.Ext state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (dense : state.DenseDefinitions) (size : provenance.vals.size = func.numValues)
    (closed : ProvenanceConvergence.InstructionRootsClosed results types func provenance)
    (produced : root ∈ rootsOfDef results types func provenance value op) :
    root ∈ rootsAt provenance.vals value := by
  obtain ⟨block, member, definition⟩ := emitted_definition_retained current (live index current) run extension blocks
  have defined : value ∈ func.blocks.toList.flatMap GIR.Block.defs := by
    apply List.mem_flatMap.mpr
    refine ⟨block, member, ?_⟩
    apply List.mem_append_right
    exact List.mem_filterMap.mpr ⟨.def value op, definition, rfl⟩
  have bound := List.mem_range.mp ((dense_finishBlocks dense blocks).mem_iff.mp defined)
  exact closed.definition member definition (by simpa only [size] using bound) produced

theorem lowerPlace_static_root {root : RootRef} {place : Place} (source : StaticOwnerPlace root place)
    {env : LEnv} {before captured state : LS} {func : Func}
    {results : Array (List RootRef)} {types : Array (Option VTy)} {provenance : Prov}
    {value : ValueId} {index : BlockId}
    (run : lowerPlace place env before = (value, captured))
    (current : before.cur = some index) (live : LiveBound before)
    (extension : captured.Ext state) (blocks : func.blocks = finishBlocks state.blocks)
    (dense : state.DenseDefinitions) (size : provenance.vals.size = func.numValues)
    (closed : ProvenanceConvergence.InstructionRootsClosed results types func provenance) :
    root ∈ rootsAt provenance.vals value := by
  induction source generalizing before captured value index with
  | slot slot =>
    exact emitted_root_of_closed current live run extension blocks dense size closed (by simp [rootsOfDef])
  | global global =>
    exact emitted_root_of_closed current live run extension blocks dense size closed (by simp [rootsOfDef])
  | field field child ih =>
    obtain ⟨address, middle, first, next⟩ := bind_eq.mp run
    have inputRoot := ih first current live ((adv_emitDef next).ext.trans extension)
    have middleCurrent := (staticOwner_lowerPlace_current child first).trans current
    have middleLive := liveBound_of_adv (advB_lowerPlace _ _ _ _ _ first) live
    apply emitted_root_of_closed middleCurrent middleLive next extension blocks dense size closed
    exact inputRoot

theorem lowerPlace_static_provenance_root {root : RootRef} {place : Place}
    (source : StaticOwnerPlace root place)
    {env : LEnv} {before captured state : LS} {module : GIR.Module} {func : Func}
    {results : Array (List RootRef)} {types : Array (Option VTy)} {value : ValueId} {index : BlockId}
    (run : lowerPlace place env before = (value, captured))
    (current : before.cur = some index) (live : LiveBound before)
    (extension : captured.Ext state) (blocks : func.blocks = finishBlocks state.blocks)
    (dense : state.DenseDefinitions) (member : func ∈ module.funcs.toList)
    (bounded : ProvenanceConvergence.RootBounds results func module.globals.size) :
    root ∈ rootsAt (func.provenance results types (ProvenanceConvergence.moduleRootCount module)).vals value := by
  exact lowerPlace_static_root source run current live extension blocks dense
    (ProvenanceConvergence.provenance_sizes results types func (ProvenanceConvergence.moduleRootCount module)).2
    (ProvenanceConvergence.provenance_module_instructionRootsClosed member bounded)

end Goose.Lower.Validation
