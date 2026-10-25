import Goose.Lower.Validation.SourceSymbolSourceAccepted
import Goose.Lower.Validation.SourceSymbolSourceLower

namespace Goose.Lower.Validation.SourceSymbolSource

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem finishFunction_source {le : LEnv} {count : Nat} (impl : Impl) (value : ValueId) :
    LS.SourceSymbolsRun le count (Goose.Lower.finishFunction impl value) := by
  simp only [Goose.Lower.finishFunction]
  apply LS.SourceSymbolsRun.bind LS.SourceSymbolsRun.readAction
  intro env
  apply LS.SourceSymbolsRun.bind LS.SourceSymbolsRun.isLive
  intro live
  cases live with
  | false => exact LS.SourceSymbolsRun.pure ()
  | true =>
    simp only [↓reduceIte]
    split
    · apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.newBlock [])
      intro allocated
      apply LS.SourceSymbolsRun.bind
        (LS.SourceSymbolsRun.emitTerm (.br allocated.1 []) (by simp [Term.origin]))
      intro _
      apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.setCur (some allocated.1))
      intro _
      exact LS.SourceSymbolsRun.emitTerm (.br allocated.1 []) (by simp [Term.origin])
    · exact LS.SourceSymbolsRun.emitTerm _ (by simp [Term.origin])

private theorem init_source (le : LEnv) (count : Nat) : LS.SourceSymbolsWF le count initState := by
  constructor
  · simp [LS.insts, initState]
  · simp [initState]

private theorem finishBlocks_source {state : LS} {le : LEnv} {count : Nat}
    (checked : LS.SourceSymbolsWF le count state) {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) :
    ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      Inst.SourceSymbolsWithin le count inst := by
  intro block member inst instMember
  rw [blocks, finishBlocks, Array.toList_map] at member
  obtain ⟨builder, builderMember, rfl⟩ := List.mem_map.mp member
  exact checked.1 inst (List.mem_flatMap.mpr ⟨builder, builderMember, instMember⟩)

private theorem parameter_initializers_bound {module : Core.Module} {index : ImplId} {impl : Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl)
    (values : List ValueId) :
    ∀ entry ∈ (impl.params.toList.zip values).map (fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map LocalVar.org).getD 0)),
      entry.1 < (lowerEnv module impl.vars impl.results.toList).slots.size ∧
      entry.2.2 < (lowerEnv module impl.vars impl.results.toList).mod.origins.size := by
  intro entry member
  obtain ⟨⟨param, value⟩, zipped, rfl⟩ := List.mem_map.mp member
  have paramMember := (List.of_mem_zip zipped).1
  obtain ⟨position, paramAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp paramMember)
  obtain ⟨aligned, localVar, localAt, _, _⟩ :=
    (validate_modOk module accepted).impl index impl lookup |>.params position param paramAt
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  have originBound := (checkImpl_variable_bounds checked localVar
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? localAt))).1
  simp only [aligned, localAt, Option.map_some, Option.getD_some]
  constructor
  · simpa [lowerEnv] using (Array.getElem?_eq_some_iff.mp localAt).1
  · exact originBound

theorem lowerImpl_source_symbols {module : Core.Module} {index : ImplId} {impl : Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    ∀ block ∈ (lowerImpl module impl).blocks.toList, ∀ inst ∈ block.insts,
      Inst.SourceSymbolsWithin (lowerEnv module impl.vars impl.results.toList)
        (lowerImpl module impl).scopes.size inst := by
  let le := lowerEnv module impl.vars impl.results.toList
  let count := (lowerImpl module impl).scopes.size
  let action : B Unit := do
    let (entry, params) ← Goose.Lower.newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    Goose.Lower.setCur (some entry)
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map LocalVar.org).getD 0)
    let value ← Goose.Lower.lowerBlock none pre false impl.body
    Goose.Lower.finishFunction impl value
  have references : LoweredWithin le (blockReferences impl.body) := by
    apply Within.lowered (implementation_references accepted lookup)
    all_goals simp [le, lowerEnv]
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  have scopes : ScopeBounds count (blockScopes none impl.body) :=
    ScopeTableContains.bounds (lowerImpl_lexicalScopeTable checked)
  have preservation : LS.SourceSymbolsRun le count action := by
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.newBlock _)
    intro allocated
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.setCur (some allocated.1))
    intro _
    apply LS.SourceSymbolsRun.bind
      (lowerBlock_references le count none none _ false impl.body references scopes
        (parameter_initializers_bound accepted lookup allocated.2))
    intro value
    exact finishFunction_source impl value
  let output := action le initState
  have bounds := preservation initState output.1 output.2 rfl (init_source le count)
  exact finishBlocks_source bounds rfl

theorem lowerGlobal_source_symbols {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (lookup : module.globals[index]? = some global) :
    ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ inst ∈ block.insts,
      Inst.SourceSymbolsWithin (lowerEnv module #[] [global.ty])
        (lowerGlobal module global).init.scopes.size inst := by
  let le := lowerEnv module #[] [global.ty]
  let count := (lowerGlobal module global).init.scopes.size
  let action : B Unit := do
    let (entry, _) ← Goose.Lower.newBlock []
    Goose.Lower.setCur (some entry)
    let value ← Goose.Lower.lowerExpr global.init
    Goose.Lower.emitTerm (.ret [value] (some global.org))
  have references : LoweredWithin le (exprReferences global.init) := by
    apply Within.lowered (initializer_references accepted lookup)
    all_goals simp [le, lowerEnv]
  have checked := validate_global_checks accepted lookup
  have scopes : ScopeBounds count (exprScopes none global.init) :=
    ScopeTableContains.bounds (lowerGlobal_lexicalScopeTable checked)
  have preservation : LS.SourceSymbolsRun le count action := by
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.newBlock [])
    intro allocated
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.setCur (some allocated.1))
    intro _
    apply LS.SourceSymbolsRun.bind (lowerExpr_references le count none global.init references scopes)
    intro value
    apply LS.SourceSymbolsRun.emitTerm
    intro origin equal
    simp only [Term.origin, Option.some.injEq] at equal
    subst origin
    exact checkGlobal_origin_bound checked
  let output := action le initState
  have bounds := preservation initState output.1 output.2 rfl (init_source le count)
  exact finishBlocks_source bounds rfl

theorem lowerContextAt_source_symbols {module : Core.Module} {index : ImplId} {impl : Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl)
    (context : Core.Context) :
    ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ inst ∈ block.insts,
      Inst.SourceSymbolsWithin (lowerEnv module impl.vars impl.results.toList)
        (lowerContextAt module context impl).scopes.size inst :=
  lowerImpl_source_symbols accepted lookup

end Goose.Lower.Validation.SourceSymbolSource
