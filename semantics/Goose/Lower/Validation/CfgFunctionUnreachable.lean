import Goose.Lower.Validation.CfgSourceUnreachable

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def FunctionUnreachable (noReturn : ContextId → Bool) (func : Func) : Prop :=
  ∀ block ∈ func.blocks.toList, UnreachableCode noReturn block.insts

theorem unreachable_finishFunction (impl : Impl) (value : ValueId) :
    UnreachableRun (finishFunction impl value) := by
  unfold finishFunction
  refine UnreachableRun.bind unreachable_read fun env => ?_
  refine UnreachableRun.bind unreachable_isLive fun live => ?_
  cases live
  · exact unreachable_pure _
  · simp only [ite_true]
    split
    · refine UnreachableRun.bind (unreachable_newBlock []) fun pair => ?_
      refine UnreachableRun.bind (unreachable_emitTerm _ (by intro h; cases h)) fun _ => ?_
      exact UnreachableRun.bind (unreachable_setCur _) fun _ =>
        unreachable_emitTerm _ (by intro h; cases h)
    · exact unreachable_emitTerm _ (by intro h; cases h)

theorem BuilderUnreachable.initState (noReturn : ContextId → Bool) :
    BuilderUnreachable noReturn initState := by
  intro index body row
  simp [Goose.Lower.initState] at row

theorem BuilderUnreachable.finished {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (func : Func)
    (blocks : func.blocks = finishBlocks state.blocks) : FunctionUnreachable noReturn func := by
  intro block member
  rw [blocks] at member
  have mapped : ∃ body ∈ state.blocks.toList, (⟨body.params, body.insts.toList⟩ : GIR.Block) = block := by
    simpa [finishBlocks] using member
  obtain ⟨body, present, same⟩ := mapped
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp present)
  rw [← same]
  exact checked index body row

theorem unreachable_function_start (types : List VTy) (continuation : List ValueId → B Unit)
    (preserves : ∀ params, UnreachableRun (continuation params)) (env : LEnv) :
    let action : B Unit := do
      let (entry, params) ← newBlock types
      setCur (some entry)
      continuation params
    let (_, state) := action env initState
    BuilderUnreachable env.mod.noReturn state := by
  apply UnreachableRun.bind (unreachable_newBlock types) (fun pair =>
    UnreachableRun.bind (unreachable_setCur _) (fun _ => preserves pair.2))
      env initState _ _ rfl (BuilderUnreachable.initState _)

theorem lowerImpl_unreachableCode (module : Core.Module) (impl : Core.Impl) :
    FunctionUnreachable module.noReturn (lowerImpl module impl) := by
  let env := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let continuation : List ValueId → B Unit := fun params => do
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have preserves : ∀ params, UnreachableRun (continuation params) := fun params =>
    UnreachableRun.bind (unreachable_lowerBlock none _ false impl.body) fun value =>
      unreachable_finishFunction impl value
  have checked := unreachable_function_start types continuation preserves env
  exact checked.finished (lowerImpl module impl) rfl

theorem lowerContextAt_unreachableCode (module : Core.Module) (context : Core.Context) (impl : Core.Impl) :
    FunctionUnreachable module.noReturn (lowerContextAt module context impl) :=
  lowerImpl_unreachableCode module impl

theorem lowerGlobal_unreachableCode (module : Core.Module) (global : Core.Global) :
    FunctionUnreachable module.noReturn (lowerGlobal module global).init := by
  let env := lowerEnv module #[] [global.ty]
  let continuation : List ValueId → B Unit := fun _ => do
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have preserves : ∀ params, UnreachableRun (continuation params) := fun _ =>
    UnreachableRun.bind (unreachable_lowerExpr global.init) fun _ =>
      unreachable_emitTerm _ (by intro h; cases h)
  have checked := unreachable_function_start [] continuation preserves env
  exact checked.finished (lowerGlobal module global).init rfl

theorem lower_unreachableCode (module : Core.Module) (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    FunctionUnreachable module.noReturn func := by
  rcases List.mem_append.mp member with implementation | initializer
  · change func ∈ (module.contexts.map fun context =>
        match (module.impls.map fun impl => (impl, lowerImpl module impl))[context.impl]? with
        | some (impl, body) => { body with roots := lowerContextRootInfo context impl }
        | none => invalidContextFunction context).toList at implementation
    simp only [Array.toList_map, List.mem_map] at implementation
    obtain ⟨context, _, equality⟩ := implementation
    rw [Array.getElem?_map] at equality
    cases source : module.impls[context.impl]? with
    | none =>
      simp only [source, Option.map_none] at equality
      subst func
      intro block member
      simp [invalidContextFunction] at member
    | some impl =>
      simp only [source, Option.map_some] at equality
      subst func
      exact lowerContextAt_unreachableCode module context impl
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, _, rfl⟩ := globalMember
    exact lowerGlobal_unreachableCode module source

end Goose.Lower.Validation
