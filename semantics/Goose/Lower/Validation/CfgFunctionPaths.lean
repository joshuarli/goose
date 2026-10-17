import Goose.Lower.Validation.CfgSourcePaths
import Goose.Lower.Finish

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem path_finishFunction (impl : Core.Impl) (value : ValueId) : PathAction (finishFunction impl value) := by
  refine ⟨advB_finishFunction impl value, ?_⟩
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    simp only [finishFunction, bind_run, read_apply, isLive_none current, Bool.false_eq_true,
      ite_false, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some source =>
    simp only [finishFunction, bind_run, read_apply, isLive_run current, ite_true] at run
    change ((if !impl.results.isEmpty && impl.body.value.isNone &&
        Core.Block.diverges env.mod.noReturn impl.body then
      (do
        let (sink, _) ← newBlock []
        emitTerm (.br sink [])
        setCur (some sink)
        emitTerm (.br sink []) : B Unit)
      else emitTerm (.ret (if impl.body.value.isSome then [value] else []) none)) env before) =
        (result, after) at run
    cases synthetic : (!impl.results.isEmpty && impl.body.value.isNone &&
        Core.Block.diverges env.mod.noReturn impl.body) with
    | false =>
      simp only [synthetic, Bool.false_eq_true, ite_false] at run
      exact paths_emitTerm _ env before result after run paths bounded
    | true =>
      simp only [synthetic, ite_true] at run
      exact paths_header0 (tail := fun sink => emitTerm (.br sink []))
        (fun _ => (path_emitTerm _).live) env before result after run paths bounded (by simp [current])

theorem paths_function_start (types : List VTy) (continuation : List ValueId → B Unit)
    (preserves : ∀ params, PathAction (continuation params)) (env : LEnv) :
    let action : B Unit := do
      let (entry, params) ← newBlock types
      setCur (some entry)
      continuation params
    let (_, state) := action env initState
    ReachableBuilder state ∧ 0 < state.blocks.size := by
  let pair := (newBlock types env initState).1
  let initial := (newBlock types env initState).2
  let started := (setCur (some pair.1) env initial).2
  have initialPaths : ReachableBuilder started := by
    intro block bound
    have one : started.blocks.size = 1 := rfl
    have zero : block = 0 := by rw [one] at bound; nat_omega
    subst block
    exact BuilderPath.entry
  have initialBound : LiveBound started := by
    intro block row
    have entry : pair.1 = 0 := rfl
    change some pair.1 = some block at row
    have zero := Option.some.inj row
    rw [← zero]
    change 0 < 1
    decide
  have paths := (preserves pair.2).paths env started _ _ rfl initialPaths initialBound
  have growth := (preserves pair.2).advance env started _ _ rfl
  have positive : 0 < (continuation pair.2 env started).2.blocks.size :=
    Nat.lt_of_lt_of_le (by change 0 < 1; decide) growth.ext.1
  exact ⟨paths, positive⟩

theorem lowerImpl_reachable (module : Core.Module) (impl : Core.Impl) :
    ∀ block, block < (lowerImpl module impl).blocks.size →
      (reachable (lowerImpl module impl))[block]? = some true := by
  let env := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let continuation : List ValueId → B Unit := fun params => do
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have actionPaths : ∀ params, PathAction (continuation params) := fun params =>
    PathAction.bind (path_lowerBlock none _ false impl.body) fun value => path_finishFunction impl value
  have started := paths_function_start types continuation actionPaths env
  exact started.1.finished started.2 (lowerImpl module impl) rfl

theorem lowerContextAt_reachable (module : Core.Module) (context : Core.Context) (impl : Core.Impl) :
    ∀ block, block < (lowerContextAt module context impl).blocks.size →
      (reachable (lowerContextAt module context impl))[block]? = some true := by
  intro block bound
  rw [reachable_of_blocks (left := lowerContextAt module context impl)
    (right := lowerImpl module impl) rfl]
  exact lowerImpl_reachable module impl block bound

theorem lowerGlobal_reachable (module : Core.Module) (global : Core.Global) :
    ∀ block, block < (lowerGlobal module global).init.blocks.size →
      (reachable (lowerGlobal module global).init)[block]? = some true := by
  let env := lowerEnv module #[] [global.ty]
  let continuation : List ValueId → B Unit := fun _ => do
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have actionPaths : ∀ params, PathAction (continuation params) := fun _ =>
    PathAction.bind (path_lowerExpr global.init) fun _ => path_emitTerm _
  have started := paths_function_start [] continuation actionPaths env
  exact started.1.finished started.2 (lowerGlobal module global).init rfl

end Goose.Lower.Validation
