import Goose.Lower.Validation.CfgStoppingReturnFree
import Goose.Lower.Validation.CfgFunctionCompletion
import Goose.Lower.GeneratedTargetsFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def FunctionNoReturnCode (func : Func) : Prop :=
  ∀ block ∈ func.blocks.toList, NoReturnCode block.insts

theorem BuilderNoReturn.initState : BuilderNoReturn initState := by
  intro index body row
  simp [Goose.Lower.initState] at row

theorem BuilderNoReturn.finished {state : LS} (checked : BuilderNoReturn state) (func : Func)
    (blocks : func.blocks = finishBlocks state.blocks) : FunctionNoReturnCode func := by
  intro block member
  rw [blocks] at member
  have mapped : ∃ body ∈ state.blocks.toList, (⟨body.params, body.insts.toList⟩ : GIR.Block) = block := by
    simpa [finishBlocks] using member
  obtain ⟨body, present, same⟩ := mapped
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp present)
  rw [← same]
  exact checked index body row

theorem lowerImpl_stopping_noReturnCode (module : Core.Module) (impl : Core.Impl)
    (free : ReturnFreeStoppingBlock module.noReturn impl.body)
    (stopped : impl.body.stops module.noReturn = true) :
    FunctionNoReturnCode (lowerImpl module impl) ∧ 0 < (lowerImpl module impl).blocks.size := by
  let env := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let allocated := newBlock types env initState
  let started := (setCur (some allocated.1.1) env allocated.2).2
  let pre := (impl.params.toList.zip allocated.1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (fun (declaration : Core.LocalVar) => declaration.org)).getD 0)
  let body := lowerBlock none pre false impl.body env started
  have startChecked : BuilderNoReturn started :=
    (BuilderNoReturn.initState.newBlock types env).setCur (some allocated.1.1) env
  have bodyChecked := returnFree_stopping_lowerBlock none pre false impl.body env started body.2 body.1
    free stopped rfl startChecked
  have bodyStopped := cfg_stops_lowerBlock none pre false impl.body env started body.2 body.1 stopped rfl
  have finish : finishFunction impl body.1 env body.2 = ((), body.2) := by
    simp only [finishFunction, bind_run, read_apply, isLive_none bodyStopped, Bool.false_eq_true, ite_false, pure_run]
  have bodyGrowth := advB_lowerBlock none pre false impl.body env started body.1 body.2 rfl
  have positive : 0 < body.2.blocks.size := Nat.lt_of_lt_of_le (by change 0 < 1; decide) bodyGrowth.ext.1
  have blocks : (lowerImpl module impl).blocks = finishBlocks body.2.blocks := by
    change finishBlocks (finishFunction impl body.1 env body.2).2.blocks = finishBlocks body.2.blocks
    rw [finish]
  exact ⟨bodyChecked.finished _ blocks, by simpa only [blocks, finishBlocks, Array.size_map] using positive⟩

theorem lowerImpl_stopping_mayReturn (module : Core.Module) (impl : Core.Impl)
    (free : ReturnFreeStoppingBlock module.noReturn impl.body)
    (stopped : impl.body.stops module.noReturn = true) (current : Array Bool)
    (callees : ∀ callee, module.noReturn callee = true → current[callee]?.getD true = false) :
    funcMayReturn current (lowerImpl module impl) = false := by
  obtain ⟨noRet, nonempty⟩ := lowerImpl_stopping_noReturnCode module impl free stopped
  apply (lowerImpl_unreachableCode module impl).funcMayReturn_false noRet ?_ ?_ nonempty current callees
  · intro block present empty
    have count := (lowerImpl_terminators module impl block present).1
    rw [empty] at count
    contradiction
  · intro block present target member
    obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp present)
    exact lowerImpl_targetsBounded module impl row target member

end Goose.Lower.Validation
