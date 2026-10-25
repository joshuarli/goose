import Goose.Lower.Frag
import Goose.Lower.Validation.CfgBuilderFunctions

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

def NativeBuilderContinuation (func : Func) (after : LS) : Prop :=
  ∃ completed, after.Ext completed ∧ func.blocks = finishBlocks completed.blocks

theorem NativeBuilderContinuation.of_extension {func : Func} {before after : LS}
    (continuation : NativeBuilderContinuation func after) (extension : before.Ext after) :
    NativeBuilderContinuation func before := by
  obtain ⟨completed, tail, blocks⟩ := continuation
  exact ⟨completed, extension.trans tail, blocks⟩

theorem NativeBuilderContinuation.of_advance {func : Func} {before after : LS}
    (continuation : NativeBuilderContinuation func after) (advance : before.Adv after) :
    NativeBuilderContinuation func before := continuation.of_extension advance.ext

theorem NativeBuilderContinuation.of_blocks {func : Func} {completed : LS}
    (blocks : func.blocks = finishBlocks completed.blocks) :
    NativeBuilderContinuation func completed :=
  ⟨completed, .refl _, blocks⟩

theorem NativeBuilderContinuation.context {module : Core.Module} {ctx : Context} {impl : Impl} {after : LS}
    (extension : after.Ext (cfg_implState module impl)) :
    NativeBuilderContinuation (lowerContextAt module ctx impl) after :=
  ⟨cfg_implState module impl, extension, cfg_context_blocks module ctx impl⟩

theorem NativeBuilderContinuation.global {module : Core.Module} {source : Core.Global} {after : LS}
    (extension : after.Ext (cfg_globalState module source)) :
    NativeBuilderContinuation (lowerGlobal module source).init after :=
  ⟨cfg_globalState module source, extension, cfg_global_blocks module source⟩

#print axioms NativeBuilderContinuation.of_extension
#print axioms NativeBuilderContinuation.of_advance
#print axioms NativeBuilderContinuation.of_blocks
#print axioms NativeBuilderContinuation.context
#print axioms NativeBuilderContinuation.global

end Goose.Lower.Validation.ReplacementContentFlowSource
