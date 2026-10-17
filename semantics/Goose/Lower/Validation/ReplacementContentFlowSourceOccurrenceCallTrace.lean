import Goose.Lower.GeneratedBuilder
import Goose.Lower.Validation.SourceCanonicalRootFloorsMetadata
import Goose.Lower.Validation.SourceCanonicalRootFloorsWriteLookup
import Goose.Lower.Validation.ReplacementContentFlowSourceNativeContinuation

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

def CallArgumentsTrace (env : PEnv) (syntaxArgs : List Arg) (args : List ValueId) (func : Func)
    (callee : FnId) (sourceOrigin : OriginId) : Prop :=
  ∃ returnTypes before after siteRoot sourcePath,
    lowerArgs syntaxArgs (lowerEnv env.mod env.impl.vars returnTypes) before = (args, after) ∧
      GeneratedBuilderState before ∧ after.cur.isSome = true ∧ NativeBuilderContinuation func after ∧
      DemandNodeAt siteRoot sourcePath (.expression (.call callee syntaxArgs sourceOrigin)) ∧
      SourceCanonicalRootFloors.SourceRootScopeValid siteRoot ∧
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func after ∧
      ∃ typingEnv start finish type, typingEnv.mod = env.mod ∧ typingEnv.vars = env.impl.vars ∧
        Core.tyExpr typingEnv (.call callee syntaxArgs sourceOrigin) start = .ok (type, finish)

end Goose.Lower.Validation.ReplacementContentFlowSource
