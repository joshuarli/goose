import Goose.Lower.Validation.ActualContentsSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerExpr_generated_actual_contents (expr : Expr)
    {env : Core.TEnv} {target : Ty} {mu : Mutability} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (.ref mu target, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (contents : (tyEnv (lowerEnv env.mod env.vars results) after).contentsWritable value = some true)
    (generated : GeneratedBuilderState before := by assumption) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value :=
  (actualContents_sourceExpr expr source run live generated).current contents

theorem lowerPlace_generated_actual_contents (place : Place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (contents : (tyEnv (lowerEnv env.mod env.vars results) after).contentsWritable value = some true)
    (generated : GeneratedBuilderState before := by assumption) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value :=
  (actualContents_sourcePlace place source run live generated).current contents

theorem lowerView_generated_actual_contents (view : View)
    {env : Core.TEnv} {pair : Ty × Bool} {start finish : Nat}
    (source : Core.tyView env view start = .ok (pair, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerView view (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (contents : (tyEnv (lowerEnv env.mod env.vars results) after).contentsWritable value = some true)
    (generated : GeneratedBuilderState before := by assumption) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value :=
  (actualContents_sourceView view source run live generated).current contents

theorem lowerBlock_generated_actual_contents (body : Core.Block)
    {env : Core.TEnv} {target : Ty} {mu : Mutability} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (.ref mu target, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (contents : (tyEnv (lowerEnv env.mod env.vars results) after).contentsWritable value = some true)
    (generated : GeneratedBuilderState before := by assumption) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value :=
  (actualContents_sourceBlock body source run live generated).current contents

end Goose.Lower.Validation
