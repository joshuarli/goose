import Goose.Lower.Validation.SourceRootShape
import Goose.Lower.Validation.SummaryPreservationLowerScalarLet

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerStmt_typed_nonref_let_source_witness {env : PEnv} {context : ContextId} {varId : VarId}
    {expression : Expr} {org : OriginId} {localVar : LocalVar}
    {typingEnv : TEnv} {typingStart typingFinish : Nat} {sourceRoots : List RootRef}
    {initialSource before after : RState} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {upper : Prov} {initial ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId}
    {value : ValueId} (loop : Option LoopCtx)
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (variableRow : env.impl.vars[varId]? = some localVar)
    (nonReference : localVar.ty.isRefLike = false)
    (tables : SourceRootTables typingEnv env)
    (typing : Core.tyExpr typingEnv expression typingStart = .ok (localVar.ty, typingFinish))
    (operandSource : rpExpr env expression { initialSource with nextVar := initialSource.nextVar + 1 } =
      .ok (sourceRoots, before))
    (source : rpStmt env (.letS varId expression org) initialSource = .ok ((), after))
    (operandRun : lowerExpr expression le initial = (value, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt upper.vals value) sourceRoots)
    (slots : upper.slots = typedContextSlotUpper env.mod env.ctx env.impl)
    (slotBound : varId < le.slots.size) (originBound : org < le.mod.origins.size) :
    ∃ next : Prov,
      BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) next
        (lowerStmt loop (.letS varId expression org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) next after.eff
        (lowerStmt loop (.letS varId expression org) le initial).2 ∧
      next.slots = upper.slots ∧
      (lowerStmt loop (.letS varId expression org) le initial).2.SymbolWF le scopeCount ∧
      (lowerStmt loop (.letS varId expression org) le initial).2.cur = some block := by
  have empty := source_expression_nonref_roots_empty expression tables typing nonReference operandSource
  subst sourceRoots
  exact lowerStmt_nonref_let_source_witness loop accepted contextLookup implLookup variableRow nonReference
    operandSource source operandRun symbols current blockBound witness prior valueBound roots slots slotBound originBound

end Goose.Lower.Validation.SummaryPreservation
