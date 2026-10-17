import Goose.Lower.Validation.SummaryPreservationSourceBlockContracts
import Goose.Lower.Validation.SummaryPreservationReplayMutations
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SourceStatementTypingStorage
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Core.Sound.AccessTyping

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem mutation_statement_transfer {typingEnv output : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
    {initial : LS} {upper next : Prov} {scope start finish : Nat} {statement : Stmt} (loop : Option LoopCtx)
    (typed : tyStmt typingEnv scope statement start = .ok (output, finish))
    (plain : statement.isPlain = true)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper)
    (retained : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) :
    ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) initial upper
      (lowerStmt loop statement (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next :=
  ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
    (returnFrame_lowerStmt loop statement (tyStmt_returnFree_of_plain_or_inExpr statement typed (Or.inr plain)) _ _ _ _ rfl)

theorem _root_.Goose.Lower.Validation.SourceRootTables.mutation_origin_bound {typingEnv output : TEnv} {env : PEnv}
    {scope start finish : Nat} {statement : Stmt} (tables : SourceRootTables typingEnv env)
    (typed : tyStmt typingEnv scope statement start = .ok (output, finish)) :
    stmtSourceOrigin statement < env.mod.origins.size := by
  rw [tables.moduleEq]
  exact Core.tyStmt_success_origin_bound typed

theorem _root_.Goose.Lower.Validation.SourceRootTables.native_place_owner {typingEnv : TEnv} {env : PEnv}
    {vt : Array (Option VTy)} {place : Place} {info : PlaceInfo} {start finish : Nat}
    {before after : LS} {value : ValueId} (tables : SourceRootTables typingEnv env)
    (native : NativeRows vt after) (generated : GeneratedBuilderState before)
    (typed : tyPlace typingEnv place start = .ok (info, finish))
    (run : lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) before = (value, after))
    (live : after.cur.isSome = true) : ownerTy vt value = some info.ty := by
  apply native.place_ownerTy (results := env.impl.results.toList) generated typed _ live
  simpa only [← tables.moduleEq, ← tables.variablesEq] using run

theorem _root_.Goose.Lower.Validation.SourceRootTables.native_place_row {typingEnv : TEnv} {env : PEnv}
    {vt : Array (Option VTy)} {place : Place} {info : PlaceInfo} {start finish : Nat}
    {before after : LS} {value : ValueId} (tables : SourceRootTables typingEnv env)
    (native : NativeRows vt after) (generated : GeneratedBuilderState before)
    (typed : tyPlace typingEnv place start = .ok (info, finish))
    (run : lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) before = (value, after))
    (live : after.cur.isSome = true) : ∃ mutability, vt[value]? = some (some (.data (.ref mutability info.ty))) := by
  apply native.place (results := env.impl.results.toList) generated typed _ live
  simpa only [← tables.moduleEq, ← tables.variablesEq] using run

theorem mutation_read_shrink_aborts_extension (func : Func) (source : Core.Eff) (roots : List RootRef) :
    EffectRefinement func source {source with
      reads := addTargets source.reads (rootsTargets roots)
      shrinks := addTargets source.shrinks (rootsTargets roots)
      aborts := true} := by
  have prior := effectRefinement_read_shrink_extension func source roots
  exact ⟨prior.reads, prior.writes, prior.grows, prior.shrinks, prior.rebinds,
    fun _ => rfl, prior.outputs, prior.unknown⟩

end Goose.Lower.Validation.SummaryPreservation
