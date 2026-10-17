import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsAssignOpCheckpoint

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem integerType_preserves (value : ValueId) (le : LEnv) (state : LS) :
    ∃ ty, intTyOf value le state = (ty, state) := by
  simp only [intTyOf, bind_run]
  generalize row : valTy value le state = pair
  have same : pair.2 = state := row ▸ valTy_run value le state
  obtain ⟨type, next⟩ := pair
  cases type <;> simp_all [pure_run]
  case data type => cases type <;> simp_all [pure_run]

 theorem statementReplay_assignOp {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {place : Place} {expression : Expr} (operation : BinOp) (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    {context : ContextId} (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (placeChild : PlaceReplayAt typingEnv env results vt target scopeCount place initial upper)
    (valueChild : ∀ provenance, ExpressionReplayAt typingEnv env results vt target scopeCount expression
      (Goose.Lower.emitDef (.load (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1)
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2).2 provenance) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.assignOp operation place expression origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
  obtain ⟨info, integer, childStart, placeTyped, infoType, valueTyped, _binding, _⟩ := tyStmt_assignOp_children typed
  obtain ⟨placeRoots, placeState, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceReplay := replay
  rw [rpStmt_assignOp_after_operands placeReplay valueReplay] at sourceReplay
  have sourceEffect := congrArg (fun pair => pair.2.eff) (Except.ok.inj sourceReplay).symm
  have valueCeiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) valueState.eff target := by
    apply EffectRefinement.trans (middle := after.eff) ?_ ceiling
    rw [sourceEffect]
    refine ⟨?_, ?_, fun _ h => h, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h⟩
    · exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
    · exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
    · intro h
      cases aborts : operation.mayAbort <;> simp [h]
  have placeCeiling := effectRefinement_before_expression valueReplay valueCeiling
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let address := lowerPlace place le initial
  let loaded := Goose.Lower.emitDef (.load address.1) le address.2
  let value := lowerExpr expression le loaded.2
  have actualType := integerType_preserves loaded.1 le value.2
  obtain ⟨runtimeType, typeRun⟩ := actualType
  have whole := lowerStmt_assignOp_after_rhs (op := operation) (org := origin) loop
    (rfl : lowerPlace place le initial = address) (rfl : Goose.Lower.emitDef (.load address.1) le address.2 = loaded)
    (rfl : lowerExpr expression le loaded.2 = value) typeRun
  have valueNative : NativeRows vt value.2 := by
    rw [whole] at native
    exact (native.of_prefix (types_emitEffect (.store address.1
      (Goose.Lower.emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2).1 (some origin)) le _ _ _ rfl)).of_prefix
      (types_emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2 _ _ rfl)
  have loadNative := valueNative.of_prefix (types_lowerExpr expression le loaded.2 _ _ rfl)
  have placeNative := loadNative.of_prefix (types_emitDef (.load address.1) le address.2 _ _ rfl)
  obtain ⟨middle, placeReady, placeValue, placePrefix⟩ := placeChild info start childStart before placeState placeRoots
    placeTyped placeReplay placeCeiling ready generated placeNative
  obtain ⟨next, completed, nextPrefix⟩ := placeReady.assignOp_checkpoint loop accepted contextRow implementationRow
    placeReplay valueReplay replay ceiling rfl (tables.mutation_origin_bound typed) (by
      intro live
      refine ⟨(placeValue live).1, (placeValue live).2, ?_, ?_⟩
      · rw [tables.native_place_owner placeNative generated placeTyped rfl live, infoType]
        rfl
      · change valRefLike vt address.2.vals.size = false
        change address.2.cur.isSome = true at live
        cases current : address.2.cur with
        | none => simp only [current, Option.isSome_none, Bool.false_eq_true] at live
        | some block =>
          have actualRun : lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars env.impl.results.toList) initial = address := by
            rw [← tables.moduleEq, ← tables.variablesEq]
          obtain ⟨mu, row⟩ := lowerPlace_generated_typed place placeTyped actualRun live generated
          have row' : address.2.vals[address.1]? = some (some (.data (.ref mu (.int integer)))) := by
            simpa only [infoType] using row
          have resultType : (Op.load address.1).resultTy (tyEnv le address.2) = .ok (.data (.int integer)) := by
            simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row', pure, Except.pure, bind, Except.bind]
          have emitted : loaded.1 = address.2.vals.size ∧ loaded.2.cur = address.2.cur ∧
              loaded.2.vals[loaded.1]? = some (some (.data (.int integer))) ∧
              (∀ old, old < address.2.vals.size → loaded.2.vals[old]? = address.2.vals[old]?) :=
            emitDef_recorded (le := le) current resultType
          have nativeRow := loadNative _ _ emitted.2.2.1
          rw [emitted.1] at nativeRow
          simp only [valRefLike, nativeRow, VTy.refLike, Ty.isRefLike]
    ) (by
      intro provenance childReady
      obtain ⟨next, nextReady, childValue, childPrefix⟩ := valueChild provenance (.int integer) childStart finish
        placeState valueState valueRoots valueTyped valueReplay valueCeiling childReady
        ((generated.lowerPlace place rfl).emitDef (.load address.1) rfl) valueNative
      exact ⟨next, nextReady, fun live => (childValue live).bound, childPrefix⟩)
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, placeReady.roots.valueSize]
      exact (advB_lowerPlace place le initial _ _ rfl).vals
    exact (nextPrefix old (Nat.lt_of_lt_of_le bound growth)).trans (placePrefix old bound)
  exact ⟨next, completed, retained, mutation_statement_transfer loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
