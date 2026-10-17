import Goose.Lower.Validation.SummaryPreservationSourceControlKernelsLet

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem readable_not_refSlice (type : Ty) (readable : type.readable = true) :
    type.isRefSlice = false := by
  cases type <;> simp_all [Ty.readable, Ty.isRefSlice]
  rename_i mu target
  cases target <;> simp_all [Ty.readable, Ty.isRefSlice, Ty.refTarget]

theorem statementReplay_rebind {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    {slotId : VarId} {expression : Expr} {origin : OriginId}
    (tables : SourceRootTables typingEnv env) (accepted : Core.validate env.mod = .ok ())
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (checked : CtxOk env.mod env.impl env.ctx)
    (child : ExpressionReplayAt typingEnv env results vt target scopeCount expression initial upper) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.rebind slotId expression origin)
      initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerExpr expression le initial
  obtain ⟨localVar, childType, sourceRow, visible, reference, mutable, childTyped, passable, _⟩ := tyStmt_rebind_children typed
  have variableRow : env.impl.vars[slotId]? = some localVar := by rw [tables.variablesEq]; exact sourceRow
  have sourceEnvironment : SourceReadableEnvironment typingEnv :=
    SourceReadableEnvironment.implementation (tables.moduleEq ▸ accepted)
      (tables.moduleEq ▸ implementationRow) tables.variablesEq.symm
  have readable := source_passable_expression_readable expression sourceEnvironment childTyped passable reference
  have ordinary : localVar.ty.isRefSlice = false := readable_not_refSlice _ readable
  have originBound : origin < le.mod.origins.size := tables.mutation_origin_bound typed
  have slotBound : slotId < le.slots.size := by
    simpa only [le, lowerEnv, Array.size_mapIdx] using (Array.getElem?_eq_some_iff.mp variableRow).1
  obtain ⟨roots, sourceAfter, childReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have contract := rpStmt_rebind_contract childReplay replay
  have priorEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) sourceAfter.eff after.eff := by
    rw [contract.2]
    split
    · exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
        fun target member => addTargets_left _ _ target member, fun h => h, fun h => h, fun h => h⟩
    · exact EffectRefinement.refl _ _
  have childNative : NativeRows vt lowered.2 := native.of_prefix
    ((types_coerceSlot slotId lowered.1 origin le lowered.2 _ _ rfl).trans
      ((types_emitDef (.slotAddr slotId) le _ _ _ rfl).trans (types_emitEffect _ le _ _ _ rfl)))
  obtain ⟨middle, childReady, valueInfo, childPrefix⟩ := child childType start finish before sourceAfter roots
    childTyped childReplay (priorEffect.trans ceiling) ready generated childNative
  have suffix : ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      le scopeCount (typedContextSlotUpper env.mod env.ctx env.impl)
      (lowerStmt loop (.rebind slotId expression origin) le initial).2 next ∧
      ∀ old, old < middle.vals.size → rootsAt next.vals old = rootsAt middle.vals old := by
    cases current : lowered.2.cur with
    | none =>
      let action : B Unit := do
        let value ← coerceSlot slotId lowered.1 origin
        let address ← emitDef (.slotAddr slotId)
        Goose.Lower.emitEffect (.store address value (some origin))
      have stopped := childReady.stopped
        (StoppedGraph.bind (stopped_coerceSlot slotId lowered.1 origin) (fun _ =>
          StoppedGraph.bind (stopped_emitDef _) fun _ => stopped_emitEffect _)) current
        (rfl : action le lowered.2 = ((), (action le lowered.2).2))
      exact ⟨middle, stopped, fun _ _ => rfl⟩
    | some block =>
      have live : lowered.2.cur.isSome = true := by rw [current]; rfl
      obtain ⟨coercedUpper, coercedRoots, coercedEffects, coercedValue, coercedSlots, coercedSymbols,
        coercedCurrent, coercedBlock, coercedBound, coercedPrefix⟩ := coerceSlot_refined_witness_growth slotId origin
          childReady.symbols current (childReady.current block current) childReady.roots childReady.effects
          (valueInfo live).bound (valueInfo live).refined originBound
      let coerced := coerceSlot slotId lowered.1 origin le lowered.2
      let address := emitDef (.slotAddr slotId) le coerced.2
      have coercedReady : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
          le scopeCount (typedContextSlotUpper env.mod env.ctx env.impl) coerced.2 coercedUpper :=
        ⟨coercedRoots, coercedEffects, coercedSymbols, fun candidate row => by
          rw [coercedCurrent] at row; cases row; exact coercedBlock, coercedSlots.trans childReady.slotsEq⟩
      obtain ⟨next, addressReady, addressValue, addressPrefix⟩ := coercedReady.emitDef (.slotAddr slotId) [.local slotId]
        (by simp [Op.uses]) (by simp [Op.origin])
        (by simpa [Op.SymbolRefsValid] using slotBound) (effectRefinement_empty _ _)
        (by intro root member; exact Or.inl (by simpa only [rootsOfDef] using member))
      have slotRow : le.slots[slotId]? = some ⟨localVar.ty, localVar.kind, localVar.scope, slotId⟩ := by
        simp [le, lowerEnv, Array.getElem?_mapIdx, variableRow]
      obtain ⟨mutability, operation⟩ : ∃ mu, (Op.slotAddr slotId).resultTy (tyEnv le coerced.2) =
          .ok (.data (.ref mu localVar.ty)) := by
        simp only [Op.resultTy, tyEnv, slotRow]
        exact ⟨_, rfl⟩
      have recorded := emitDef_recorded coercedCurrent operation
      have addressCurrent : address.2.cur = some block := recorded.2.1.trans coercedCurrent
      have addressLive : address.2.cur.isSome = true := by rw [addressCurrent]; rfl
      have addressRoots : rootsAt next.vals address.1 = [.local slotId] := by
        simpa only [rootsOfDef] using (addressValue addressLive).2.1
      have valueBound : coerced.1 < address.2.vals.size :=
        Nat.lt_of_lt_of_le coercedBound (adv_emitDef (rfl : emitDef (.slotAddr slotId) le coerced.2 = address)).vals
      have valueRoots : RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt next.vals coerced.1) roots := by
        rw [addressPrefix coerced.1 (by rw [coercedReady.roots.valueSize]; exact coercedBound)]
        exact coercedValue
      have slotRoots := bindRootsV_typed_slot_bound checked.annotationShape variableRow ordinary contract.1 valueRoots
      have addressNative : NativeRows vt address.2 := native.of_prefix (types_emitEffect (.store address.1 coerced.1 (some origin)) le address.2 _ _ rfl)
      have addressType : vt[address.1]? = some (some (.data (.ref mutability localVar.ty))) :=
        addressNative _ _ recorded.2.2.1
      have owner : (ownerTy vt address.1).any Ty.isRefLike = true := by
        simpa [ownerTy, addressType] using reference
      have completed := addressReady.emitEffect_live (.store address.1 coerced.1 (some origin))
        (by intro _; apply Inst.SymbolsWithin.eff
            · simpa [Effect.uses] using And.intro (addressValue addressLive).1 valueBound
            · intro candidate same; cases same; exact originBound
            · trivial)
        (by
          intro _ slot member root found
          rw [addressRoots] at member
          have same : slot = slotId := RootRef.local.inj (List.mem_singleton.mp member)
          subst slot
          rw [addressReady.slotsEq]
          exact slotRoots root found)
        (by intro _; exact (effectStep_rebind_refines_from_source variableRow reference addressRoots owner childReplay replay).trans ceiling)
      refine ⟨next, completed, ?_⟩
      intro old bound
      have growth : middle.vals.size ≤ coercedUpper.vals.size := by
        rw [childReady.roots.valueSize, coercedReady.roots.valueSize]
        exact (advB_coerceSlot slotId lowered.1 origin le lowered.2 _ _ rfl).vals
      exact (addressPrefix old (Nat.lt_of_lt_of_le bound growth)).trans (coercedPrefix old bound)
  obtain ⟨next, completed, retained⟩ := suffix
  have retainedAll : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
    intro old bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, childReady.roots.valueSize]
      exact (advB_lowerExpr expression le initial _ _ rfl).vals
    exact (retained old (Nat.lt_of_lt_of_le bound growth)).trans (childPrefix old bound)
  exact ⟨next, completed, retainedAll, mutation_statement_transfer loop typed rfl ready retainedAll⟩

#print axioms statementReplay_rebind

end Goose.Lower.Validation.SummaryPreservation
