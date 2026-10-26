import Goose.Lower.FuelBoundBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private def fuelBoundBlockTail (n : Nat) (cfg : Cfg) (env : Env) (loop : Option LoopCtx)
    (scope : ScopeId) (si : ScopeInst) (value : Option Expr) (flow : Flow) : M Flow :=
  match flow with
  | .ret v => pure (.ret v)
  | .brk | .cont => match loop with
    | some _ => pure flow
    | none => do Core.releaseScope env scope si; pure flow
  | .normal v => do
    let result ← valueFlow n cfg value { env with scopes := (scope,si) :: env.scopes } (.normal v)
    Core.releaseScope env scope si
    pure result

theorem typedBlockFuelBound_mk {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)}
    {pre' : List (VarId × Val)} {want : Bool} {scope : ScopeId}
    {stmts : List Stmt} {value : Option Expr}
    (statements : ∀ residual, residual ≤ fuel → TypedStatementsFuelBound sourceFuel residual cfg results loop stmts)
    (expression : ∀ residual, residual ≤ fuel →
      match value with | none => True | some expr => TypedExprFuelBound sourceFuel residual cfg results expr) :
    TypedBlockFuelBound (sourceFuel + 1) fuel cfg results loop pre pre' want (.mk scope stmts value) := by
  intro env state source metadata loops ls ls' result pt cx fr lowering point extension rel prerel
    moduleEq resultsEq depth targets counter generated frames
  obtain ⟨ls1,ls_p,ls_s,ls_x,ls_l,u0,u,rx,h1,h2,h3,h4,h5,hls',hr⟩ := prefixBlock_unfold lowering
  cases u0
  cases u
  subst result
  have ext_l : ExtT ls_l cx.fn.blocks := by rw [hls'] at extension; exact extension
  have ext_x := ext_l.of_adv (adv_emitEffect h5)
  have ext_s := ext_x.of_adv (advB_lowerBlockValue want value _ _ _ _ h4)
  have ext_p := ext_s.of_adv (advB_lowerStmts loop stmts _ _ _ _ h3)
  have ext_i := ext_p.of_adv (advB_initSlots pre _ _ _ _ h2)
  have ext_1 : ExtT ls1 cx.fn.blocks := ext_i
  have generated1 := generated.emitEffect (.enter scope) h1
  have generatedI : GeneratedBuilderState { ls1 with stack := scope :: ls1.stack } :=
    ⟨generated1.dense,generated1.live,generated1.targets⟩
  have generatedP := generatedI.initSlots pre h2
  have framesP : LoopBuilderFrames loop ls_p :=
    ((frames.mono (adv_emitEffect h1).ext).of_blocks
      (before := ls1) (after := { ls1 with stack := scope :: ls1.stack }) rfl).mono
      (advB_initSlots pre _ _ _ _ h2).ext
  have generatedS := generatedP.lowerStmts loop stmts framesP.toTargets h3
  have first := block_enter_fuelBoundAt (sourceFuel := sourceFuel) (fuel := fuel) state point h1 ext_1 rel
  have assembled : FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => preparedCoreLoopBlock n cfg env loop scope stmts value pre')
      (fun flow _ pt' fr' => BlockLoopPost cfg env cx ls fr ls' loop (.mk scope stmts value)
        want rx flow pt' fr') state := by
    unfold preparedCoreLoopBlock
    change FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => freshScope >>= fun si => bindAll env.act si pre' >>= fun _ =>
        (execStmts n cfg { env with scopes := (scope,si) :: env.scopes } stmts >>=
          prepareLoopFlow { env with scopes := (scope,si) :: env.scopes } loop) >>=
          fuelBoundBlockTail n cfg env loop scope si value) _ state
    refine first.bind ?_
    · intro si entered pt1 fr1 hfresh enteredPost residual bound
      obtain ⟨hpp1,hv1,hfr1,hrel1⟩ := enteredPost
      have headScope : ({ env with scopes := (scope,si) :: env.scopes } : Env).scopes.head? =
          some (scope,si) := rfl
      have initialized := initSlots_fuelBoundAt (sourceFuel := sourceFuel) (fuel := residual) headScope pre pre' entered
        (source.preScopes prerel) h2 hpp1 ext_p hrel1 (PreRel.ext hfr1 prerel)
      refine initialized.bind ?_
      · intro initializedUnit initialized pt_s fr_s hbind initialPost statementFuel statementBound
        obtain ⟨hpp_s,rfl,hst,hvals⟩ := initialPost
        have innerRel := hrel1.stack_eq hst
        have initialSize : ls_p.vals.size = ls.vals.size := by rw [hvals]; exact hv1
        have freshEq : Res.ok state.nextScope { state with nextScope := state.nextScope + 1 } =
            .ok si entered := hfresh
        obtain ⟨rfl,rfl⟩ := Res.ok.inj freshEq
        rw [Core.Sound.bindAll_eq] at hbind
        obtain ⟨_,rfl⟩ := Res.ok.inj hbind
        obtain ⟨sourceS,typing,finalTyping,roots,world,observation,typingStart,typingEnd,
          rootsStart,rootsEnd,plans,path,context,all,blockValue,offset,_⟩ := source.enter
        have metadataS : SourceResults sourceS.typingEnv sourceS.rootsEnv results := by
          apply metadata.transport
          · rw [typing]; exact source.same.impl
          · rw [roots]
        have loopsS : LoopSourceMatches sourceS.typingEnv loop := by
          apply loops.transport
          rw [typing]; exact source.same.loops
        have statementReflection := statements statementFuel (Nat.le_trans statementBound bound)
          _ _ sourceS metadataS loopsS ls_p ls_s pt_s cx fr_s h3 hpp_s ext_s innerRel moduleEq
          resultsEq (loopDepthFits_entered scope _ depth) targets
          (counter.sameValues hfr1 initialSize) generatedP framesP
        refine statementReflection.bind ?_
        intro flow after pt2 fr2 actual matched valueFuel valueBound
        rcases matched with ⟨rfl,P2⟩ | returned | ⟨loopContext,loopEq,transfer⟩
        · have raw := preparedLoopFlow_normal_success actual
          have valueReflection : FuelBoundAt sourceFuel valueFuel cx pt2 fr2
              (fun n => valueFlow n cfg value
                { env with scopes := (scope,state.nextScope) :: env.scopes } (.normal .unit))
              (fun flow _ pt3 fr3 => ∃ v, flow = .normal v ∧ (value = none → v = .unit) ∧
                Post cfg { env with scopes := (scope,state.nextScope) :: env.scopes }
                  cx ls_s fr2 ls_x fr3 pt3 (blockCells (.mk scope stmts value) want rx v)) after := by
            cases value with
            | some expr =>
              have typed : tyExpr sourceS.typingAfter expr sourceS.typingEnd =
                  .ok (source.ty,source.typingEnd) := by
                rw [finalTyping,typingEnd]; exact source.typedValue
              have rooted : rpExpr sourceS.rootsEnv expr sourceS.rootsEnd =
                  .ok (source.roots,source.rootsEnd) := by
                rw [roots,rootsEnd]; exact source.rootedValue
              have effects : Core.Sound.EffLe source.rootsEnd.eff sourceS.world.E := by
                rw [world]; exact source.effects
              obtain ⟨child,childTyping,childRoots,childTy, _⟩ := sourceS.valueChild expr blockValue
                source.ty source.typingEnd source.roots source.rootsEnd typed rooted effects sourceFuel .unit raw
              obtain ⟨final,same,frame,normal⟩ := (sourceS.result sourceFuel (.normal .unit) raw).frame
              have finalEq := normal .unit rfl
              subst final
              have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
                apply metadata.transport
                · rw [childTyping,same.impl,typing]; exact source.same.impl
                · rw [childRoots,roots]
              simp only [lowerBlockValue] at h4
              simp only [valueFlow]
              have childReflection := expression valueFuel
                (Nat.le_trans valueBound (Nat.le_trans statementBound bound)) _ _ child childMetadata
                ls_s ls_x rx pt2 cx fr2 h4 P2.pp ext_x P2.rel moduleEq resultsEq generatedS
              refine childReflection.bind ?_
              intro v after pt3 fr3 done P3 residual bound
              exact FuelBoundAt.ret ⟨v,rfl,(fun h => by cases h),by
                simpa only [blockCells,Core.Block.value,Core.Block.scope,Option.isSome_some,Bool.true_or,↓reduceIte] using P3⟩
            | none =>
              cases want with
              | false =>
                simp only [lowerBlockValue] at h4
                obtain ⟨rfl,rfl⟩ := Prod.mk.inj h4
                exact FuelBoundAt.ret ⟨.unit,rfl,(fun _ => rfl),by
                  simpa only [blockCells,Core.Block.value,Core.Block.scope,Option.isSome_none,Bool.false_or,
                    Bool.false_eq_true,↓reduceIte] using Post.init P2.rel P2.pp⟩
              | true =>
                simp only [lowerBlockValue] at h4
                have leaf := leaf_def_fuelBoundAt (fuel := valueFuel) (state := after)
                  (Post.init P2.rel P2.pp) h4 ext_x (by intro f args org h; cases h)
                  (source := fun _ => pure ()) (sourceFuel := sourceFuel) (fun _ => RVal.val Val.unit)
                  (by simp [execPure])
                change FuelBoundAt sourceFuel valueFuel cx pt2 fr2
                  (fun _ => (pure () : M Unit) >>= fun _ => pure (Flow.normal .unit)) _ after
                refine leaf.bind ?_
                intro v after pt3 fr3 done P3 residual bound
                exact FuelBoundAt.ret ⟨.unit,rfl,(fun _ => rfl),by
                  simpa only [blockCells,Core.Block.value,Core.Block.scope,Option.isSome_none,Bool.false_or,
                    Bool.or_true,↓reduceIte] using P3⟩
          simp only [fuelBoundBlockTail]
          refine valueReflection.bind ?_
          · intro result afterValue pt3 fr3 valueRun valuePost leaveFuel leaveBound
            obtain ⟨v,rfl,isUnit,P3⟩ := valuePost
            have leaveReflection := block_leave_fuelBoundAt (sourceFuel := sourceFuel) (fuel := leaveFuel) afterValue P3.pp h5 ext_l P3.rel
            refine leaveReflection.bind ?_
            intro releasedUnit afterLeave pt4 fr4 leaveRun leavePost residual bound
            obtain ⟨hpp4,hv4,hfr4,hrel4⟩ := leavePost
            refine FuelBoundAt.ret (Or.inl ⟨v,rfl,isUnit,?_⟩)
            have P23 := P2.comp P3
            refine Post.rescope (P23.sub (cells' := blockCells (.mk scope stmts value) want rx v)
              (by simp)) initialSize hfr1 ?_ ?_ hfr4 ?_
            · rw [hls']; exact hpp4
            · rw [hls']; exact hv4
            · rw [hls']; exact hrel4
        · obtain ⟨returned,org,rfl,site⟩ := returned
          exact FuelBoundAt.ret (Or.inr (Or.inl ⟨returned,org,rfl,site⟩))
        · have rescope := StatementLoopPost.rescope (out := ls_s) (after := fr2)
            (flow := flow) (pt := pt2) depth rel innerRel hfr1 initialSize
          rcases transfer with ⟨rfl,exit⟩ | ⟨rfl,continued⟩
          · have outer := rescope (Or.inr (Or.inr ⟨loopContext,loopEq,Or.inl ⟨rfl,exit⟩⟩))
              (by intro v h; cases h)
            simp only [fuelBoundBlockTail,loopEq]
            exact FuelBoundAt.ret (Or.inr (loopEq ▸ outer))
          · have outer := rescope (Or.inr (Or.inr ⟨loopContext,loopEq,Or.inr ⟨rfl,continued⟩⟩))
              (by intro v h; cases h)
            simp only [fuelBoundBlockTail,loopEq]
            exact FuelBoundAt.ret (Or.inr (loopEq ▸ outer))
  exact assembled.of_source (otherFuel := sourceFuel + 1)
    (congrFun (prepareLoopFlow_execBlock sourceFuel cfg env loop scope stmts value pre' depth) state)


#print axioms typedBlockFuelBound_mk

end Goose.Lower
