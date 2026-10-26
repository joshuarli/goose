import Goose.Lower.DemandGeneratedClearValueBlock
import Goose.Lower.DemandGeneratedIndexEntry
import Goose.Lower.DemandGeneratedIndexChecks
import Goose.Lower.TypedControlExpressions
import Goose.Lower.DemandGeneratedOwner
import Goose.Lower.DemandGeneratedBlockPrefix
import Goose.Lower.TypedGlobals

namespace Goose.Lower.DemandGeneratedClearBlockChecks

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Lower Goose.Lower.DemandGeneratedIndexChecks

private def configuration : Cfg := ⟨.release, retainedIndexSource⟩
private def environment : Env := ⟨#[], 1, [], 0⟩
private def ownerState : St := { St.initial with nextAct := 1, store := Store.empty.introduce (.global 0) (.limited (.int .i64) 1 #[.int .i64 9] 1) }
private def initialState : St := { ownerState with nextAct := 2 }
private def clearedState : St := { initialState with nextScope := 1, store :=
  ⟨(initialState.store.roots.erase (.global 0)).insert (.global 0) (.limited (.int .i64) 1 #[.int .i64 9] 0)⟩ }
private def sample : ViewVal := ⟨⟨.global 0, []⟩, 0, 1, false⟩
private def context : FnCtx := ⟨⟨.release, lower retainedIndexSource⟩, retainedIndexFunction⟩
private def initialFrame : GIR.Frame := ⟨1, [], {}, 0⟩
private def addressFrame : GIR.Frame := initialFrame.set 0 (.val (.ref ⟨.global 0, []⟩))
private def sampledFrame : GIR.Frame := addressFrame.set 1 (.view sample)

private theorem initialized (accepted : Core.validate retainedIndexSource = .ok ()) : InitializedGlobals retainedIndexSource 1 ownerState :=
  InitializedGlobals.afterInitializer (cfg := configuration)
    (before := St.initial) (after := { St.initial with nextAct := 1 })
    (g := 0) (value := .limited (.int .i64) 1 #[.int .i64 9] 1)
    accepted (by rfl) (InitializedGlobals.initial _) 3 (by cbv)

private theorem sampled_reachable : Evidence.RuntimePoint context.cfg context.fn (0, 2) sampledFrame initialState := by
  have initial : Evidence.RuntimePoint context.cfg context.fn (0, 0) initialFrame initialState := by
    apply Evidence.RuntimePoint.initializer (fuel := 12) (index := 1) (before := ownerState)
      (global := lowerGlobal retainedIndexSource retainedIndexedGlobal)
    · decide
    · change 1 < (retainedIndexSource.globals.map (lowerGlobal retainedIndexSource)).size
      simp [retainedIndexSource, retainedIndexModule]
    · cbv
      simp only [execOp, execPure, bind_apply, pure_apply]
      cbv
    · change (retainedIndexSource.globals.map (lowerGlobal retainedIndexSource))[1]? = some _
      simp [retainedIndexSource, retainedIndexModule]
    · refine ⟨rfl, 1, initialState, rfl, ?_⟩
      cbv
  have addressStep : Evidence.RuntimeStep context.cfg context.fn (0, 0) initialFrame initialState (0, 1) addressFrame initialState := by
    apply Evidence.RuntimeStep.define (fuel := 0) generated_address.instruction
    simp only [execOp, execPure, pure_apply]
  have snapshotStep : Evidence.RuntimeStep context.cfg context.fn (0, 1) addressFrame initialState (0, 2) sampledFrame initialState := by
    apply Evidence.RuntimeStep.define (fuel := 0) generated_snapshot.instruction
    simp [execOp, execPure, addressFrame, initialFrame, initialState, ownerState, sample, Frame.set,
      getVal, getCell, Store.introduce, Store.empty, Store.read, Val.get?, readLoc, expectRef, expectArray,
      bind_apply, pure_apply]
  exact .step (.step initial addressStep) snapshotStep

theorem accepted_retained_index_body_all_runtime_points
    (accepted : Core.validate retainedIndexSource = .ok ()) :
    ∃ source : BlockSource configuration environment [] retainedIndexBlock initialState,
      source.path = [0, 1, 0] ∧
    ∃ selected : GeneratedDemandRootSelection retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot 2,
      GeneratedSourceOwner selected source.context ∧
    ∃ after finalFrame,
      Evidence.RuntimePoint context.cfg context.fn (0, 2) sampledFrame initialState ∧
      DemandUniformTraversal context
        (GeneratedClearBlockDemand source retainedSampleRows retainedSampleRows context [.int .i64]
          retainedIndexBefore none sampledFrame) 5
        ⟨(0, 2), sampledFrame, initialState⟩ ⟨(0, 7), finalFrame, after⟩ ∧
      execBlock 5 configuration environment [] retainedIndexBlock initialState = .ok (.normal (.int .i64 0)) after ∧
      (∀ taken reached, DemandRuntimePrefix context taken ⟨(0, 2), sampledFrame, initialState⟩ reached →
        (taken = 0 ∧ reached = ⟨(0, 2), sampledFrame, initialState⟩ ∧
          GeneratedClearBlockDemand source retainedSampleRows retainedSampleRows context [.int .i64]
            retainedIndexBefore none sampledFrame reached) ∨
        GeneratedBlockStatementsPrefix (cx := context) (results := [.int .i64]) (before := retainedIndexBefore) (loop := none) source selected
          retainedSampleRows retainedSampleRows sampledFrame (0, 2)
          (@GeneratedGlobalClearPrefixCursor configuration { environment with scopes := [(0, 0)] } context [.int .i64])
          taken reached) ∧
      ∀ taken reached, taken ≤ 5 → DemandRuntimePrefix context taken ⟨(0, 2), sampledFrame, initialState⟩ reached →
        Evidence.RuntimePoint context.cfg context.fn reached.point reached.frame reached.state ∧
        (∃ typing roots future,
          DemandFrameAt configuration environment context source.world typing roots future
            retainedSampleRows.values retainedSampleRows.runs reached ∨
          DemandFrameAt configuration { environment with scopes := [(0, 0)] } context source.world typing roots future
            retainedSampleRows.values retainedSampleRows.runs reached) ∧
        ∃ values, (getView reached.frame 1 >>= readRun) reached.state = .ok values reached.state := by
  obtain ⟨rootSource, rootTyping, rootRoots, _, _, rootPath, rootPlanOwner⟩ := acceptedGlobalActivation (cfg := configuration)
    (g := 1) (global := retainedIndexedGlobal) accepted (by rfl) (initialized accepted).invariant
  change ExprSource configuration environment
    (.read (.elem retainedOwnerView (.blockE retainedIndexBlock) 0)) initialState at rootSource
  have selected : GeneratedDemandRootSelection retainedIndexSource retainedIndexFunction retainedIndexEnvironment retainedIndexRoot 2 :=
    .global (globalId := 1) (by rfl)
  have rootOwned : GeneratedSourceOwner selected rootSource.context :=
    ⟨rootPlanOwner, by rw [rootPath]; exact .here _⟩
  obtain ⟨place, placeTyping, placeRoots, placeCanonical⟩ := rootSource.readChild
  have placeOwned : GeneratedSourceOwner selected place.context :=
    (rootOwned.child rfl 0 (.place (.elem retainedOwnerView (.blockE retainedIndexBlock) 0)) .place rfl (by trivial)).transport
      placeCanonical.plans.symm placeCanonical.path.symm rfl placeCanonical.context.symm
  have placePath : place.path = [0] := by rw [placeCanonical.path, rootPath]; rfl
  have placeAccess : place.rootsEnv.access = retainedIndexAccess := by rw [placeRoots, rootRoots]; rfl
  have placeOccurrence : GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment
      retainedIndexRoot place.path (.place (.elem retainedOwnerView (.blockE retainedIndexBlock) 0)) startLS := by
    rw [placePath]
    exact retainedPlaceOccurrence
  have placeRows : GeneratedDemandRows retainedIndexSource place.rootsEnv.access placeOccurrence (⟨[], []⟩ : RetainedSsaMap) := by
    simpa only [placePath, placeAccess, retainedElementPlace, retainedIndexExpression, retainedEmptyRows] using retainedPlaceRows
  have initialRelated : Rel configuration environment context initialFrame startLS := by constructor <;> rfl
  have addressPost : Post configuration environment context startLS initialFrame
      (lowerPlace (.global 0) retainedIndexEnvironment startLS).2 addressFrame (0, 1)
      [(0, .val (.ref ⟨.global 0, []⟩))] :=
    (Post.def_leaf (Post.init (pt := (0, 0)) initialRelated (by rfl))
      (show emitDef (.globalAddr 0) retainedIndexEnvironment startLS =
        (0, (lowerPlace (.global 0) retainedIndexEnvironment startLS).2) from rfl)
      (generated_view_place_extended retainedViewExtended) (.val (.ref ⟨.global 0, []⟩))).1
  have viewPost : Post configuration environment context startLS initialFrame
      (lowerView retainedOwnerView retainedIndexEnvironment startLS).2 sampledFrame (0, 2) [(1, .view sample)] :=
    (Post.def_leaf addressPost
      (show emitDef (.snapshot .owner 0) retainedIndexEnvironment (lowerPlace (.global 0) retainedIndexEnvironment startLS).2 =
        ((lowerView retainedOwnerView retainedIndexEnvironment startLS).1,
         (lowerView retainedOwnerView retainedIndexEnvironment startLS).2) from by cbv)
      retainedViewExtended (.view sample)).1
  have query : place.rootsEnv.access.aliasView (place.path ++ [0]) retainedOwnerView = .ok [retainedSampleAlias] := by
    rw [placePath, placeAccess]
    rfl
  have viewDone : evalView 2 configuration environment retainedOwnerView initialState = .ok sample initialState := by cbv
  obtain ⟨indexSource, indexCanonical, indexTyping, indexRoots, _, _, covered, admitted, bounded, atPoint, demanded⟩ :=
    accepted_generated_index_entry (cx := context) (results := [.int .i64]) place placeOccurrence placeRows
      (show (⟨[], []⟩ : RetainedSsaMap).Covers ⟨[], []⟩ from ⟨fun _ h => h, fun _ h => h⟩)
      (by intro profile alias member; cases member)
      (by constructor <;> intro cell member <;> cases member)
      (show (⟨[], []⟩ : RetainedSsaMap).Realizes retainedIndexSource place.world environment
        ⟨(0, 0), initialFrame, initialState⟩ from by constructor <;> intro cell member <;> cases member)
      query viewDone viewPost
  have indexOwned : GeneratedSourceOwner selected indexSource.context :=
    (placeOwned.child rfl 1 (.expression (.blockE retainedIndexBlock)) .expression rfl (by trivial)).transport
      indexCanonical.plans.symm indexCanonical.path.symm rfl indexCanonical.context.symm
  obtain ⟨source, sourceTyping, sourceRoots, canonical⟩ := indexSource.blockEChild
  have sourceOwned : GeneratedSourceOwner selected source.context :=
    (indexOwned.child rfl 0 (.block retainedIndexBlock) .block rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have sourcePath : source.path = [0, 1, 0] := by rw [canonical.path, indexCanonical.path, placePath]; rfl
  have sourceAccess : source.rootsEnv.access = retainedIndexAccess := by rw [sourceRoots, indexRoots, placeAccess]
  have occurrence : GeneratedDemandOccurrence retainedIndexSource retainedIndexFunction retainedIndexEnvironment
      retainedIndexRoot source.path (.block none [] true retainedIndexBlock) retainedIndexBefore := by
    rw [sourcePath]
    exact retainedBlockOccurrence
  have rows : GeneratedDemandRows retainedIndexSource source.rootsEnv.access occurrence retainedSampleRows := by
    simpa only [sourcePath, sourceAccess] using retainedBlockRows
  have coverage : retainedSampleRows.Covers retainedSampleRows := covered
  have sourceAdmitted : retainedSampleRows.Admitted retainedIndexSource.profile source.context.retained :=
    fun profile alias member => canonical.retained alias (admitted profile alias member)
  have sourceRealized : retainedSampleRows.Realizes retainedIndexSource source.world environment
      ⟨(0, 2), sampledFrame, initialState⟩ := by
    have indexRealized : retainedSampleRows.Realizes retainedIndexSource indexSource.world environment
        ⟨(0, 2), sampledFrame, initialState⟩ := demanded.operands
    simpa only [RetainedSsaMap.Realizes, canonical.world] using indexRealized
  have related : Rel configuration environment context sampledFrame retainedIndexBefore :=
    ((initialRelated.set 0 (.val (.ref ⟨.global 0, []⟩))).set 1 (.view sample)).stack_eq (by rfl)
  have sourceMetadata : SourceResults source.typingEnv source.rootsEnv [.int .i64] := by
    intro implementation found
    rw [sourceTyping, indexTyping, placeTyping, rootTyping] at found
    cases found
  have sourceLoops : LoopSourceMatches source.typingEnv none := by
    unfold LoopSourceMatches
    rw [sourceTyping, indexTyping, placeTyping, rootTyping]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  have generated : GeneratedBuilderState retainedIndexBefore :=
    startLS_generated.lowerView retainedOwnerView rfl
  have prefixInput : GeneratedPrefixInput configuration environment context [.int .i64] none
      source.typingEnv source.rootsEnv retainedIndexBefore sampledFrame (0, 2) :=
    ⟨sourceMetadata, sourceLoops, atPoint, related, rfl, rfl, trivial, trivial, trivial, generated, trivial⟩
  have decomposition := fun {taken : Nat} {reached : DemandRuntimePoint}
      (steps : DemandRuntimePrefix context taken ⟨(0, 2), sampledFrame, initialState⟩ reached) =>
    accepted_generated_block_statements_prefix (cx := context) (results := [.int .i64]) source selected sourceOwned occurrence rows coverage
    sourceAdmitted bounded sourceRealized prefixInput retainedBlockExtended
    (@GeneratedGlobalClearPrefixCursor configuration { environment with scopes := [(0, 0)] } context [.int .i64])
    (accepted_generated_global_clears_prefix (cfg := configuration) (env := { environment with scopes := [(0, 0)] }) (cx := context) (results := [.int .i64]) selected retainedIndexBefore none [] true retainedIndexBlock (.cons 0 0 .nil)) steps
  have statements : execStmts 4 configuration { environment with scopes := [(0, 0)] }
      retainedIndexBlock.stmts { initialState with nextScope := 1 } = .ok (.normal .unit) clearedState := by cbv
  obtain ⟨after, finalPoint, finalFrame, traversal, evaluatedBlock, post, _, _, invariant⟩ :=
    accepted_generated_global_clear_value_block_traversal (cx := context) (results := [.int .i64]) source (.cons 0 0 .nil) (by rfl) occurrence rows coverage
      sourceAdmitted bounded sourceRealized atPoint related retainedBlockExtended statements
  have finalPointEq : finalPoint = (0, 7) := Option.some.inj (post.pp.symm.trans (by rfl))
  subst finalPoint
  refine ⟨source, sourcePath, selected, sourceOwned, after, finalFrame, sampled_reachable, traversal, evaluatedBlock, (fun taken reached steps => decomposition steps), ?_⟩
  intro taken reached bound steps
  have valid := invariant taken reached bound steps
  have framed := valid.frame
  refine ⟨steps.reachable sampled_reachable, framed, ?_⟩
  obtain ⟨typing, roots, future, outer | inner⟩ := framed
  · exact (outer.operands.2 (1, retainedSampleAlias) (by simp only [retainedSampleRows, List.mem_singleton])).read_safe
  · exact (inner.operands.2 (1, retainedSampleAlias) (by simp only [retainedSampleRows, List.mem_singleton])).read_safe

end Goose.Lower.DemandGeneratedClearBlockChecks
