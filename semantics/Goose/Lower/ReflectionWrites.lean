import Goose.Lower.ReflectionTypedMutations
import Goose.Lower.ReflectionLeaves
import Goose.Lower.ReflectionEffects
import Goose.Lower.ReflectionSources
import Goose.Lower.WholeReplacementSources

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel Goose.Core.Sound

private theorem effectActionReflection {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt} {cellsk : List (ValueId × RVal)}
    {state : St} {effect : Effect} {le : LEnv} {sourceFuel : Nat} {source : Nat → M α}
    (post : Post cfg env cx ls fr lsk frk ptk cellsk)
    (emit : emitEffect effect le lsk = ((), ls1)) (extension : ExtT ls1 cx.fn.blocks)
    (equal : execEff cx.fn frk effect = source sourceFuel >>= fun _ => pure frk) (fuel : Nat) :
    ReflectAtFuel fuel cx ptk frk source
      (fun _ _ pt' fr' => Post cfg env cx ls fr ls1 fr' pt' cellsk) state := by
  cases fuel with
  | zero => exact ReflectAtFuel.zero cx ptk frk source _ state
  | succ fuel =>
    obtain ⟨_, instruction⟩ := Post.eff_leaf post emit extension
    have facts := emitEffect_facts emit post.pp extension
    have preserved : Post cfg env cx ls fr ls1 frk (ptk.1, ptk.2 + 1) cellsk := by
      refine ⟨facts.2.2.1, post.has, ?_, ?_, post.same, post.rel.stack_eq facts.2.1⟩
      · intro p hp
        rw [facts.1]
        exact post.lt p hp
      · rw [facts.1]
        exact post.mono
    exact (ReflectAtFuel.eff_step (fuel := fuel) (sourceFuel := sourceFuel)
      instruction equal).mono (fun _ _ _ _ matched => by
        rcases matched with ⟨rfl, rfl⟩
        exact preserved)

private theorem typedWriteEffectReflection {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt} {cellsk : List (ValueId × RVal)}
    {state : St} {effect : Effect} {le : LEnv} {loop : Option LoopCtx} {fuel sourceFuel : Nat}
    (post : Post cfg env cx ls fr lsk frk ptk cellsk)
    (emit : emitEffect effect le lsk = ((), ls1)) (extension : ExtT ls1 cx.fn.blocks)
    {source : M α} (equal : execEff cx.fn frk effect = source >>= fun _ => pure frk) :
    ReflectAtFuel fuel cx ptk frk
      (fun _ => source >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls1 loop flow pt' fr') state := by
  have reflected := normalEffectReflection (fuel := fuel) (sourceFuel := sourceFuel)
    (state := state) post emit extension (source := fun _ => source)
    (by intro n m bound; exact MonoM.refl _) equal
  exact reflected.mono (fun _ _ _ _ matched => Or.inl matched)

private theorem bindFlow_normal {α : Type} {source : M α} {continuation : α → M Flow}
    (normal : ∀ value state flow after, continuation value state = .ok flow after → flow = .normal .unit)
    {state : St} {flow : Flow} {after : St}
    (run : (source >>= continuation) state = .ok flow after) : flow = .normal .unit := by
  rw [bind_apply] at run
  cases hsource : source state with
  | stop reason next => simp [hsource] at run
  | ok value next =>
    have continuationRun : continuation value next = .ok flow after := by
      simpa [M.bind', hsource] using run
    exact normal value next flow after continuationRun

private theorem prepareLoopFlow_normal_only (env : Env) (loop : Option LoopCtx)
    (source : M Flow)
    (normal : ∀ state flow after, source state = .ok flow after → flow = .normal .unit) :
    source >>= prepareLoopFlow env loop = source := by
  funext state
  cases hsource : source state with
  | stop reason next => simp [bind_apply, hsource]
  | ok flow next =>
    have hflow := normal state flow next hsource
    subst flow
    cases loop <;> simp [bind_apply, pure_apply, hsource, prepareLoopFlow, prepareReturn, prepareLoopExit]

private theorem normalFlowMap_success {source : M Unit} {state : St} {flow : Flow} {after : St}
    (run : (source >>= fun _ => pure (Flow.normal .unit)) state = .ok flow after) :
    flow = .normal .unit := by
  cases hsource : source state with
  | stop reason next => simp [bind_apply, hsource] at run
  | ok value next => simp [bind_apply, hsource] at run; cases run; rfl

private theorem assignWholeSource_normal {cfg : Cfg} {env : Env} {owner : Place}
    {replacement : Expr} {fuel : Nat} {state : St} {flow : Flow} {after : St}
    (run : (evalPlace fuel cfg env owner >>= fun location =>
      truncateLoc location 0 >>= fun _ =>
        evalExpr fuel cfg env replacement >>= fun replacementValue =>
          (match replacementValue with
           | .resizable .. => writeLoc location replacementValue
           | _ => fault .shape) >>= fun _ => pure (Flow.normal .unit)) state =
      .ok flow after) : flow = .normal .unit := by
  exact bindFlow_normal
    (source := evalPlace fuel cfg env owner)
    (continuation := fun location => truncateLoc location 0 >>= fun _ =>
      evalExpr fuel cfg env replacement >>= fun replacementValue =>
        (match replacementValue with
         | .resizable .. => writeLoc location replacementValue
         | _ => fault .shape) >>= fun _ => pure (Flow.normal .unit))
    (normal := by
      intro location placeState flow final truncateRun
      exact bindFlow_normal
        (source := truncateLoc location 0)
        (continuation := fun _ => evalExpr fuel cfg env replacement >>= fun replacementValue =>
          (match replacementValue with
           | .resizable .. => writeLoc location replacementValue
           | _ => fault .shape) >>= fun _ => pure (Flow.normal .unit))
        (normal := by
          intro _ clearedState flow final expressionRun
          exact bindFlow_normal
            (source := evalExpr fuel cfg env replacement)
            (continuation := fun replacementValue =>
              (match replacementValue with
               | .resizable .. => writeLoc location replacementValue
               | _ => fault .shape) >>= fun _ => pure (Flow.normal .unit))
            (normal := by
              intro replacementValue expressionState flow final writeRun
              exact bindFlow_normal
                (source := match replacementValue with
                  | .resizable .. => writeLoc location replacementValue
                  | _ => fault .shape)
                (continuation := fun _ => pure (Flow.normal .unit))
                (normal := by
                  intro _ _ flow final run
                  exact (Res.ok.inj run).1.symm)
                writeRun)
            expressionRun)
        truncateRun)
    run

theorem typedStatementReflection_assignWhole {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {owner : Place} {replacement : Expr} {origin : OriginId}
    (placeChild : TypedPlaceReflection fuel cfg results owner)
    (expressionChild : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results replacement) :
    TypedStatementReflection fuel cfg results loop (.assignWhole owner replacement origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth
    targets counter generated frames
  obtain ⟨destination, typing, roots, _, _, ready⟩ := source.assignWholeChildren
  have destinationMetadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, ignored, cleared, clearRun, value, expressionAfter, replaceRun⟩ := lowering
  cases ignored
  obtain ⟨expressionRun, replaceRun⟩ := replaceRun
  have replaceExtension := extension.of_adv (adv_emitEffect replaceRun)
  have expressionExtension := replaceExtension.of_adv (advB_lowerExpr replacement _ _ _ _ expressionRun)
  have clearExtension := expressionExtension.of_adv (adv_emitEffect clearRun)
  have first := placeChild (env := env) (state := state) (source := destination)
    destinationMetadata (ls := ls) (after := middle) (id := address) (pt := pt) (cx := cx) (fr := fr)
    placeRun point clearExtension rel moduleEq resultsEq generated
  have middleGenerated := generated.lowerPlace owner placeRun
  have clearedGenerated := middleGenerated.emitEffect (.clear address (some origin)) clearRun
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env owner >>= fun location =>
        truncateLoc location 0 >>= fun _ =>
          evalExpr n cfg env replacement >>= fun replacementValue =>
            (match replacementValue with
             | .resizable .. => writeLoc location replacementValue
             | _ => fault .shape) >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
      (fun n k bound => (monoAll n k bound).place cfg env owner)
      (fun location n k bound =>
        MonoM.bind (MonoM.refl (truncateLoc location 0)) (fun _ =>
          MonoM.bind ((monoAll n k bound).expr cfg env replacement) (fun _ => MonoM.refl _)))
    intro n location afterPlace placePoint placeFrame placeDone placePost residual residualBound
    have addressCell := placePost.has (address, .val (.ref location)) (by simp)
    have clearEqual : execEff cx.fn placeFrame (.clear address (some origin)) =
        truncateLoc location 0 >>= fun _ => pure placeFrame := by
      simp only [execEff, getVal_of addressCell, Goose.Core.expectRef, pure_bind]
    have clearReflection := effectActionReflection (state := afterPlace) (sourceFuel := n)
      (source := fun _ => truncateLoc location 0) placePost clearRun expressionExtension clearEqual residual
    refine clearReflection.bind ?_
        (fun n k bound => MonoM.refl (truncateLoc location 0))
      (fun _ n k bound =>
        MonoM.bind ((monoAll n k bound).expr cfg env replacement) (fun _ => MonoM.refl _))
    intro k _ afterClear clearPoint clearFrame clearDone clearPost remaining remainingBound
    cases truncated : afterPlace.store.truncate location 0 with
    | error error => simp [truncateLoc, truncated] at clearDone
    | ok clearStore =>
      have stateEq : afterClear = { afterPlace with store := clearStore } := by
        simp only [truncateLoc, truncated] at clearDone
        exact (Res.ok.inj clearDone).2.symm
      subst afterClear
      obtain ⟨child, childTyping, childRoots, _, _, _, _⟩ :=
        ready n location afterPlace clearStore placeDone truncated
      have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
        rw [childTyping, childRoots]
        exact metadata
      have replacementReflection := (expressionChild remaining (Nat.le_trans remainingBound residualBound)) env
        { afterPlace with store := clearStore } child childMetadata cleared expressionAfter value
        clearPoint cx clearFrame expressionRun clearPost.pp replaceExtension clearPost.rel
        moduleEq resultsEq clearedGenerated
      let replaceAction : Val → Nat → M Flow := fun replacementValue _ =>
        (match replacementValue with
         | .resizable .. => writeLoc location replacementValue
         | _ => fault .shape) >>= fun _ => pure (Flow.normal .unit)
      have replacementComposition : ReflectAtFuel remaining cx clearPoint clearFrame
          (fun j => evalExpr j cfg env replacement >>= fun replacementValue => replaceAction replacementValue j)
          (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr')
          { afterPlace with store := clearStore } := by
        refine ReflectAtFuel.bind (source₂ := replaceAction) replacementReflection ?_ ?_ ?_
        · intro m replacementValue next expressionPoint expressionFrame expressionDone expressionPost final finalBound
          have combined := clearPost.comp expressionPost
          have addressCell := combined.has (address, .val (.ref location)) (by simp)
          have valueCell := combined.has (value, .val replacementValue) (by simp)
          have equal : execEff cx.fn expressionFrame (.replace address value (some origin)) =
              (match replacementValue with
               | .resizable .. => writeLoc location replacementValue
               | _ => fault .shape) >>= fun _ => pure expressionFrame := by
            simp only [execEff, getVal_of addressCell, getVal_of valueCell,
              Goose.Core.expectRef, pure_bind]
            funext s
            cases replacementValue <;> rfl
          exact typedWriteEffectReflection (sourceFuel := m) combined replaceRun extension equal
        · intro n m bound
          exact (monoAll n m bound).expr cfg env replacement
        · intro replacementValue n m bound
          exact MonoM.refl (replaceAction replacementValue n)
      exact replacementComposition
  refine composition.of_source (fun n => ⟨n + 1, ?_⟩)
  have sourceRun : execStmt (n + 1) cfg env (.assignWhole owner replacement origin) =
      (evalPlace n cfg env owner >>= fun location =>
        truncateLoc location 0 >>= fun _ =>
          evalExpr n cfg env replacement >>= fun replacementValue =>
            (match replacementValue with
             | .resizable .. => writeLoc location replacementValue
             | _ => fault .shape) >>= fun _ => pure (Flow.normal .unit)) := by
    funext state
    cases placeRun : evalPlace n cfg env owner state with
    | stop reason next => simp [execStmt, bind_apply, placeRun]
    | ok location placeState =>
      cases clearRun : truncateLoc location 0 placeState with
      | stop reason next => simp [execStmt, bind_apply, placeRun, clearRun]
      | ok _ clearState =>
        cases expressionRun : evalExpr n cfg env replacement clearState with
        | stop reason next => simp [execStmt, bind_apply, placeRun, clearRun, expressionRun]
        | ok replacementValue expressionState =>
          cases replacementValue <;>
            simp [execStmt, bind_apply, placeRun, clearRun, expressionRun,
              M.bind', M.pure', Functor.map]
  rw [sourceRun]
  exact congrFun (prepareLoopFlow_normal_only env loop _ (by
    intro state flow final run
    exact assignWholeSource_normal run)) state

private theorem assignOpSafe {cfg : Cfg} {env : Env} {state : St}
    {operation : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assignOp operation place expression origin) state)
    (fuel : Nat) :
    Sat (execStmt fuel cfg env (.assignOp operation place expression origin)) state
      (fun _ _ => True) := by
  exact ((Core.Sound.specs_all (Core.Sound.validate_modOk cfg.mod source.accepted)
    cfg.profile source.plans fuel).stmt source.path (.assignOp operation place expression origin)
    source.context source.observation source.world source.typingEnv source.typingAfter source.rootsEnv env state
    source.scope source.typingStart source.typingEnd source.rootsStart source.rootsEnd source.lowerBound
    source.active source.access source.protection source.observed source.classified source.permission source.frame
    source.scopeHead source.top source.bounded source.typed source.rooted source.effects).mono
      (by intro flow after matched; trivial)

private theorem assignOpReadInt {cfg : Cfg} {env : Env} {state : St}
    {operation : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assignOp operation place expression origin) state)
    {fuel : Nat} {location : Loc} {afterPlace : St}
    (placeRun : evalPlace fuel cfg env place state = .ok location afterPlace) :
    ∃ type value, readLoc location afterPlace = .ok (.int type value) afterPlace := by
  have safe := assignOpSafe source (fuel + 1)
  cases readRun : afterPlace.store.read location with
  | error error =>
      have fullRun : execStmt (fuel + 1) cfg env (.assignOp operation place expression origin) state =
          .stop (.fault error) afterPlace := by
        simp only [execStmt, bind_apply, placeRun, readLoc, readRun]
      have contradiction : False := by
        simp [Sat, fullRun] at safe
      exact contradiction.elim
  | ok old =>
      cases old with
      | int type value => exact ⟨type, value, by simp [readLoc, readRun]⟩
      | bool | unit | fixed | record | resizable | limited | ref | slice =>
          have fullRun : execStmt (fuel + 1) cfg env (.assignOp operation place expression origin) state =
              .stop (.fault .shape) afterPlace := by
            simp only [execStmt, bind_apply, placeRun, readLoc, readRun,
              expectInt, M.stop, Core.fault]
          have contradiction : False := by
            simp [Sat, fullRun] at safe
          exact contradiction.elim

private def assignOpUpdate (cfg : Cfg) (operation : BinOp) (origin : OriginId)
    (location : Loc) (oldType : IntTy) (oldValue : Int) (rightValue : Val) : M Flow := do
  let (rightType, rightInteger) ← expectInt rightValue
  expectSameTy oldType rightType
  match evalBin cfg.profile operation oldType oldValue rightInteger with
  | .ok value => writeLoc location (.int oldType value) >>= fun _ => pure (.normal .unit)
  | .error kind => abortAt (AbortKind.ofNum kind) origin

private theorem assignOpUpdate_normal {cfg : Cfg} {state : St} {flow : Flow} {after : St}
    {operation : BinOp} {origin : OriginId} {location : Loc} {oldType : IntTy}
    {oldValue : Int} {rightValue : Val}
    (run : assignOpUpdate cfg operation origin location oldType oldValue rightValue state =
      .ok flow after) : flow = .normal .unit := by
  cases hRight : expectInt rightValue state with
  | stop reason next => simp [assignOpUpdate, bind_apply, hRight] at run
  | ok pair next =>
      cases hSame : expectSameTy oldType pair.1 next with
      | stop reason final => simp [assignOpUpdate, bind_apply, hRight, hSame] at run
      | ok _ final =>
          cases hBinary : evalBin cfg.profile operation oldType oldValue pair.2 with
          | error kind => simp [assignOpUpdate, bind_apply, hRight, hSame, hBinary, abortAt, M.stop] at run
          | ok value =>
              exact normalFlowMap_success (source := writeLoc location (.int oldType value)) (by
                simpa only [assignOpUpdate,bind_apply,hRight,hSame,hBinary,map_eq_pure_bind] using run)

private theorem assignOpSource_normal {cfg : Cfg} {env : Env} {state : St}
    {operation : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    {fuel : Nat} {flow : Flow} {after : St}
    (run : (evalPlace fuel cfg env place >>= fun location =>
      readLoc location >>= fun oldValue =>
        expectInt oldValue >>= fun oldInteger =>
          evalExpr fuel cfg env expression >>= assignOpUpdate cfg operation origin location
            oldInteger.1 oldInteger.2) state = .ok flow after) :
    flow = .normal .unit := by
  exact bindFlow_normal
    (source := evalPlace fuel cfg env place)
    (continuation := fun location => readLoc location >>= fun oldValue =>
      expectInt oldValue >>= fun oldInteger =>
        evalExpr fuel cfg env expression >>= assignOpUpdate cfg operation origin location
          oldInteger.1 oldInteger.2)
    (normal := by
      intro location placeState flow afterPlace readRun
      exact bindFlow_normal
        (source := readLoc location)
        (continuation := fun oldValue => expectInt oldValue >>= fun oldInteger =>
          evalExpr fuel cfg env expression >>= assignOpUpdate cfg operation origin location
            oldInteger.1 oldInteger.2)
        (normal := by
          intro oldValue readState flow afterRead intRun
          exact bindFlow_normal
            (source := expectInt oldValue)
            (continuation := fun oldInteger => evalExpr fuel cfg env expression >>=
              assignOpUpdate cfg operation origin location oldInteger.1 oldInteger.2)
            (normal := by
              intro oldInteger intState flow afterInt expressionRun
              exact bindFlow_normal
                (source := evalExpr fuel cfg env expression)
                (continuation := assignOpUpdate cfg operation origin location oldInteger.1 oldInteger.2)
                (normal := by
                  intro rightValue expressionState flow afterExpression updateRun
                  exact assignOpUpdate_normal updateRun)
                expressionRun)
            intRun)
        readRun)
    run

theorem typedStatementReflection_assignOp {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {operation : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    (placeChild : TypedPlaceReflection fuel cfg results place)
    (expressionChild : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results expression) :
    TypedStatementReflection fuel cfg results loop (.assignOp operation place expression origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth
    targets counter generated frames
  obtain ⟨destination, destinationTyping, destinationRoots, _, _, ready⟩ := source.assignOpChildren
  have destinationMetadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [destinationTyping, destinationRoots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, afterPlaceBuilder, placeRun, old, afterLoadBuilder, loadRun,
    right, afterExpressionBuilder, expressionRun, operationType, afterTypeBuilder, typeRun,
    result, afterOperationBuilder, operationRun, storeRun⟩ := lowering
  have builderType := intTyOf_eq typeRun
  subst afterTypeBuilder
  have storeExtension := extension.of_adv (adv_emitEffect storeRun)
  have operationExtension := storeExtension.of_adv (adv_emitDef operationRun)
  have expressionExtension := operationExtension.of_adv
    (advB_lowerExpr expression _ _ _ _ expressionRun)
  have loadExtension := expressionExtension.of_adv (adv_emitDef loadRun)
  have first := placeChild env state destination destinationMetadata ls afterPlaceBuilder address pt cx fr
    placeRun point loadExtension rel moduleEq resultsEq generated
  have placeGenerated := generated.lowerPlace place placeRun
  let sourceAction : Nat → M Flow := fun n =>
    evalPlace n cfg env place >>= fun location =>
      readLoc location >>= fun oldValue =>
        expectInt oldValue >>= fun oldInteger =>
          evalExpr n cfg env expression >>= assignOpUpdate cfg operation origin location
            oldInteger.1 oldInteger.2
  have compositionGrouped : ReflectAtFuel fuel cx pt fr (fun n =>
      evalPlace n cfg env place >>= fun location =>
        (readLoc location >>= expectInt) >>= fun oldInteger =>
          evalExpr n cfg env expression >>= assignOpUpdate cfg operation origin location
            oldInteger.1 oldInteger.2)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
      (fun n k bound => (monoAll n k bound).place cfg env place)
      (fun location n k bound =>
        MonoM.bind (MonoM.refl (readLoc location >>= expectInt)) (fun oldInteger =>
          MonoM.bind ((monoAll n k bound).expr cfg env expression) (fun rightValue =>
            MonoM.refl (assignOpUpdate cfg operation origin location oldInteger.1 oldInteger.2 rightValue))))
    intro n location afterSourcePlace placePoint placeFrame placeDone placePost residual residualBound
    obtain ⟨expressionSource, childTyping, childRoots, _, _, _⟩ := ready n location afterSourcePlace placeDone
    have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
      rw [childTyping, childRoots]
      exact metadata
    obtain ⟨oldType, oldValue, oldRead⟩ := assignOpReadInt source placeDone
    have addressCell := placePost.has (address, .val (.ref location)) (by simp)
    have loadBase := Post.init placePost.rel placePost.pp
    have loadReflection : ReflectAtFuel residual cx placePoint placeFrame
        (fun _ => readLoc location >>= expectInt)
        (fun pair _ pt' fr' =>
          Post cfg env cx afterPlaceBuilder placeFrame afterLoadBuilder fr' pt'
            [(old, .val (.int pair.1 pair.2))]) afterSourcePlace := by
      cases residual with
      | zero => exact ReflectAtFuel.zero cx placePoint placeFrame _ _ afterSourcePlace
      | succ remaining =>
        have instruction := (Post.def_leaf loadBase loadRun expressionExtension (.val .unit)).2
        have operationEquality :
            execOp remaining cx placeFrame (.load address) afterSourcePlace =
              ((readLoc location >>= expectInt) >>= fun pair =>
                pure (.val (.int pair.1 pair.2))) afterSourcePlace := by
          simp only [execOp,execPure,getVal_of addressCell,Goose.Core.expectRef,
            bind_apply,oldRead,expectInt,pure_apply]
        have operation : ReflectMFuel remaining
            (fun n => (readLoc location >>= expectInt) >>= fun pair =>
              pure (.val (.int pair.1 pair.2)))
            (fun n => execOp n cx placeFrame (.load address)) afterSourcePlace :=
          ReflectMFuel.of_eq (sourceFuel := 0) operationEquality
        exact (ReflectAtFuel.def_step (fun pair => .val (.int pair.1 pair.2)) instruction operation).mono
          (by
            intro pair final point' frame' matched
            rcases matched with ⟨rfl, rfl⟩
            exact (Post.def_leaf loadBase loadRun expressionExtension (.val (.int pair.1 pair.2))).1)
    have readAndPlace : ReflectAtFuel residual cx placePoint placeFrame
        (fun _ => readLoc location >>= expectInt)
        (fun pair _ point' frame' =>
          Post cfg env cx ls fr afterLoadBuilder frame' point'
            [(address, .val (.ref location)), (old, .val (.int pair.1 pair.2))]) afterSourcePlace := by
      exact ReflectAtFuel.mono loadReflection (by
        intro pair final point' frame' post
        exact placePost.comp post)
    have remainingReflection : ReflectAtFuel residual cx placePoint placeFrame
        (fun n => (readLoc location >>= expectInt) >>= fun oldInteger =>
          evalExpr n cfg env expression >>= assignOpUpdate cfg operation origin location
            oldInteger.1 oldInteger.2)
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') afterSourcePlace := by
      refine readAndPlace.bind ?_
        (fun n k bound => MonoM.refl (readLoc location >>= expectInt))
        (fun oldInteger n k bound =>
          MonoM.bind ((monoAll n k bound).expr cfg env expression) (fun rightValue =>
            MonoM.refl (assignOpUpdate cfg operation origin location oldInteger.1 oldInteger.2 rightValue)))
      intro readFuel oldInteger next readPoint readFrame readDone readPost remaining remainingBound
      have readValues : oldInteger = (oldType, oldValue) ∧ next = afterSourcePlace := by
        simp only [bind_apply, oldRead, expectInt] at readDone
        cases readDone
        exact ⟨rfl, rfl⟩
      obtain ⟨pairEq,stateEq⟩ := readValues
      subst oldInteger
      subst next
      obtain ⟨rightSource, rightTyping, rightRoots, _, _⟩ := ready n location afterSourcePlace placeDone
      have rightMetadata : SourceResults rightSource.typingEnv rightSource.rootsEnv results := by
        rw [rightTyping, rightRoots]
        exact metadata
      have rightReflection := expressionChild remaining (Nat.le_trans remainingBound residualBound)
        env afterSourcePlace rightSource rightMetadata afterLoadBuilder afterExpressionBuilder right
        readPoint cx readFrame expressionRun readPost.pp operationExtension readPost.rel
        moduleEq resultsEq (placeGenerated.emitDef (.load address) loadRun)
      let binaryAction : Val → M Val := fun rightValue => do
        let (rightType, rightInteger) ← expectInt rightValue
        expectSameTy oldType rightType
        match evalBin cfg.profile operation oldType oldValue rightInteger with
        | .ok value => pure (.int oldType value)
        | .error kind => abortAt (AbortKind.ofNum kind) origin
      have rightThenUpdate : ReflectAtFuel remaining cx readPoint readFrame
          (fun j => evalExpr j cfg env expression >>=
            assignOpUpdate cfg operation origin location oldType oldValue)
          (fun flow _ point' frame' =>
            StatementLoopPost cfg env cx ls fr after loop flow point' frame') afterSourcePlace := by
        refine rightReflection.bind ?_
          (fun j k bound => (monoAll j k bound).expr cfg env expression)
          (fun rightValue j k bound =>
            MonoM.refl (assignOpUpdate cfg operation origin location oldType oldValue rightValue))
        intro j rightValue afterRight rightPoint rightFrame rightDone rightPost operationFuel operationBound
        have beforeOperation := readPost.comp rightPost
        have oldCell := beforeOperation.has (old, .val (.int oldType oldValue)) (by simp)
        have rightCell := beforeOperation.has (right, .val rightValue) (by simp)
        have binaryEquality : execPure cx rightFrame
            (.bin operation operationType old right (some origin)) =
              binaryAction rightValue >>= fun value => pure (.val value) := by
          simp only [execPure,getVal_of oldCell,getVal_of rightCell,expectInt,pure_bind,
            binaryAction,bind_assoc,beforeOperation.rel.prof]
          congr 1
          funext pair
          congr 1
          funext ignored
          cases evalBin cfg.profile operation oldType oldValue pair.2 <;> rfl
        let operationBase := Post.init beforeOperation.rel beforeOperation.pp
        have operationReflection : ReflectAtFuel operationFuel cx rightPoint rightFrame
            (fun _ => binaryAction rightValue)
            (fun value _ point' frame' =>
              Post cfg env cx afterExpressionBuilder rightFrame afterOperationBuilder frame' point'
                [(result, .val value)]) afterRight := by
          exact leaf_def_reflectAtFuel operationBase operationRun storeExtension
            (by intro callee arguments callOrigin impossible; cases impossible)
            (fun value => .val value) (sourceFuel := 0) binaryEquality
        have binaryThenStore : ReflectAtFuel operationFuel cx rightPoint rightFrame
            (fun j => binaryAction rightValue >>= fun value =>
              writeLoc location value >>= fun _ => pure (Flow.normal .unit))
            (fun flow _ point' frame' =>
              StatementLoopPost cfg env cx ls fr after loop flow point' frame') afterRight := by
          refine operationReflection.bind ?_
            (fun j k bound => MonoM.refl (binaryAction rightValue))
            (fun value j k bound => MonoM.refl _)
          intro j value afterOperation pointAfterOperation frameAfterOperation operationDone operationPost
            effectFuel effectBound
          have allOperations := beforeOperation.comp operationPost
          have addressAfterOperation := allOperations.has (address, .val (.ref location)) (by simp)
          have resultAfterOperation := allOperations.has (result, .val value) (by simp)
          have storeEquality : execEff cx.fn frameAfterOperation (.store address result (some origin)) =
              writeLoc location value >>= fun _ => pure frameAfterOperation := by
            simp only [execEff, getVal_of addressAfterOperation, getVal_of resultAfterOperation,
              Goose.Core.expectRef, pure_bind]
          exact typedWriteEffectReflection (sourceFuel := 0) allOperations storeRun extension storeEquality
        have updateEqual : assignOpUpdate cfg operation origin location oldType oldValue rightValue
            afterRight =
              (binaryAction rightValue >>= fun value =>
                writeLoc location value >>= fun _ => pure (Flow.normal .unit)) afterRight := by
          apply congrFun
          simp only [assignOpUpdate,binaryAction,bind_assoc]
          congr 1
          funext pair
          congr 1
          funext ignored
          cases evalBin cfg.profile operation oldType oldValue pair.2 <;> rfl
        exact binaryThenStore.of_source (fun k => ⟨k, updateEqual⟩)
      exact rightThenUpdate
    exact remainingReflection
  have composition : ReflectAtFuel fuel cx pt fr sourceAction
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    simpa only [sourceAction, bind_assoc] using compositionGrouped
  have sourceRun (n : Nat) : execStmt (n + 1) cfg env (.assignOp operation place expression origin) = sourceAction n := by
    unfold sourceAction assignOpUpdate
    simp only [execStmt]
    congr 1
  exact composition.of_source (fun n => ⟨n + 1, by
    have prepared :
        (execStmt (n + 1) cfg env (.assignOp operation place expression origin) >>=
          prepareLoopFlow env loop) state = sourceAction n state := by
      rw [sourceRun n]
      exact congrFun (prepareLoopFlow_normal_only env loop (sourceAction n) (by
        intro sourceState flow final run
        exact assignOpSource_normal (by simpa only [sourceAction] using run))) state
    exact prepared⟩)

end Goose.Lower
