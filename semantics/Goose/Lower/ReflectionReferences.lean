import Goose.Lower.ReflectionSources
import Goose.Lower.ReflectionPlaces

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel
open Goose.Core.Sound

def TypedArgReflection (fuel : Nat) (cfg : Cfg) (results : List Ty) (arg : Arg) : Prop :=
  ∀ (env : Env) (state : St) (source : ArgSource cfg env state arg),
    source.resultsMatch results →
    ∀ (ls after : LS) (id : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerArg arg (lowerEnv cfg.mod env.vars results) ls = (id,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    ReflectAtFuel fuel cx pt fr (fun n => evalArg n cfg env arg)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state

def TypedArgsReflection (fuel : Nat) (cfg : Cfg) (results : List Ty) (args : List Arg) : Prop :=
  ∀ (env : Env) (state : St) (sources : ∀ n, ArgsSource n cfg env args state),
    (∀ n, (sources n).resultsMatch results) →
    ∀ (ls after : LS) (ids : List ValueId) (pt : Pt) (cx : FnCtx) (fr : Frame),
    lowerArgs args (lowerEnv cfg.mod env.vars results) ls = (ids,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    ReflectAtFuel fuel cx pt fr (fun n => mapList (evalArg n cfg env) args)
      (fun values _ pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr after fr' pt' (cellsOf ids values)) state

theorem typedExprReflection_read {fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (child : TypedPlaceReflection fuel cfg results place) :
    TypedExprReflection fuel cfg results (.read place) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨placeSource, typing, roots, _⟩ := source.readChild
  have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, readRun⟩ := lowering
  rcases readRun with ⟨value, afterLoad, load, unitResult, afterRecord, record, returned⟩
  cases unitResult
  rw [pure_run] at returned
  rcases Prod.mk.inj returned with ⟨rfl, rfl⟩
  have recordAdvance : afterLoad.Adv afterRecord :=
    advB_recordReadValueRootRecipe value place (lowerEnv cfg.mod env.vars results)
      afterLoad () afterRecord record
  have extensionAfterLoad : ExtT afterLoad cx.fn.blocks := extension.of_adv recordAdvance
  have middleExtension : ExtT middle cx.fn.blocks :=
    extension.of_adv ((adv_emitDef load).trans recordAdvance)
  have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun point
    middleExtension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= readLoc)
      (fun readValue _ pt' fr' =>
        Post cfg env cx ls fr afterRecord fr' pt' [(value,.val readValue)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
      (fun _ _ _ _ => MonoM.refl _)
    intro n location next pt' fr' done post residual bound
    have cell := post.has (address,.val (.ref location)) (by simp)
    have loadReflection : ReflectAtFuel residual cx pt' fr'
        (fun _ => readLoc location)
        (fun readValue _ point'' frame'' =>
          Post cfg env cx ls fr afterLoad frame'' point'' [(value,.val readValue)]) next := by
      exact leaf_def_reflectAtFuel post load extensionAfterLoad
        (by intro f args org h; cases h) RVal.val (sourceFuel := 0) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
    exact ReflectAtFuel.mono loadReflection (by
      intro readValue final point'' frame'' postAfterLoad
      exact Post.recordReadValueRootRecipe postAfterLoad record)
  exact composition.of_source (fun n => ⟨n + 1, by simp only [evalExpr]⟩)

theorem typedExprReflection_ref {fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (mutability : Mutability) (child : TypedPlaceReflection fuel cfg results place) :
    TypedExprReflection fuel cfg results (.ref mutability place) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨placeSource, typing, roots⟩ := source.refChild mutability
  have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, freeze⟩ := lowering
  rcases borrowTo_ref_cases freeze with ⟨rfl,rfl⟩ | definition | definition
  · have first := child env state placeSource placeMetadata ls after resultId pt cx fr placeRun
      point extension rel moduleEq resultsEq generated
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => evalPlace n cfg env place >>= fun location => pure (.ref location))
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
        (fun _ _ _ _ => MonoM.refl _)
      intro n location next pt' fr' done post residual bound
      exact ReflectAtFuel.ret residual post
    exact composition.of_source (fun n => ⟨n + 1, by simp only [evalExpr]⟩)
  · have middleExtension := extension.of_adv (adv_emitDef definition)
    have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun
      point middleExtension rel moduleEq resultsEq generated
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => evalPlace n cfg env place >>= fun location => pure (.ref location))
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
        (fun _ _ _ _ => MonoM.refl _)
      intro n location next pt' fr' done post residual bound
      have cell := post.has (address,.val (.ref location)) (by simp)
      exact leaf_def_reflectAtFuel post definition extension (by intro f args org h; cases h)
        RVal.val (sourceFuel := 0) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
    exact composition.of_source (fun n => ⟨n + 1, by simp only [evalExpr]⟩)

  · have middleExtension := extension.of_adv (adv_emitDef definition)
    have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun
      point middleExtension rel moduleEq resultsEq generated
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => evalPlace n cfg env place >>= fun location => pure (.ref location))
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
        (fun _ _ _ _ => MonoM.refl _)
      intro n location next pt' fr' done post residual bound
      have cell := post.has (address,.val (.ref location)) (by simp)
      exact leaf_def_reflectAtFuel post definition extension (by intro f args org h; cases h)
        RVal.val (sourceFuel := 0) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
    exact composition.of_source (fun n => ⟨n + 1, by simp only [evalExpr]⟩)

theorem typedExprReflection_len {fuel : Nat} {cfg : Cfg} {results : List Ty} {view : View}
    (child : TypedViewReflection fuel cfg results view) :
    TypedExprReflection fuel cfg results (.len view) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨viewSource, typing, roots⟩ := source.lenChild
  have viewMetadata : SourceResults viewSource.typingEnv viewSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨viewId, middle, viewRun, definition⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef definition)
  have first := child env state viewSource viewMetadata ls middle viewId pt cx fr viewRun point
    middleExtension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalView n cfg env view >>= fun value => pure (.int .i64 value.len))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).view cfg env view)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' done post residual bound
    have cell := post.has (viewId,.view value) (by simp)
    exact leaf_def_reflectAtFuel post definition extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) (by simp only [execPure, getView_of cell, pure_bind])
  exact composition.of_source (fun n => ⟨n + 1, by simp only [evalExpr]⟩)

theorem typedExprReflection_slice {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {view : View} {low high : Bound} {mutability : Mutability} {origin : OriginId}
    (viewChild : TypedViewReflection fuel cfg results view)
    (lowChild : ∀ residual, residual ≤ fuel → TypedBoundReflection residual cfg results low)
    (highChild : ∀ residual, residual ≤ fuel → TypedBoundReflection residual cfg results high) :
    TypedExprReflection fuel cfg results (.slice mutability view low high origin) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨viewSource, viewTyping, viewRoots, next⟩ := source.sliceChildren mutability origin
  have viewMetadata : SourceResults viewSource.typingEnv viewSource.rootsEnv results := by
    rw [viewTyping, viewRoots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨viewId, first, viewRun, lowBnd, second, lowRun, highBnd, third, highRun, definition⟩ := lowering
  have thirdExtension := extension.of_adv (adv_emitDef definition)
  have secondExtension := thirdExtension.of_adv (advB_lowerBound high _ _ _ _ highRun)
  have firstExtension := secondExtension.of_adv (advB_lowerBound low _ _ _ _ lowRun)
  have viewReflection := viewChild env state viewSource viewMetadata ls first viewId pt cx fr viewRun
    point firstExtension rel moduleEq resultsEq generated
  have firstGenerated := generated.lowerView view viewRun
  let sliceFinish : ViewVal → Int → Int → M Val := fun sampled lower upper =>
    if 0 ≤ lower ∧ lower ≤ upper ∧ upper ≤ (sampled.len : Int) then
      pure (.slice sampled.loc (sampled.start + lower.toNat) (upper - lower).toNat)
    else abortAt .sliceOob origin
  let sliceBounds : ViewVal → Nat → M Val := fun sampled n => do
    let lower ← evalBound n cfg env sampled.len 0 low
    let upper ← evalBound n cfg env sampled.len sampled.len high
    sliceFinish sampled lower upper
  have sliceBoundsMonotone : ∀ sampled, FuelMonotone (sliceBounds sampled) := by
    intro sampled n k bound
    exact MonoM.bind ((monoAll n k bound).bound cfg env sampled.len 0 low) fun lower =>
      MonoM.bind ((monoAll n k bound).bound cfg env sampled.len sampled.len high) fun upper =>
        MonoM.refl (sliceFinish sampled lower upper)
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalView n cfg env view >>= fun sampled => sliceBounds sampled n)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine viewReflection.bind ?_ (fun n k bound => (monoAll n k bound).view cfg env view)
      sliceBoundsMonotone
    intro n sampled nextState pt' fr' viewDone viewPost residual residualBound
    obtain ⟨lowerSource, lowerTyping, lowerRoots, upperSources⟩ :=
      next n sampled nextState viewDone
    have lowerMetadata : SourceResults lowerSource.typingEnv lowerSource.rootsEnv results := by
      rw [lowerTyping, lowerRoots]
      exact metadata
    have firstBounds := (lowChild residual residualBound) env nextState lowerSource lowerMetadata
      first second lowBnd pt' cx fr' sampled.len 0 lowRun viewPost.pp secondExtension
      viewPost.rel moduleEq resultsEq firstGenerated
    have boundsComposition : ReflectAtFuel residual cx pt' fr'
        (fun k => evalBound k cfg env sampled.len 0 low >>= fun lower =>
          evalBound k cfg env sampled.len sampled.len high >>= fun upper =>
            sliceFinish sampled lower upper)
        (fun value _ pt'' fr'' =>
          Post cfg env cx ls fr after fr'' pt'' [(resultId,.val value)]) nextState := by
      refine firstBounds.bind ?_ (fun k j bound =>
        (monoAll k j bound).bound cfg env sampled.len 0 low) ?_
      · intro k lower lowerAfter pt'' fr'' lowerDone lowerPost remaining remainingBound
        obtain ⟨upperSource, upperTyping, upperRoots⟩ :=
          upperSources k lower lowerAfter lowerDone
        obtain ⟨lowCells, lowSpec, lowPostState⟩ := lowerPost
        have upperMetadata : SourceResults upperSource.typingEnv upperSource.rootsEnv results := by
          rw [upperTyping, upperRoots]
          exact metadata
        have secondGenerated := firstGenerated.lowerBound low lowRun
        have secondBounds := (highChild remaining (Nat.le_trans remainingBound residualBound))
          env lowerAfter upperSource upperMetadata second third highBnd pt'' cx fr'' sampled.len
          sampled.len highRun lowPostState.pp thirdExtension lowPostState.rel moduleEq resultsEq
          secondGenerated
        refine secondBounds.bind ?_ (fun k j bound =>
          (monoAll k j bound).bound cfg env sampled.len sampled.len high)
          (fun _ _ _ _ => MonoM.refl _)
        intro j upper final pt''' fr''' upperDone ⟨highCells, highSpec, highPost⟩ remaining' remainingBound'
        have combined := (viewPost.comp lowPostState).comp highPost
        have sampledCell := combined.has (viewId,.view sampled) (by simp)
        have lowCell : ∀ cell ∈ lowCells, fr'''.vals[cell.1]? = some cell.2 := by
          intro cell member
          exact combined.has cell (by simp [member])
        have highCell : ∀ cell ∈ highCells, fr'''.vals[cell.1]? = some cell.2 := by
          intro cell member
          exact combined.has cell (by simp [member])
        have lowerEval := evalBnd_of_spec lowSpec lowCell
        have upperEval := evalBnd_of_spec highSpec highCell
        exact leaf_def_reflectAtFuel combined definition extension
          (by intro f args org h; cases h) RVal.val (sourceFuel := 0) (by
            simp only [execPure, getView_of sampledCell, lowerEval, upperEval,
              sliceFinish, pure_bind]
            by_cases inBounds : 0 ≤ lower ∧ lower ≤ upper ∧ upper ≤ (sampled.len : Int)
            · simp [inBounds]
            · simp [inBounds, abortAtOrg, abortAt]
              rfl)
      · intro lower k j bound
        exact ((monoAll k j bound).bound cfg env sampled.len sampled.len high).bind
          (fun _ => MonoM.refl _)
    exact boundsComposition
  exact composition.of_source (fun n => ⟨n + 1, by simp only [evalExpr, sliceBounds, sliceFinish]⟩)

theorem typedArgReflection_byVal {fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (child : TypedExprReflection fuel cfg results expression) :
    TypedArgReflection fuel cfg results (.byVal expression) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  cases source with
  | byVal expressionSource =>
    simp only [lowerArg] at lowering
    have reflected := child env state expressionSource metadata ls after id pt cx fr lowering point
      extension rel moduleEq resultsEq generated
    exact reflected.of_source (fun n => ⟨n + 1, by simp only [evalArg]⟩)

theorem typedArgReflection_byRef {fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (mutability : Mutability) (child : TypedPlaceReflection fuel cfg results place) :
    TypedArgReflection fuel cfg results (.byRef mutability place) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  cases source with
  | byRef _ placeSource target =>
    have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := metadata
    simp only [lowerArg, bind_eq] at lowering
    obtain ⟨address, middle, placeRun, freeze⟩ := lowering
    rcases borrowTo_ref_cases freeze with ⟨rfl,rfl⟩ | definition | definition
    · have first := child env state placeSource placeMetadata ls after resultId pt cx fr placeRun
        point extension rel moduleEq resultsEq generated
      have composition : ReflectAtFuel fuel cx pt fr
          (fun n => evalPlace n cfg env place >>= fun location => pure (.ref location))
          (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
        refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
          (fun _ _ _ _ => MonoM.refl _)
        intro n location next pt' fr' done post residual bound
        exact ReflectAtFuel.ret residual post
      exact composition.of_source (fun n => ⟨n + 1, by simp only [evalArg]⟩)
    · have middleExtension := extension.of_adv (adv_emitDef definition)
      have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun
        point middleExtension rel moduleEq resultsEq generated
      have composition : ReflectAtFuel fuel cx pt fr
          (fun n => evalPlace n cfg env place >>= fun location => pure (.ref location))
          (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
        refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
          (fun _ _ _ _ => MonoM.refl _)
        intro n location next pt' fr' done post residual bound
        have cell := post.has (address,.val (.ref location)) (by simp)
        exact leaf_def_reflectAtFuel post definition extension (by intro f args org h; cases h)
          RVal.val (sourceFuel := 0) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
      exact composition.of_source (fun n => ⟨n + 1, by simp only [evalArg]⟩)

    · have middleExtension := extension.of_adv (adv_emitDef definition)
      have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun
        point middleExtension rel moduleEq resultsEq generated
      have composition : ReflectAtFuel fuel cx pt fr
          (fun n => evalPlace n cfg env place >>= fun location => pure (.ref location))
          (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
        refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
          (fun _ _ _ _ => MonoM.refl _)
        intro n location next pt' fr' done post residual bound
        have cell := post.has (address,.val (.ref location)) (by simp)
        exact leaf_def_reflectAtFuel post definition extension (by intro f args org h; cases h)
          RVal.val (sourceFuel := 0) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
      exact composition.of_source (fun n => ⟨n + 1, by simp only [evalArg]⟩)

def TypedArgChildrenReflection (fuel : Nat) (cfg : Cfg) (results : List Ty)
    (arguments : List Arg) : Prop :=
  ∀ residual, residual ≤ fuel → ∀ argument, argument ∈ arguments →
    TypedArgReflection residual cfg results argument

theorem typedArgsReflection_of_children {fuel : Nat} {cfg : Cfg} {results : List Ty} :
    ∀ (arguments : List Arg), TypedArgChildrenReflection fuel cfg results arguments →
      TypedArgsReflection fuel cfg results arguments := by
  intro arguments
  induction arguments generalizing fuel with
  | nil =>
    intro children env state sources sourceMetadata ls after ids pt cx fr lowering point extension
      rel moduleEq resultsEq generated
    simp only [lowerArgs, pure_run] at lowering
    obtain ⟨idsEq, afterEq⟩ := Prod.mk.inj lowering
    subst ids
    subst after
    change ReflectAtFuel fuel cx pt fr (fun _ => pure ([] : List Val))
      (fun (values : List Val) _ pt' fr' =>
        ([] : List ValueId).length = values.length ∧
          Post cfg env cx ls fr ls fr' pt' (cellsOf [] values)) state
    exact ReflectAtFuel.ret fuel (value := ([] : List Val))
      ⟨rfl, by simpa [cellsOf] using Post.init rel point⟩
  | cons argument rest induction =>
    intro children env state sources sourceMetadata ls after ids pt cx fr lowering point extension
      rel moduleEq resultsEq generated
    simp only [lowerArgs, bind_eq] at lowering
    obtain ⟨id, middle, headRun, tailIds, after, tailRun, finish⟩ := lowering
    rw [pure_run] at finish
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj finish
    have middleExtension : ExtT middle cx.fn.blocks :=
      extension.of_adv (advB_lowerArgs rest _ _ _ _ tailRun)
    cases sourceAt : sources fuel with
    | cons head tail =>
      have sourceAtMetadata : (sources fuel).resultsMatch results := sourceMetadata fuel
      rw [sourceAt] at sourceAtMetadata
      have headMetadata : head.resultsMatch results := by
        simpa only [ArgsSource.resultsMatch] using sourceAtMetadata.1
      have headReflection := children fuel (Nat.le_refl _) argument (by simp) env state head
        headMetadata ls middle id pt cx fr headRun point middleExtension rel moduleEq resultsEq generated
      let tailSource : Val → Nat → M (List Val) := fun value n => do
        let values ← mapList (evalArg n cfg env) rest
        pure (value :: values)
      have tailSourceMonotone : ∀ value, FuelMonotone (tailSource value) := by
        intro value n k bound
        exact MonoM.bind (MonoM.mapList (fun child => (monoAll n k bound).arg cfg env child) rest)
          (fun values => MonoM.refl (pure (value :: values)))
      have composition : ReflectAtFuel fuel cx pt fr
          (fun n => mapList (evalArg n cfg env) (argument :: rest))
          (fun values _ pt' fr' => (id :: tailIds).length = values.length ∧
            Post cfg env cx ls fr after fr' pt' (cellsOf (id :: tailIds) values)) state := by
        refine headReflection.bind ?_ (fun n k bound => (monoAll n k bound).arg cfg env argument)
          tailSourceMonotone
        intro n value nextState pt' fr' headDone headPost residual residualBound
        let tailSources : ∀ k, ArgsSource k cfg env rest nextState := fun k =>
          ArgsSource.afterHead sources headDone k
        have tailMetadata : ∀ k, (tailSources k).resultsMatch results := fun k =>
          ArgsSource.afterHead_resultsMatch sources sourceMetadata headDone k
        have tailChildren : TypedArgChildrenReflection residual cfg results rest := by
          intro remaining remainingBound child member
          exact children remaining (Nat.le_trans remainingBound residualBound) child
            (by simp [member])
        have tailReflection := induction tailChildren env nextState tailSources tailMetadata
          middle after tailIds pt' cx fr' tailRun headPost.pp extension headPost.rel moduleEq
          resultsEq (generated.lowerArg argument headRun)
        have sourceWithHead : ReflectAtFuel residual cx pt' fr' (tailSource value)
            (fun values _ pt'' fr'' => (id :: tailIds).length = values.length ∧
              Post cfg env cx ls fr after fr'' pt'' (cellsOf (id :: tailIds) values)) nextState := by
          refine tailReflection.bind ?_
            (fun n k bound => MonoM.mapList (fun child => (monoAll n k bound).arg cfg env child) rest)
            (fun values n k bound => MonoM.refl (pure (value :: values)))
          intro k values final pt'' fr'' tailDone ⟨tailLength, tailPost⟩ remaining remainingBound
          exact ReflectAtFuel.ret remaining ⟨by simp [tailLength], by
            simpa [cellsOf] using headPost.comp tailPost⟩
        exact sourceWithHead
      exact composition.of_source (fun n => ⟨n, by simp only [mapList]⟩)

end Goose.Lower
