import Goose.Lower.ReflectionTyped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel
open Goose.Core.Sound

def TypedPlaceReflection (fuel : Nat) (cfg : Cfg) (results : List Ty) (place : Place) : Prop :=
  ∀ (env : Env) (state : St) (source : PlaceSource cfg env place state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls after : LS) (id : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerPlace place (lowerEnv cfg.mod env.vars results) ls = (id,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    ReflectAtFuel fuel cx pt fr (fun n => evalPlace n cfg env place)
      (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state

def TypedViewReflection (fuel : Nat) (cfg : Cfg) (results : List Ty) (view : View) : Prop :=
  ∀ (env : Env) (state : St) (source : ViewSource cfg env view state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls after : LS) (id : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerView view (lowerEnv cfg.mod env.vars results) ls = (id,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    ReflectAtFuel fuel cx pt fr (fun n => evalView n cfg env view)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.view value)]) state

def TypedBoundReflection (fuel : Nat) (cfg : Cfg) (results : List Ty) (bound : Bound) : Prop :=
  ∀ (env : Env) (state : St) (source : BoundSource cfg env bound state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls after : LS) (bnd : Bnd) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
      (length : Nat) (default : Int),
    lowerBound bound (lowerEnv cfg.mod env.vars results) ls = (bnd,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    ReflectAtFuel fuel cx pt fr (fun n => evalBound n cfg env length default bound)
      (fun value _ pt' fr' => ∃ cells, BndSpec length default bnd value cells ∧
        Post cfg env cx ls fr after fr' pt' cells) state

theorem TypedPlaceReflection.of_untyped {fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (reflection : PlaceReflection fuel place) : TypedPlaceReflection fuel cfg results place := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact reflection cfg env cx (lowerEnv cfg.mod env.vars results) ls after fr pt id state
    rel point lowering extension

theorem TypedViewReflection.of_untyped {fuel : Nat} {cfg : Cfg} {results : List Ty} {view : View}
    (reflection : ViewReflection fuel view) : TypedViewReflection fuel cfg results view := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact reflection cfg env cx (lowerEnv cfg.mod env.vars results) ls after fr pt id state
    rel point lowering extension

theorem typedPlaceReflection_var (fuel : Nat) (cfg : Cfg) (results : List Ty) (id : VarId) :
    TypedPlaceReflection fuel cfg results (.var id) :=
  TypedPlaceReflection.of_untyped (placeReflection_var fuel id)

theorem typedPlaceReflection_global (fuel : Nat) (cfg : Cfg) (results : List Ty) (id : GlobalId) :
    TypedPlaceReflection fuel cfg results (.global id) :=
  TypedPlaceReflection.of_untyped (placeReflection_global fuel id)

theorem typedPlaceReflection_deref {fuel : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (child : TypedExprReflection fuel cfg results expr) :
    TypedPlaceReflection fuel cfg results (.deref expr) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  cases hslice : sliceRefTy source.typingEnv expr with
  | none =>
    obtain ⟨childSource, typing, roots, mutability, target, type⟩ := source.derefChild hslice
    have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
      rw [typing, roots]
      exact metadata
    simp only [lowerPlace] at lowering
    have first := child env state childSource childMetadata ls after id pt cx fr lowering
      point extension rel moduleEq resultsEq generated
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => evalExpr n cfg env expr >>= expectRef)
        (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expr)
        (fun value n k bound => MonoM.refl (expectRef value))
      intro n value next pt' fr' done post residual bound
      have typed := (childSource.result n value done).typed
      rw [type] at typed
      obtain ⟨location,rfl,_⟩ := typed
      exact ReflectAtFuel.ret residual post
    exact composition.of_source fun n => ⟨n + 1, by simp only [evalPlace]⟩
  | some ty =>
    obtain ⟨varId, localDecl, mutability, sliceMutability, element, rfl, visible, variableProof,
      type, flat, sameTy⟩ := Core.Sound.sliceRefTy_some hslice
    have future : varId ∈ source.context.inputFuture := by
      cases source.context <;>
        simp [EvaluationContext.inputFuture, NodeContext.inputFuture,
          DemandNode.variables, Place.variables, Expr.variables]
    have sourceReference : ∀ n,
        Core.Sound.Sat (evalExpr n cfg env (.read (.var varId))) state
          (fun value _ => ∃ location, value = .ref location) := by
      intro n
      apply Core.Sound.sat_read_var source.frame visible future n
      intro actual scopeInst value varLookup scopeRun rootRun typed
      rw [source.frame.vars_t, varLookup] at variableProof
      cases variableProof
      rw [type] at typed
      obtain ⟨location,rfl,_⟩ := typed
      exact ⟨location,rfl⟩
    simp only [lowerPlace] at lowering
    have reflected : ExprReflection fuel (.read (.var varId)) :=
      exprReflection_read (placeReflection_var fuel varId)
    have first := reflected cfg env cx (lowerEnv cfg.mod env.vars results) ls after fr pt id state
      rel point lowering extension
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => evalExpr n cfg env (.read (.var varId)) >>= expectRef)
        (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env (.read (.var varId)))
        (fun value n k bound => MonoM.refl (expectRef value))
      intro n value next pt' fr' done post residual bound
      have known := sourceReference n
      unfold Core.Sound.Sat at known
      rw [done] at known
      obtain ⟨location,rfl⟩ := known
      exact ReflectAtFuel.ret residual post
    exact composition.of_source fun n => ⟨n + 1, by simp only [evalPlace]⟩

theorem typedPlaceReflection_field {fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (child : TypedPlaceReflection fuel cfg results place) (index : Nat) :
    TypedPlaceReflection fuel cfg results (.field place index) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots⟩ := source.fieldChild index
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerPlace, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, fieldRun⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef fieldRun)
  have first := child env state childSource childMetadata ls middle address pt cx fr placeRun
    point middleExtension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= fun location => pure { location with path := location.path ++ [index] })
      (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
      (fun location n k bound => by
        change MonoM (pure { location with path := location.path ++ [index] })
          (pure { location with path := location.path ++ [index] })
        exact MonoM.refl _)
    intro n location next pt' fr' done post residual bound
    have cell := post.has (address,.val (.ref location)) (by simp)
    refine leaf_def_reflectAtFuel post fieldRun extension (by intro f args org h; cases h)
      (fun location => RVal.val (.ref location)) (sourceFuel := 0) ?_
    simp only [execPure, getVal_of cell, expectRef, pure_bind]
  exact composition.of_source fun n => ⟨n + 1, by simp only [evalPlace]⟩

theorem typedPlaceReflection_elem {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {view : View} {index : Expr} (viewChild : TypedViewReflection fuel cfg results view)
    (indexChild : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results index)
    (origin : OriginId) :
    TypedPlaceReflection fuel cfg results (.elem view index origin) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨intTy, viewSource, viewTyping, viewRoots, next⟩ := source.elemChildren origin
  have viewMetadata : SourceResults viewSource.typingEnv viewSource.rootsEnv results := by
    rw [viewTyping, viewRoots]
    exact metadata
  simp only [lowerPlace, bind_eq] at lowering
  obtain ⟨viewId, firstLs, viewRun, indexId, middle, indexRun, indexChecked⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef indexChecked)
  have firstExtension := middleExtension.of_adv (advB_lowerExpr index _ _ _ _ indexRun)
  have first := viewChild env state viewSource viewMetadata ls firstLs viewId pt cx fr viewRun
    point firstExtension rel moduleEq resultsEq generated
  have middleGenerated := generated.lowerView view viewRun
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalView n cfg env view >>= fun sampled =>
        evalExpr n cfg env index >>= fun value => do
          let (_,integer) ← expectInt value
          if 0 ≤ integer ∧ integer < (sampled.len : Int) then
            pure (Loc.mk sampled.loc.root (sampled.loc.path ++ [sampled.start + integer.toNat]))
          else abortAt .indexOob origin)
      (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).view cfg env view) ?_
    · intro n sampled sampledAfter pt' fr' viewDone post residual bound
      obtain ⟨indexSource,indexTyping,indexRoots,indexType⟩ := next n sampled sampledAfter viewDone
      have indexMetadata : SourceResults indexSource.typingEnv indexSource.rootsEnv results := by
        rw [indexTyping, indexRoots]
        exact metadata
      have second := (indexChild residual bound) env sampledAfter indexSource indexMetadata
        firstLs middle indexId pt' cx fr' indexRun post.pp middleExtension post.rel
        moduleEq resultsEq middleGenerated
      have secondComposition : ReflectAtFuel residual cx pt' fr'
          (fun k => evalExpr k cfg env index >>= fun value => do
            let (_,integer) ← expectInt value
            if 0 ≤ integer ∧ integer < (sampled.len : Int) then
              pure (Loc.mk sampled.loc.root (sampled.loc.path ++ [sampled.start + integer.toNat]))
            else abortAt .indexOob origin)
          (fun location _ pt'' fr'' =>
            Post cfg env cx ls fr after fr'' pt'' [(id,.val (.ref location))]) sampledAfter := by
        refine second.bind ?_ (fun k j bound => (monoAll k j bound).expr cfg env index)
          (fun value k j bound => MonoM.refl
            (do
              let (_,integer) ← expectInt value
              if 0 ≤ integer ∧ integer < (sampled.len : Int) then
                pure (Loc.mk sampled.loc.root (sampled.loc.path ++ [sampled.start + integer.toNat]))
              else abortAt .indexOob origin))
        intro k value final pt'' fr'' indexDone postIndex remaining remainingBound
        have indexTyped := (indexSource.result k value indexDone).typed
        rw [indexType] at indexTyped
        obtain ⟨integer,rfl⟩ := Core.Sound.hasTy_int indexTyped
        have combined := post.comp postIndex
        have sampledCell := combined.has (viewId,.view sampled) (by simp)
        have indexCell := combined.has (indexId,.val (.int intTy integer)) (by simp)
        refine leaf_def_reflectAtFuel combined indexChecked extension
          (by intro f args org h; cases h) (fun location => RVal.val (.ref location))
          (sourceFuel := 0) ?_
        simp only [execPure, getView_of sampledCell, getVal_of indexCell, Core.expectInt,
          pure_bind]
        by_cases inBounds : 0 ≤ integer ∧ integer < (sampled.len : Int)
        · simp [inBounds]
        · simp [inBounds, abortAtOrg, abortAt]
          rfl
      exact secondComposition
    · intro sampled n k bound
      exact ((monoAll n k bound).expr cfg env index).bind
        (fun _ => MonoM.refl _)
  exact composition.of_source fun n => ⟨n + 1, by simp only [evalPlace]⟩

theorem typedViewReflection_of {fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (child : TypedPlaceReflection fuel cfg results place) :
    TypedViewReflection fuel cfg results (.of place) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots⟩ := source.ofChild
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerView, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, viewRun⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef viewRun)
  have first := child env state childSource childMetadata ls middle address pt cx fr placeRun
    point middleExtension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        readLoc location >>= fun value => do
          let (length,resizable) ← expectArray value
          pure ({loc := location, start := 0, len := length, resizable := resizable} : ViewVal))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.view value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
      (fun location n k bound => by
        change MonoM
          (readLoc location >>= fun value => do
            let (length,resizable) ← expectArray value
            pure ({loc := location, start := 0, len := length, resizable := resizable} : ViewVal))
          (readLoc location >>= fun value => do
            let (length,resizable) ← expectArray value
            pure ({loc := location, start := 0, len := length, resizable := resizable} : ViewVal))
        exact MonoM.refl _)
    intro n location next pt' fr' done post residual bound
    have cell := post.has (address,.val (.ref location)) (by simp)
    refine leaf_def_reflectAtFuel post viewRun extension (by intro f args org h; cases h)
      RVal.view (sourceFuel := 0) ?_
    simp only [execPure, getVal_of cell, expectRef, pure_bind, bind_assoc]
  exact composition.of_source fun n => ⟨n + 1, by simp only [evalView]⟩

theorem typedViewReflection_val {fuel : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (child : TypedExprReflection fuel cfg results expr) :
    TypedViewReflection fuel cfg results (.val expr) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots, mutability, type⟩ := source.valChild
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerView, bind_eq] at lowering
  obtain ⟨sliceId, middle, exprRun, viewRun⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef viewRun)
  have first := child env state childSource childMetadata ls middle sliceId pt cx fr exprRun
    point middleExtension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expr >>= fun value => do
        let (location,start,length) ← expectSlice value
        pure ({loc := location, start := start, len := length, resizable := false} : ViewVal))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.view value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expr)
      (fun value n k bound => by
        change MonoM
          (do
            let (location,start,length) ← expectSlice value
            pure ({loc := location, start := start, len := length, resizable := false} : ViewVal))
          (do
            let (location,start,length) ← expectSlice value
            pure ({loc := location, start := start, len := length, resizable := false} : ViewVal))
        exact MonoM.refl _)
    intro n value next pt' fr' done post residual bound
    have cell := post.has (sliceId,.val value) (by simp)
    refine leaf_def_reflectAtFuel post viewRun extension (by intro f args org h; cases h)
      RVal.view (sourceFuel := 0) ?_
    simp only [execPure, getVal_of cell, expectSlice, pure_bind, bind_assoc]
  exact composition.of_source fun n => ⟨n + 1, by simp only [evalView]⟩

theorem typedBoundReflection_expr {fuel : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (child : TypedExprReflection fuel cfg results expr) :
    TypedBoundReflection fuel cfg results (.expr expr) := by
  intro env state source metadata ls after bnd pt cx fr length default lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots, intTy, type⟩ := source.expressionChild false
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerBound, bind_eq] at lowering
  obtain ⟨valueId, middle, exprRun, pureRun⟩ := lowering
  rw [pure_run] at pureRun
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj pureRun
  have first := child env state childSource childMetadata ls middle valueId pt cx fr exprRun
    point extension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expr >>= fun value => do
        let (_,integer) ← expectInt value
        pure integer)
      (fun value _ pt' fr' => ∃ cells, BndSpec length default (.val valueId) value cells ∧
        Post cfg env cx ls fr middle fr' pt' cells) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expr)
      (fun value n k bound => by
        change MonoM (do let (_,integer) ← expectInt value; pure integer)
          (do let (_,integer) ← expectInt value; pure integer)
        exact MonoM.refl _)
    intro n value next pt' fr' done post residual bound
    have typed := (childSource.result n value done).typed
    rw [type] at typed
    obtain ⟨integer,rfl⟩ := Core.Sound.hasTy_int typed
    refine ReflectAtFuel.ret residual ⟨[(valueId,.val (.int intTy integer))], ?_, post⟩
    exact ⟨intTy, by simp⟩
  exact composition.of_source fun n => ⟨n + 1, by simp only [evalBound]⟩

theorem typedBoundReflection_fromEnd {fuel : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (child : TypedExprReflection fuel cfg results expr) :
    TypedBoundReflection fuel cfg results (.fromEnd expr) := by
  intro env state source metadata ls after bnd pt cx fr length default lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots, intTy, type⟩ := source.expressionChild true
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerBound, bind_eq] at lowering
  obtain ⟨valueId, middle, exprRun, pureRun⟩ := lowering
  rw [pure_run] at pureRun
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj pureRun
  have first := child env state childSource childMetadata ls middle valueId pt cx fr exprRun
    point extension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expr >>= fun value => do
        let (_,integer) ← expectInt value
        pure ((length : Int) - integer))
      (fun value _ pt' fr' => ∃ cells, BndSpec length default (.fromEnd valueId) value cells ∧
        Post cfg env cx ls fr middle fr' pt' cells) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expr)
      (fun value n k bound => by
        change MonoM (do let (_,integer) ← expectInt value; pure ((length : Int) - integer))
          (do let (_,integer) ← expectInt value; pure ((length : Int) - integer))
        exact MonoM.refl _)
    intro n value next pt' fr' done post residual bound
    have typed := (childSource.result n value done).typed
    rw [type] at typed
    obtain ⟨integer,rfl⟩ := Core.Sound.hasTy_int typed
    refine ReflectAtFuel.ret residual ⟨[(valueId,.val (.int intTy integer))], ?_, post⟩
    exact ⟨intTy, integer, by simp⟩
  exact composition.of_source fun n => ⟨n + 1, by simp only [evalBound]⟩

theorem typedPlaceReflection_zero (cfg : Cfg) (results : List Ty) (place : Place) :
    TypedPlaceReflection 0 cfg results place := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact ReflectAtFuel.zero cx pt fr _ _ state

theorem typedViewReflection_zero (cfg : Cfg) (results : List Ty) (view : View) :
    TypedViewReflection 0 cfg results view := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact ReflectAtFuel.zero cx pt fr _ _ state

theorem typedBoundReflection_zero (cfg : Cfg) (results : List Ty) (bound : Bound) :
    TypedBoundReflection 0 cfg results bound := by
  intro env state source metadata ls after bnd pt cx fr length default lowering point extension rel moduleEq resultsEq generated
  exact ReflectAtFuel.zero cx pt fr _ _ state

theorem typedBoundReflection_omitted (fuel : Nat) (cfg : Cfg) (results : List Ty) :
    TypedBoundReflection fuel cfg results .omitted := by
  cases fuel with
  | zero => exact typedBoundReflection_zero cfg results .omitted
  | succ fuel =>
    intro env state source metadata ls after bnd pt cx fr length default lowering point extension rel moduleEq resultsEq generated
    simp only [lowerBound, pure_run] at lowering
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj lowering
    have matched : ∃ cells, BndSpec length default Bnd.omitted default cells ∧
        Post cfg env cx ls fr ls fr pt cells := by
      refine ⟨[], ?_, Post.init rel point⟩
      simp [BndSpec]
    exact (ReflectAtFuel.ret (fuel + 1) matched).of_source fun n =>
      ⟨n + 1, by simp [evalBound]⟩

end Goose.Lower
