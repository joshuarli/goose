import Goose.Lower.ReflectionPlaces
import Goose.Lower.DemandRunAtPrefix
import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.DemandGeneratedTransfer

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem PlaceSource.sliceReference_actual {cfg : Cfg} {env : Env} {state : St} {expression : Expr}
    (source : PlaceSource cfg env (.deref expression) state) {ty : Ty}
    (slice : sliceRefTy source.typingEnv expression = some ty) :
    ∃ (slot : VarId) (location : Loc), expression = .read (.var slot) ∧
      evalPlace 3 cfg env (.deref expression) state = .ok location state ∧
      PlaceOk cfg.mod source.world.G source.world.P source.rootsEnv env state.store (.deref expression) location source.ty := by
  obtain ⟨slot, descriptor, outer, mutability, element, expressionEq, visible, variableAt, variableType, flat, typeEq⟩ :=
    sliceRefTy_some slice
  subst expression
  have future : slot ∈ source.context.inputFuture := by
    cases context : source.context <;> simp [context, EvaluationContext.inputFuture,
      NodeContext.inputFuture, DemandNode.variables, Place.variables, Expr.variables]
  obtain ⟨actual, scope, value, found, scopeAt, _, stored, typed⟩ := source.frame.vis slot visible future
  rw [source.frame.vars_t, found] at variableAt
  cases variableAt
  rw [variableType] at typed
  obtain ⟨location, valueEq, referenceTyped⟩ := typed
  subst value
  have evaluated : evalPlace 3 cfg env (.deref (.read (.var slot))) state = .ok location state := by
    simp [evalPlace, evalExpr, rootOf, found, scopeAt, readLoc, read_root stored, bind_apply, pure_apply, expectRef]
  exact ⟨slot, location, rfl, evaluated, (source.result 3 location evaluated).typed⟩

theorem PlaceSource.sliceReference_operandAlias {cfg : Cfg} {env : Env} {state : St} {expression : Expr}
    (source : PlaceSource cfg env (.deref expression) state) {ty : Ty}
    (slice : sliceRefTy source.typingEnv expression = some ty) (path : List Nat) :
    ∃ (location : Loc) (alias : RetainedAlias),
      evalPlace 3 cfg env (.deref expression) state = .ok location state ∧
      source.rootsEnv.access.aliasPlace path (.deref expression) = .ok [alias] ∧
      AliasAt cfg.mod source.world env state.store alias (.ref location) := by
  obtain ⟨slot, descriptor, outer, mutability, element, expressionEq, visible, variableAt, variableType, flat, typeEq⟩ :=
    sliceRefTy_some slice
  subst expression
  have actualType : source.ty = .slice mutability element := by
    have checked := source.typed
    simp only [tyPlace, slice, typeEq, variableType] at checked
    inv at checked
    exact checked.1
  obtain ⟨_, location, _, placed, valid⟩ := source.sliceReference_actual slice
  rw [actualType] at valid
  rcases valid with impossible | impossible | valid
  · simp [Ty.refTarget] at impossible
  · obtain ⟨_, _, _, _, impossible, _⟩ := impossible
    cases impossible
  · obtain ⟨x, lv, mu0, mu, el, ann, eq, lookup, declared, target, isFlat, pathEq, annotation, rooted, present⟩ := valid
    cases eq
    have referenceType : HasTy cfg.mod source.world.G state.store (.ref location) (.ref .mutable (.slice mutability element)) := by
      refine ⟨location, rfl, Or.inr ⟨by simp [Ty.isSlice, flat], pathEq, present⟩⟩
    have accessVariable : source.rootsEnv.impl.vars[slot]? = some descriptor := by
      rw [source.frame.vars_p, ← source.frame.vars_t]
      exact variableAt
    have rawAnn : (source.rootsEnv.ctx.varRoots.find? (·.1 == slot)).map (·.2) = some ann := annotation
    have placeType : source.rootsEnv.access.placeType? (.deref (.read (.var slot))) = some (.slice mutability element) := by
      have lookupType := tyPlace_accessType (source.frame.mod_t.trans source.frame.mod_p.symm)
        (source.frame.vars_t.trans source.frame.vars_p.symm) source.typed
      simpa only [actualType] using lookupType
    let alias : RetainedAlias := ⟨.ref .mutable (.slice mutability element), ann, .operand path⟩
    refine ⟨location, alias, placed, ?_, referenceType, ?_⟩
    · simp only [AccessEnv.aliasPlace, placeType]
      simp [Ty.interiorTarget?, Ty.ownerElem?, AccessEnv.placeRoots,
        AccessEnv.exprRoots, AccessEnv.variableRoots, PEnv.access, accessVariable, variableType, rawAnn,
        Ty.isRefLike, alias, pure, Except.pure]
      rfl
    · intro root targetRoot
      have equal : location.root = root := targetRoot
      simpa [alias, ← equal] using rooted

#print axioms PlaceSource.sliceReference_operandAlias

theorem accepted_generated_slice_reference_address {cfg : Cfg} {env : Env} {state : St} {expression : Expr}
    (source : PlaceSource cfg env (.deref expression) state) {ty : Ty}
    (slice : sliceRefTy source.typingEnv expression = some ty)
    {cx : FnCtx} {results : List Ty} {before : LS} {initial : GIR.Frame} {point : Pt}
    (atPoint : before.pp = some point) (related : Rel cfg env cx initial before)
    (map : RetainedSsaMap) (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, initial, state⟩)
    (extended : ExtT (lowerPlace (.deref expression) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (finalPoint : Pt) (frame : GIR.Frame),
      evalPlace 3 cfg env (.deref expression) state = .ok location state ∧
      DemandRuntimePrefix cx 2 ⟨point, initial, state⟩ ⟨finalPoint, frame, state⟩ ∧
      DemandUniformTraversal cx (DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.inputFuture map.values map.runs) 2 ⟨point, initial, state⟩ ⟨finalPoint, frame, state⟩ ∧
      Post cfg env cx before initial (lowerPlace (.deref expression) (lowerEnv cfg.mod env.vars results) before).2
        frame finalPoint [((lowerPlace (.deref expression) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] := by
  obtain ⟨slot, descriptor, outer, mutability, element, expressionEq, visible, variableAt, variableType, flat, typeEq⟩ :=
    sliceRefTy_some slice
  subst expression
  have future : slot ∈ source.context.inputFuture := by
    cases context : source.context <;> simp [context, EvaluationContext.inputFuture,
      NodeContext.inputFuture, DemandNode.variables, Place.variables, Expr.variables]
  obtain ⟨actual, scope, value, found, scopeAt, _, stored, typed⟩ := source.frame.vis slot visible future
  rw [source.frame.vars_t, found] at variableAt
  cases variableAt
  rw [variableType] at typed
  obtain ⟨location, valueEq, referenceTyped⟩ := typed
  subst value
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace (.var slot) le before
  let loaded := emitDef (.load addressed.1) le addressed.2
  let built := lowerExpr (.read (.var slot)) le before
  have readExtended : ExtT built.2 cx.fn.blocks := by simpa only [built, lowerPlace] using extended
  have loadExtended := generated_read_load_extended readExtended
  have addressExtended : ExtT addressed.2 cx.fn.blocks :=
    loadExtended.of_adv (adv_emitDef (show emitDef (.load addressed.1) le addressed.2 = (loaded.1, loaded.2) from rfl))
  let holder : Loc := ⟨.local env.act scope slot, []⟩
  have addressEmit : emitDef (.slotAddr slot) le before = (addressed.1, addressed.2) := rfl
  obtain ⟨addressPost, addressInstruction⟩ := Post.def_leaf (Post.init related atPoint) addressEmit addressExtended (.val (.ref holder))
  let middleFrame := initial.set addressed.1 (.val (.ref holder))
  have addressStep : ∀ fuel, DemandInstructionStep cx fuel ⟨point, initial, state⟩
      ⟨(point.1, point.2 + 1), middleFrame, state⟩ := by
    intro fuel
    apply DemandInstructionStep.definition addressInstruction
    simp only [execOp, execPure, slotRoot_eq related]
    simp [rootOf, found, scopeAt, holder, bind_apply, pure_apply]
  have addressCell : middleFrame.vals[addressed.1]? = some (.val (.ref holder)) := by
    simpa only [middleFrame] using addressPost.has (addressed.1, .val (.ref holder)) (by simp)
  have loadEmit : emitDef (.load addressed.1) le addressed.2 = (loaded.1, loaded.2) := rfl
  obtain ⟨loadPost, loadInstruction⟩ := Post.def_leaf addressPost loadEmit loadExtended (.val (.ref location))
  have loadStep : ∀ fuel, DemandInstructionStep cx fuel ⟨(point.1, point.2 + 1), middleFrame, state⟩
      ⟨(point.1, point.2 + 2), middleFrame.set loaded.1 (.val (.ref location)), state⟩ := by
    intro fuel
    apply DemandInstructionStep.definition loadInstruction
    simp [execOp, execPure, getVal_of addressCell, expectRef, readLoc, read_root stored, holder, bind_apply, pure_apply, Functor.map, M.bind', M.pure']
  have recordRun : recordReadValueRootRecipe loaded.1 (.var slot) le loaded.2 =
      ((), (recordReadValueRootRecipe loaded.1 (.var slot) le loaded.2).2) := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  have post := Post.recordReadValueRootRecipe loadPost recordRun
  have finalPost : Post cfg env cx before initial built.2 (middleFrame.set loaded.1 (.val (.ref location)))
      (point.1, point.2 + 2) [(built.1, .val (.ref location))] := by
    simpa only [built, lowerExpr_read_run, Nat.add_assoc] using post
  have evaluated : evalPlace 3 cfg env (.deref (.read (.var slot))) state = .ok location state := by
    simp [evalPlace, evalExpr, rootOf, found, scopeAt, readLoc, read_root stored, bind_apply, pure_apply, expectRef]
  have startDemand : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
      source.context.inputFuture map.values map.runs ⟨point, initial, state⟩ :=
    ⟨⟨before, atPoint, related⟩, source.frame, realized⟩
  have middleDemand : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
      source.context.inputFuture map.values map.runs ⟨(point.1, point.2 + 1), middleFrame, state⟩ :=
    ⟨⟨addressed.2, addressPost.pp, addressPost.rel⟩, source.frame,
      realized.retained addressPost.same bounded.1 bounded.2 RetainsAliases.refl⟩
  have endDemand : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
      source.context.inputFuture map.values map.runs
        ⟨(point.1, point.2 + 2), middleFrame.set loaded.1 (.val (.ref location)), state⟩ :=
    ⟨⟨built.2, finalPost.pp, finalPost.rel⟩, source.frame,
      realized.retained finalPost.same bounded.1 bounded.2 RetainsAliases.refl⟩
  refine ⟨location, (point.1, point.2 + 2), middleFrame.set loaded.1 (.val (.ref location)), evaluated, ?_, ?_, ?_⟩
  · exact .next (addressStep 0).runtime (.next (loadStep 0).runtime (.zero _))
  · exact .next startDemand addressStep (.next middleDemand loadStep (.done endDemand))
  · simpa only [lowerPlace, built, lowerExpr_read_run] using finalPost

theorem accepted_generated_slice_reference_retained {cfg : Cfg} {env : Env} {state : St} {expression : Expr}
    (source : PlaceSource cfg env (.deref expression) state) {ty : Ty}
    (slice : sliceRefTy source.typingEnv expression = some ty) (path : List Nat)
    {cx : FnCtx} {results : List Ty} {before : LS} {initial : GIR.Frame} {point : Pt}
    (atPoint : before.pp = some point) (related : Rel cfg env cx initial before)
    (map : RetainedSsaMap) (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, initial, state⟩)
    (extended : ExtT (lowerPlace (.deref expression) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (finalPoint : Pt) (frame : GIR.Frame) (alias : RetainedAlias),
      evalPlace 3 cfg env (.deref expression) state = .ok location state ∧
      DemandRuntimePrefix cx 2 ⟨point, initial, state⟩ ⟨finalPoint, frame, state⟩ ∧
      DemandUniformTraversal cx (DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.inputFuture map.values map.runs) 2 ⟨point, initial, state⟩ ⟨finalPoint, frame, state⟩ ∧
      Post cfg env cx before initial (lowerPlace (.deref expression) (lowerEnv cfg.mod env.vars results) before).2
        frame finalPoint [((lowerPlace (.deref expression) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      source.rootsEnv.access.aliasPlace path (.deref expression) = .ok [alias] ∧
      (map.addValues (lowerPlace (.deref expression) (lowerEnv cfg.mod env.vars results) before).1 [alias]).Realizes
        cfg.mod source.world env ⟨finalPoint, frame, state⟩ := by
  obtain ⟨location, finalPoint, frame, placed, steps, traversal, post⟩ :=
    accepted_generated_slice_reference_address source slice atPoint related map bounded realized extended
  obtain ⟨other, alias, otherPlaced, query, aliasAt⟩ := source.sliceReference_operandAlias slice path
  have equal : other = location := (Res.ok.inj (otherPlaced.symm.trans placed)).1
  subst other
  have carried : map.Realizes cfg.mod source.world env ⟨finalPoint, frame, state⟩ :=
    realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl
  have added := RetainedSsaMap.addValues_realizes (id := (lowerPlace (.deref expression) (lowerEnv cfg.mod env.vars results) before).1) (aliases := [alias]) carried (fun next member => by
    simp only [List.mem_singleton] at member
    subst next
    exact ValueAliasAt.of_post post (by simp) aliasAt)
  exact ⟨location, finalPoint, frame, alias, placed, steps, traversal, post, query, added⟩

#print axioms accepted_generated_slice_reference_retained

#print axioms accepted_generated_slice_reference_address

#print axioms PlaceSource.sliceReference_actual
end Goose.Lower
