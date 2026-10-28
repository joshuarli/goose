import Goose.Lower.DemandCallSliceHolderFuture

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure SliceSlotArgumentCell where
  value : ValueId
  argument : Nat
  slot : VarId
  scope : ScopeInst
  descriptor : LocalVar
  borrow : Mutability
  mutability : Mutability
  element : Ty
  alias : RetainedAlias

def SliceSlotArgumentCell.Checked {cfg : Cfg} {env : Env} {initial : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call contextId arguments origin) initial)
    (offset : Nat) (frame : GIR.Frame) (cell : SliceSlotArgumentCell) : Prop :=
  arguments[cell.argument]? = some (.byRef cell.borrow (.var cell.slot)) ∧ cell.argument < offset ∧
  cell.slot ∈ root.typingEnv.visible ∧ env.vars[cell.slot]? = some cell.descriptor ∧
  env.scopes.lookup cell.descriptor.scope = some cell.scope ∧ cell.descriptor.ty = .slice cell.mutability cell.element ∧
  root.rootsEnv.ann cell.slot = some cell.alias.roots ∧ cell.alias.ty = .slice cell.mutability cell.element ∧
  frame.vals[cell.value]? = some (.val (.ref ⟨.local env.act cell.scope cell.slot, []⟩))

theorem SliceSlotArgumentCell.ofReference {cfg : Cfg} {env : Env} {initial state after : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call contextId arguments origin) initial)
    {index : Nat} {borrow : Mutability} {slot : VarId}
    (found : arguments[index]? = some (.byRef borrow (.var slot)))
    (child : PlaceSource cfg env (.var slot) state)
    (target : child.ty.refTarget = true ∨ (child.ty.isSlice = true ∧ child.mutable = true ∧ (Place.var slot).sliceArg = true))
    (canonical : (ArgSource.byRef borrow child target).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context index (.byRef borrow (.var slot)) found))
    {mutability : Mutability} {element : Ty} (type : child.ty = .slice mutability element)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env (.var slot) state = .ok location after)
    {cx : FnCtx} {before built : LS} {initialFrame frame : GIR.Frame} {point : Pt} {id : ValueId}
    (post : Post cfg env cx before initialFrame built frame point [(id, .val (.ref location))]) :
    ∃ cell : SliceSlotArgumentCell, cell.value = id ∧ cell.Checked root (index + 1) frame ∧
      SliceSlotAliasAt cfg.mod root.world env after.store frame id cell.alias mutability element := by
  obtain ⟨plans, path, world, typing, roots, childContext⟩ := canonical
  have typed := child.typed
  simp only [tyPlace] at typed
  obtain ⟨binding, next, checked, resultType⟩ := (st_bind_ok _ _ _ _).1 typed
  have visibleChild := ((varOf_ok child.typingEnv slot child.typingStart (binding, next)).1 checked).1
  have visible : slot ∈ root.typingEnv.visible := by simpa only [typing] using visibleChild
  have placeOk := (child.result fuel location placed).typed
  rw [type] at placeOk
  rcases placeOk with impossible | valid | impossible
  · simp [Ty.refTarget] at impossible
  · obtain ⟨x, lv, si, value, equal, variableAt, scope, locationEq, variableType, _, stored, typedValue⟩ := valid
    cases equal
    obtain ⟨alias, query, relation⟩ := child.sliceSlotAlias type placed post (path := root.path ++ [index])
    have accessVariable : root.rootsEnv.impl.vars[slot]? = some lv := by
      rw [← roots, child.frame.vars_p]
      exact variableAt
    have annotation : root.rootsEnv.ann slot = some alias.roots := by
      rw [roots] at query
      cases annotation : root.rootsEnv.ann slot with
      | none =>
        have rawAnn : (root.rootsEnv.ctx.varRoots.find? (·.1 == slot)).map (·.2) = none := annotation
        simp [AccessEnv.aliasArg, AccessEnv.placeType?, PEnv.access, accessVariable, variableType,
          AccessEnv.exprRoots, AccessEnv.variableRoots, rawAnn, Ty.isRefLike, Functor.map, Except.map, reject] at query
      | some declared =>
        have rawAnn : (root.rootsEnv.ctx.varRoots.find? (·.1 == slot)).map (·.2) = some declared := annotation
        simp [AccessEnv.aliasArg, AccessEnv.placeType?, PEnv.access, accessVariable, variableType,
          AccessEnv.exprRoots, AccessEnv.variableRoots, rawAnn, Ty.isRefLike, Functor.map, Except.map] at query
        cases query
        rfl
    obtain ⟨slotLoc, backing, start, length, valueAt, slotPath, slotStored, referenceTyped, aliasType, aliasAt⟩ := relation
    have slotEq : slotLoc = location := by
      have same := valueAt.symm.trans (post.has (id, .val (.ref location)) (by simp))
      cases same
      rfl
    subst slotLoc
    let cell : SliceSlotArgumentCell := ⟨id, index, slot, si, lv, borrow, mutability, element, alias⟩
    refine ⟨cell, rfl, ?_, ?_⟩
    · exact ⟨found, by change index < index + 1; omega, visible, variableAt, scope, variableType, annotation, aliasType, by simpa [locationEq] using valueAt⟩
    · simpa only [world] using (show SliceSlotAliasAt cfg.mod child.world env after.store frame id alias mutability element from
        ⟨location, backing, start, length, valueAt, slotPath, slotStored, referenceTyped, aliasType, aliasAt⟩)
  · obtain ⟨x, lv, mu0, mu, ty, ann, impossible, _⟩ := impossible
    cases impossible

#print axioms SliceSlotArgumentCell.ofReference

theorem SliceSlotArgumentCell.advance {cfg : Cfg} {env : Env} {initialState : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    {root : ExprSource cfg env (.call contextId arguments origin) initialState}
    {offset nextOffset : Nat} {initial frame : GIR.Frame} {cell : SliceSlotArgumentCell}
    (checked : cell.Checked root offset initial) (later : offset ≤ nextOffset)
    {cx : FnCtx} {before built : LS} {point : Pt} {results : List (ValueId × RVal)}
    (post : Post cfg env cx before initial built frame point results) (bounded : cell.value < before.vals.size) :
    cell.Checked root nextOffset frame := by
  obtain ⟨found, prior, visible, descriptorAt, scope, descriptorType, annotation, aliasType, valueAt⟩ := checked
  refine ⟨found, Nat.lt_of_lt_of_le prior later, visible, descriptorAt, scope, descriptorType, annotation, aliasType, ?_⟩
  rw [post.same cell.value bounded]
  exact valueAt

#print axioms SliceSlotArgumentCell.advance

def SliceSlotArgumentCells.Realizes (cells : List SliceSlotArgumentCell) (m : Core.Module) (world : World) (env : Env)
    (point : DemandRuntimePoint) : Prop :=
  ∀ cell ∈ cells, SliceSlotAliasAt m world env point.state.store point.frame cell.value cell.alias cell.mutability cell.element

theorem SliceSlotArgumentCells.ofLaterValue {cfg : Cfg} {env : Env} {initial state : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call contextId arguments origin) initial)
    {offset : Nat} {expression : Expr} (current : arguments[offset]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context offset (.byVal expression) current))
    {frame : GIR.Frame} {point : Pt} (cells : List SliceSlotArgumentCell)
    (checked : ∀ cell ∈ cells, cell.Checked root offset frame) :
    SliceSlotArgumentCells.Realizes cells cfg.mod root.world env ⟨point, frame, state⟩ := by
  intro cell member
  obtain ⟨found, prior, visible, variableAt, scope, variableType, annotation, aliasType, valueAt⟩ := checked cell member
  exact SliceSlotAliasAt.ofLaterValueArgument root current found prior child canonical visible variableAt scope variableType annotation aliasType valueAt

theorem SliceSlotArgumentCells.ofLaterReference {cfg : Cfg} {env : Env} {initial state : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call contextId arguments origin) initial)
    {offset : Nat} {place : Place} {borrow : Mutability} (current : arguments[offset]? = some (.byRef borrow place))
    (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true ∨ (child.ty.isSlice = true ∧ child.mutable = true ∧ place.sliceArg = true))
    (canonical : (ArgSource.byRef borrow child target).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context offset (.byRef borrow place) current))
    {frame : GIR.Frame} {point : Pt} (cells : List SliceSlotArgumentCell)
    (checked : ∀ cell ∈ cells, cell.Checked root offset frame) :
    SliceSlotArgumentCells.Realizes cells cfg.mod root.world env ⟨point, frame, state⟩ := by
  intro cell member
  obtain ⟨found, prior, visible, variableAt, scope, variableType, annotation, aliasType, valueAt⟩ := checked cell member
  exact SliceSlotAliasAt.ofLaterReferenceArgument root current found prior child target canonical visible variableAt scope variableType annotation aliasType valueAt


theorem SliceSlotArgumentCells.ofLaterArgumentOutput {cfg : Cfg} {env : Env} {initial state : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call contextId arguments origin) initial)
    {offset : Nat} {argument : Arg} (current : arguments[offset]? = some argument)
    {cx : FnCtx} {before built : LS} {initialFrame frame : GIR.Frame} {point : Pt} {results : List (ValueId × RVal)}
    (post : Post cfg env cx before initialFrame built frame point results)
    (source : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state
      (callArgContext root.context offset argument current).outputFuture)
    (cells : List SliceSlotArgumentCell)
    (checked : ∀ cell ∈ cells, cell.Checked root offset initialFrame)
    (bounded : ∀ cell ∈ cells, cell.value < before.vals.size) :
    SliceSlotArgumentCells.Realizes cells cfg.mod root.world env ⟨point, frame, state⟩ := by
  intro cell member
  have next := SliceSlotArgumentCell.advance (checked cell member) (Nat.le_refl offset) post (bounded cell member)
  obtain ⟨found, prior, visible, variableAt, scope, variableType, annotation, aliasType, valueAt⟩ := next
  exact SliceSlotAliasAt.ofLaterArgumentOutputFrame root.context root.active root.access current source
    visible variableAt scope variableType annotation aliasType valueAt found prior

#print axioms SliceSlotArgumentCells.ofLaterArgumentOutput

#print axioms SliceSlotArgumentCells.ofLaterValue
#print axioms SliceSlotArgumentCells.ofLaterReference
end Goose.Lower
