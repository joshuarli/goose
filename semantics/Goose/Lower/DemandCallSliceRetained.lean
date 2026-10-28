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

theorem SliceSlotArgumentCell.advance {cfg : Cfg} {env : Env} {initialState : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    {root : ExprSource cfg env (.call contextId arguments origin) initialState}
    {offset nextOffset : Nat} {initial frame : GIR.Frame} {cell : SliceSlotArgumentCell}
    (checked : cell.Checked root offset initial) (later : offset ≤ nextOffset)
    {cx : FnCtx} {before built : LS} {point : Pt}
    (post : Post cfg env cx before initial built frame point []) (bounded : cell.value < before.vals.size) :
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

#print axioms SliceSlotArgumentCells.ofLaterValue
#print axioms SliceSlotArgumentCells.ofLaterReference
end Goose.Lower
