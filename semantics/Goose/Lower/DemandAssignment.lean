import Goose.Lower.DemandTrace
import Goose.Lower.SourceContexts

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive AssignmentDemandStage where
  | destination
  | rhs
  | mutation
  | continuation

def AssignmentDemandStage.path (parent : List Nat) : AssignmentDemandStage → List Nat
  | .destination => parent ++ [0]
  | .rhs | .mutation => parent ++ [1]
  | .continuation => parent

def AssignmentDemandStage.phase : AssignmentDemandStage → DemandPhase
  | .destination => .place
  | .rhs | .mutation => .expression
  | .continuation => .statement

def AssignmentDemandStage.boundary : AssignmentDemandStage → DemandBoundary
  | .destination | .rhs => .entry
  | .mutation | .continuation => .exit

def AssignmentDemandStage.offset : AssignmentDemandStage → Nat
  | .destination => 0
  | .rhs => 1
  | .mutation => 2
  | .continuation => 3

def AssignmentDemandStage.target (start : Pt) (stage : AssignmentDemandStage) : Pt :=
  (start.1, start.2 + stage.offset)

def literalAssignmentPointMap (parent : List Nat) (start : Pt) : List DemandPointMapEntry :=
  ([.destination, .rhs, .mutation, .continuation] : List AssignmentDemandStage).map
    (fun stage => ⟨stage.target start, ⟨stage.path parent, stage.phase, stage.boundary⟩⟩)

theorem AssignmentDemandStage.target_injective (start : Pt) :
    Function.Injective (AssignmentDemandStage.target start) := by
  intro first second same
  have offsets := (Prod.mk.inj same).2
  cases first <;> cases second <;> simp only [offset] at offsets <;> first | rfl | omega

theorem literalAssignmentPointMap.target_unique {parent : List Nat} {start : Pt}
    {first second : DemandPointMapEntry}
    (firstMember : first ∈ literalAssignmentPointMap parent start)
    (secondMember : second ∈ literalAssignmentPointMap parent start)
    (same : first.target = second.target) : first = second := by
  obtain ⟨firstStage, _, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨secondStage, _, rfl⟩ := List.mem_map.mp secondMember
  have stages := AssignmentDemandStage.target_injective start same
  cases stages
  rfl

def AssignmentDemandStage.future {cfg : Cfg} {env : Env} {stmt : Stmt} {state : St}
    (source : StmtSource cfg env stmt state) : AssignmentDemandStage → List VarId
  | .destination => source.context.inputFuture
  | .rhs | .mutation | .continuation => source.context.outputFuture

def AssignmentDemandStage.operands (address : ValueId) (alias : RetainedAlias) :
    AssignmentDemandStage → List (ValueId × RetainedAlias)
  | .rhs | .mutation => [(address, alias)]
  | .destination | .continuation => []

def LiteralAssignmentDemand {cfg : Cfg} {env : Env} {state : St} {varId : VarId}
    {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state)
    (cx : FnCtx) (address : ValueId) (alias : RetainedAlias) (start : Pt) (point : DemandRuntimePoint) : Prop :=
  ∃ stage : AssignmentDemandStage,
    point.point = stage.target start ∧
    alias.source = .operand (AssignmentDemandStage.destination.path source.path) ∧
    source.rootsEnv.access.aliasPlace (AssignmentDemandStage.destination.path source.path) (.var varId) = .ok [alias] ∧
    match stage with
    | .continuation => DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv
        (stage.future source) (stage.operands address alias) [] point
    | _ => DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        (stage.future source) (stage.operands address alias) [] point

theorem LiteralAssignmentDemand.point_map {cfg : Cfg} {env : Env} {state : St} {varId : VarId}
    {type : IntTy} {number : Int} {origin : OriginId}
    {source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state}
    {cx : FnCtx} {address : ValueId} {alias : RetainedAlias} {start : Pt} {point : DemandRuntimePoint}
    (valid : LiteralAssignmentDemand source cx address alias start point) :
    ∃ entry ∈ literalAssignmentPointMap source.path start, entry.target = point.point := by
  obtain ⟨stage, targetAt, _, _, _⟩ := valid
  refine ⟨⟨stage.target start, ⟨stage.path source.path, stage.phase, stage.boundary⟩⟩, ?_, targetAt.symm⟩
  apply List.mem_map.mpr
  refine ⟨stage, ?_, rfl⟩
  cases stage <;> simp

private theorem literal_assignment_alias {cfg : Cfg} {env : Env} {state : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state)
    {location : Loc} (done : evalPlace 1 cfg env (.var varId) state = .ok location state) :
    ∃ alias : RetainedAlias,
      alias.source = .operand (AssignmentDemandStage.destination.path source.path) ∧
      source.rootsEnv.access.aliasPlace (AssignmentDemandStage.destination.path source.path) (.var varId) = .ok [alias] ∧
      AliasAt cfg.mod source.world env state.store alias (.ref location) := by
  obtain ⟨destination, typing, roots, world, observation, ready⟩ := source.assignChildren
  obtain ⟨child, _, _, _, _, typeEq⟩ := ready 1 location state done
  have literalType := child.typed
  simp only [tyExpr] at literalType
  have childType : child.ty = .int type := by
    split at literalType
    · exact (congrArg Prod.fst (Except.ok.inj literalType)).symm
    · cases literalType
  have destinationType : destination.ty = .int type := typeEq.symm.trans childType
  have result := destination.result 1 location done
  have valid := result.typed
  rw [destinationType] at valid
  have locationType : HasTy cfg.mod destination.world.G state.store (.ref location) (.ref .mutable (.int type)) := by
    rcases valid with valid | invalid | invalid
    · exact ⟨location, rfl, Or.inl valid⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, impossible, _⟩ := invalid
      cases impossible
    · obtain ⟨_, _, _, _, _, _, _, _, _, impossible, _⟩ := invalid
      cases impossible
  have lookup := tyPlace_accessType
    (destination.frame.mod_t.trans destination.frame.mod_p.symm)
    (destination.frame.vars_t.trans destination.frame.vars_p.symm) destination.typed
  rw [roots, destinationType] at lookup
  have rooted := destination.rooted
  change Except.ok ([RootRef.local varId], destination.rootsStart) =
    Except.ok (destination.roots, destination.rootsEnd) at rooted
  have rootsShape : destination.roots = [.local varId] :=
    (congrArg Prod.fst (Except.ok.inj rooted)).symm
  refine ⟨⟨.ref .mutable (.int type), destination.roots,
    .operand (AssignmentDemandStage.destination.path source.path)⟩, rfl, ?_, ?_, ?_⟩
  · simp [AccessEnv.aliasPlace, lookup, AccessEnv.placeRoots, rootsShape,
      Ty.interiorTarget?, Ty.ownerElem?]
    rfl
  · simpa [world] using locationType
  · intro root target
    have targetEq : location.root = root := target
    rw [← targetEq]
    simpa [world] using result.rooted

private theorem output_frame {cfg : Cfg} {env : Env} {state : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state) :
    Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      source.context.outputFuture := by
  apply source.frame.narrowFuture
  intro varId member
  cases contextEq : source.context <;>
    simp only [contextEq, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
      NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.visibleAfter] at member ⊢ <;>
    exact List.mem_append_right _ member

private theorem literal_assignment_execution_traversal {cfg : Cfg} {env : Env} {state after : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state)
    {cx : FnCtx} {ls ls' : LS} {pt : Pt} {frame : GIR.Frame} {loop : Option LoopCtx}
    {location : Loc} {results : List Ty}
    (placeDone : evalPlace 1 cfg env (.var varId) state = .ok location state)
    (writeDone : writeLoc location (.int type number) state = .ok () after)
    (lowered : lowerStmt loop (.assign (.var varId) (.lit type number) origin)
      (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (point : ls.pp = some pt) (extended : ExtT ls' cx.fn.blocks)
    (related : Rel cfg env cx frame ls) :
    ∃ (address value : ValueId) (alias : RetainedAlias) (finalPoint : Pt) (finalFrame : GIR.Frame),
      instAt cx.fn pt = some (.def address (.slotAddr varId)) ∧
      alias.source = .operand (AssignmentDemandStage.destination.path source.path) ∧
      DemandUniformTraversal cx
        (fun point => LiteralAssignmentDemand source cx address alias pt point ∧
          DemandFramePreserved ls.vals.size frame state after point) 3
        ⟨pt, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      finalFrame.vals[value]? = some (.val (.int type number)) ∧
      ls'.pp = some finalPoint ∧ Rel cfg env cx finalFrame ls' := by
  simp only [lowerStmt, lowerPlace, lowerExpr, bind_eq] at lowered
  obtain ⟨address, addressed, addressLowered, value, evaluated, valueLowered, stored⟩ := lowered
  have valueExtended := extended.of_adv (adv_emitEffect stored)
  have addressExtended := valueExtended.of_adv (adv_emitDef valueLowered)
  have start := Post.init related point
  obtain ⟨first, firstInstruction⟩ := start.def_leaf addressLowered addressExtended (.val (.ref location))
  obtain ⟨second, secondInstruction⟩ := (Post.init first.rel first.pp).def_leaf valueLowered valueExtended (.val (.int type number))
  obtain ⟨last, lastInstruction⟩ := second.eff_leaf stored extended
  obtain ⟨alias, aliasSite, aliasQuery, aliasValid⟩ := literal_assignment_alias source placeDone
  have coreDone : execStmt 2 cfg env (.assign (.var varId) (.lit type number) origin) state =
      .ok (.normal .unit) after := by
    simp only [execStmt, bind_apply, placeDone, evalExpr, pure_apply, writeDone]
  have result := source.result 2 (.normal .unit) coreDone
  have initialOperands : RetainedOperandsAt cfg.mod source.world env state.store frame [] [] := by
    constructor <;> simp
  have addressCell := first.has (address, .val (.ref location)) (by simp)
  have addressBound := first.lt (address, .val (.ref location)) (by simp)
  have addressCell' := (second.same address addressBound).trans addressCell
  have valueCell := second.has (value, .val (.int type number)) (by simp)
  have retainedFirst : RetainedOperandsAt cfg.mod source.world env state.store
      (frame.set address (.val (.ref location))) [(address, alias)] [] := by
    constructor
    · intro cell member
      simp only [List.mem_singleton] at member
      subst cell
      exact ⟨.ref location, addressCell, aliasValid⟩
    · simp
  have retainedSecond : RetainedOperandsAt cfg.mod source.world env state.store
      ((frame.set address (.val (.ref location))).set value (.val (.int type number)))
      [(address, alias)] [] := by
    constructor
    · intro cell member
      simp only [List.mem_singleton] at member
      subst cell
      exact ⟨.ref location, addressCell', aliasValid⟩
    · simp
  refine ⟨address, value, alias, (pt.1, pt.2 + 3), _, firstInstruction, aliasSite, ?_, valueCell, last.pp, last.rel⟩
  apply DemandUniformTraversal.next (middle := ⟨(pt.1, pt.2 + 1), frame.set address (.val (.ref location)), state⟩)
  · exact ⟨⟨.destination, rfl, aliasSite, aliasQuery, ⟨⟨ls, point, related⟩, source.frame, initialOperands⟩⟩,
      Same.refl _ _, Or.inl rfl⟩
  · intro fuel
    apply DemandLinearStep.definition firstInstruction
    have action : execOp fuel cx frame (.slotAddr varId) =
        evalPlace 1 cfg env (.var varId) >>= fun loc => pure (.val (.ref loc)) := by
      simp only [execOp, execPure, evalPlace, slotRoot_eq related, bind_assoc, pure_bind]
    simp only [action, bind_apply, placeDone, pure_apply]
  · apply DemandUniformTraversal.next (middle := ⟨(pt.1, pt.2 + 2), (frame.set address (.val (.ref location))).set value (.val (.int type number)), state⟩)
    · exact ⟨⟨.rhs, rfl, aliasSite, aliasQuery, ⟨⟨addressed, first.pp, first.rel⟩, output_frame source, retainedFirst⟩⟩,
        first.same, Or.inl rfl⟩
    · intro fuel
      apply DemandLinearStep.definition secondInstruction
      simp only [execOp, execPure, pure_apply]
    · apply DemandUniformTraversal.next (middle := ⟨(pt.1, pt.2 + 3), (frame.set address (.val (.ref location))).set value (.val (.int type number)), after⟩)
      · exact ⟨⟨.mutation, rfl, aliasSite, aliasQuery, ⟨⟨evaluated, second.pp, second.rel⟩, output_frame source, retainedSecond⟩⟩,
          first.same.trans second.same first.mono, Or.inl rfl⟩
      · intro fuel
        apply DemandLinearStep.effect lastInstruction
        simp only [execEff, getVal_of addressCell', getVal_of valueCell,
          Core.expectRef, pure_bind, bind_apply, writeDone, pure_apply]
      · apply DemandUniformTraversal.done
        exact ⟨⟨.continuation, rfl, aliasSite, aliasQuery, ⟨⟨ls', last.pp, last.rel⟩, result.frame,
          by constructor <;> simp [AssignmentDemandStage.operands]⟩⟩,
          first.same.trans last.same first.mono, Or.inr rfl⟩

theorem accepted_literal_assignment_execution_traversal {cfg : Cfg} {env : Env} {state : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state)
    {cx : FnCtx} {ls ls' : LS} {pt : Pt} {frame : GIR.Frame} {loop : Option LoopCtx}
    {results : List Ty}
    (lowered : lowerStmt loop (.assign (.var varId) (.lit type number) origin)
      (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (point : ls.pp = some pt) (extended : ExtT ls' cx.fn.blocks)
    (related : Rel cfg env cx frame ls) :
    ∃ (after : St) (address value : ValueId) (alias : RetainedAlias)
        (finalPoint : Pt) (finalFrame : GIR.Frame),
      execStmt 2 cfg env (.assign (.var varId) (.lit type number) origin) state =
        .ok (.normal .unit) after ∧
      instAt cx.fn pt = some (.def address (.slotAddr varId)) ∧
      alias.source = .operand (AssignmentDemandStage.destination.path source.path) ∧
      DemandUniformTraversal cx
        (fun point => LiteralAssignmentDemand source cx address alias pt point ∧
          DemandFramePreserved ls.vals.size frame state after point) 3
        ⟨pt, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      finalFrame.vals[value]? = some (.val (.int type number)) ∧
      ls'.pp = some finalPoint ∧ Rel cfg env cx finalFrame ls' := by
  obtain ⟨destination, _, _, _, _, _⟩ := source.assignChildren
  have typed := destination.typed
  simp only [tyPlace] at typed
  obtain ⟨binding, finish, variableChecked, _⟩ := (st_bind_ok _ _ _ _).mp typed
  have visible := ((varOf_ok _ _ _ _).mp variableChecked).1
  have demanded : varId ∈ destination.context.inputFuture := by
    cases destination.context <;>
      simp [EvaluationContext.inputFuture, NodeContext.inputFuture, DemandNode.variables, Place.variables]
  obtain ⟨binding, scope, old, variableAt, scopeAt, _, rootAt, _⟩ :=
    destination.frame.vis varId visible demanded
  let location : Loc := ⟨.local env.act scope varId, []⟩
  have placeDone : evalPlace 1 cfg env (.var varId) state = .ok location state := by
    simp [evalPlace, rootOf, variableAt, scopeAt, location, pure_apply]
  let after : St := { state with store := ⟨(state.store.roots.erase location.root).insert location.root (.int type number)⟩ }
  have writeDone : writeLoc location (.int type number) state = .ok () after := by
    simp only [writeLoc, location, write_root state.store _ old _ rootAt]
    rfl
  obtain ⟨address, value, alias, finalPoint, finalFrame, instruction, aliasSource, traversal, valueAt, finalPointAt, finalRelated⟩ :=
    literal_assignment_execution_traversal source placeDone writeDone lowered point extended related
  refine ⟨after, address, value, alias, finalPoint, finalFrame, ?_, instruction,
    aliasSource, traversal, valueAt, finalPointAt, finalRelated⟩
  simp only [execStmt, bind_apply, placeDone, evalExpr, pure_apply, writeDone]

theorem accepted_literal_assignment_demand_traversal {cfg : Cfg} {env : Env} {state : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state)
    {cx : FnCtx} {ls ls' : LS} {pt : Pt} {frame : GIR.Frame} {loop : Option LoopCtx}
    {results : List Ty}
    (lowered : lowerStmt loop (.assign (.var varId) (.lit type number) origin)
      (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (point : ls.pp = some pt) (extended : ExtT ls' cx.fn.blocks)
    (related : Rel cfg env cx frame ls) :
    ∃ (after : St) (address value : ValueId) (alias : RetainedAlias)
        (finalPoint : Pt) (finalFrame : GIR.Frame),
      execStmt 2 cfg env (.assign (.var varId) (.lit type number) origin) state =
        .ok (.normal .unit) after ∧
      instAt cx.fn pt = some (.def address (.slotAddr varId)) ∧
      alias.source = .operand (AssignmentDemandStage.destination.path source.path) ∧
      DemandUniformTraversal cx (LiteralAssignmentDemand source cx address alias pt) 3
        ⟨pt, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      finalFrame.vals[value]? = some (.val (.int type number)) ∧
      ls'.pp = some finalPoint ∧ Rel cfg env cx finalFrame ls' := by
  obtain ⟨after, address, value, alias, finalPoint, finalFrame, done, instruction, aliasSource,
    traversal, valueAt, finalPointAt, finalRelated⟩ :=
    accepted_literal_assignment_execution_traversal source lowered point extended related
  exact ⟨after, address, value, alias, finalPoint, finalFrame, done, instruction, aliasSource,
    traversal.mono (fun _ valid => valid.1), valueAt, finalPointAt, finalRelated⟩

end Goose.Lower
