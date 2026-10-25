import Goose.Core.Sound.Check

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

private theorem after_origin {α : Type} {env : TEnv} {origin start : Nat}
    {action : Core.T α} {result : α × Nat}
    (source : (do checkOrg env origin; action) start = .ok result) :
    action start = .ok result := by
  obtain ⟨_, next, checked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have same : next = start := congrArg Prod.snd ((checkOrg_ok _ _ _ _).mp checked).2
  subst next
  exact source

private theorem after_shrink {α : Type} {env : TEnv} {start : Nat}
    {action : Core.T α} {result : α × Nat}
    (source : (do requireShrink env; action) start = .ok result) :
    action start = .ok result := by
  obtain ⟨_, next, checked, source⟩ := (st_bind_ok _ _ _ _).mp source
  unfold requireShrink at checked
  inv at checked
  have same := checked.2
  subst next
  exact source

private theorem ownerRun_state {env : TEnv} {expr : Expr} {type : Ty} {start finish : Nat}
    (source : checkOwnerRun env expr type start = .ok ((), finish)) : finish = start := by
  unfold checkOwnerRun at source
  split at source <;> inv at source
  exact source

theorem tyStmt_let_children {env output : TEnv} {x : VarId} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.letS x expr origin) start = .ok (output, finish)) :
    ∃ localVar childType childStart,
      declare env x scope start = .ok (localVar, childStart) ∧
      Core.tyExpr env expr childStart = .ok (childType, finish) ∧
      childType.passableTo localVar.ty = true ∧
      output = { env with visible := x :: env.visible } := by
  simp only [Core.tyStmt] at source
  have source := after_origin source
  obtain ⟨localVar, childStart, declared, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨childType, childFinish, child, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, ownerFinish, owner, source⟩ := (st_bind_ok _ _ _ _).mp source
  have same := ownerRun_state owner
  subst ownerFinish
  inv at source
  obtain ⟨passable, outputEq, finishEq⟩ := source
  subst finish
  exact ⟨localVar, childType, childStart, declared, child, passable, outputEq⟩

theorem tyStmt_assign_children {env output : TEnv} {place : Place} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assign place expr origin) start = .ok (output, finish)) :
    ∃ info childStart,
      Core.tyPlace env place start = .ok (info, childStart) ∧
      Core.tyExpr env expr childStart = .ok (info.ty, finish) ∧
      (info.ty.flat || info.ty.isSlice && place.derefVar?.isSome) = true ∧
      info.bindingWritable = true ∧ output = env := by
  simp only [Core.tyStmt] at source
  have source := after_origin source
  obtain ⟨info, childStart, placeChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  inv at source
  simp only [beq_iff_eq] at source
  obtain ⟨flat, childType, childFinish, child, typeEq, writable, outputEq, finishEq⟩ := source
  subst childType
  subst finish
  exact ⟨info, childStart, placeChecked, child, flat, writable, outputEq⟩

theorem tyStmt_assignOp_children {env output : TEnv} {place : Place} {expr : Expr}
    {operation : BinOp} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignOp operation place expr origin) start = .ok (output, finish)) :
    ∃ info integer childStart,
      Core.tyPlace env place start = .ok (info, childStart) ∧
      info.ty = .int integer ∧
      Core.tyExpr env expr childStart = .ok (.int integer, finish) ∧
      info.bindingWritable = true ∧ output = env := by
  simp only [Core.tyStmt] at source
  have source := after_origin source
  obtain ⟨info, childStart, placeChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  inv at source
  obtain ⟨integer, infoType, childType, childFinish, child, childInteger, childTypeEq,
    integerEq, writable, outputEq, finishEq⟩ := source
  subst childInteger
  subst childType
  subst finish
  exact ⟨info, integer, childStart, placeChecked, infoType, child, writable, outputEq⟩

theorem tyStmt_rebind_children {env output : TEnv} {x : VarId} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.rebind x expr origin) start = .ok (output, finish)) :
    ∃ localVar childType,
      env.vars[x]? = some localVar ∧ x ∈ env.visible ∧ localVar.ty.isRefLike = true ∧
      localVar.kind = .mutable ∧ Core.tyExpr env expr start = .ok (childType, finish) ∧
      childType.passableTo localVar.ty = true ∧ output = env := by
  simp only [Core.tyStmt] at source
  have source := after_origin source
  inv at source
  simp only [beq_iff_eq] at source
  obtain ⟨visible, localVar, row, refLike, mutable, childType, childFinish, child,
    passable, outputEq, finishEq⟩ := source
  subst finish
  exact ⟨localVar, childType, row, visible, refLike, mutable, child, passable, outputEq⟩

theorem tyStmt_append_children {env output : TEnv} {owner : Place} {view : View}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.append owner view origin) start = .ok (output, finish)) :
    ∃ info element writable childStart,
      Core.tyPlace env owner start = .ok (info, childStart) ∧
      info.ty.ownerElem? = some element ∧
      Core.tyView env view childStart = .ok ((element, writable), finish) ∧
      info.ownerMutationWritable env.mod.profile = true ∧ output = env := by
  simp only [Core.tyStmt] at source
  have source := after_origin source
  obtain ⟨info, childStart, ownerChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨element, elementFinish, elementChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have ownerFacts := ownerElement_ok _ _ _ _ _ elementChecked
  have same := ownerFacts.2.2
  subst elementFinish
  inv at source
  simp only [beq_iff_eq] at source
  obtain ⟨viewElement, writable, childFinish, viewChecked, elementEq, writableOwner, outputEq, finishEq⟩ := source
  subst viewElement
  subst finish
  exact ⟨info, element, writable, childStart, ownerChecked, ownerFacts.2.1,
    viewChecked, writableOwner, outputEq⟩

theorem tyStmt_popN_children {env output : TEnv} {owner : Place} {count : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.popN owner count origin) start = .ok (output, finish)) :
    ∃ info element integer childStart,
      Core.tyPlace env owner start = .ok (info, childStart) ∧
      info.ty.ownerElem? = some element ∧
      Core.tyExpr env count childStart = .ok (.int integer, finish) ∧
      info.contentsWritable = true ∧ output = env := by
  simp only [Core.tyStmt] at source
  have source := after_origin (after_shrink source)
  obtain ⟨info, childStart, ownerChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨element, elementFinish, elementChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have ownerFacts := ownerElement_ok _ _ _ _ _ elementChecked
  have same := ownerFacts.2.2
  subst elementFinish
  inv at source
  obtain ⟨childType, childFinish, child, integer, childTypeEq, writable, outputEq, finishEq⟩ := source
  subst childType
  subst finish
  exact ⟨info, element, integer, childStart, ownerChecked, ownerFacts.2.1,
    child, writable, outputEq⟩

theorem tyStmt_clear_children {env output : TEnv} {owner : Place}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.clear owner origin) start = .ok (output, finish)) :
    ∃ info element,
      Core.tyPlace env owner start = .ok (info, finish) ∧
      info.ty.ownerElem? = some element ∧ info.contentsWritable = true ∧ output = env := by
  simp only [Core.tyStmt] at source
  have source := after_origin (after_shrink source)
  obtain ⟨info, childStart, ownerChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨element, elementFinish, elementChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have ownerFacts := ownerElement_ok _ _ _ _ _ elementChecked
  have same := ownerFacts.2.2
  subst elementFinish
  inv at source
  obtain ⟨writable, outputEq, finishEq⟩ := source
  subst finish
  exact ⟨info, element, ownerChecked, ownerFacts.2.1, writable, outputEq⟩

theorem tyStmt_resize_children {env output : TEnv} {owner : Place} {size : Expr}
    {fill : Option Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.resize owner size fill origin) start = .ok (output, finish)) :
    ∃ info element integer childStart sizeFinish,
      Core.tyPlace env owner start = .ok (info, childStart) ∧
      info.ty.ownerElem? = some element ∧
      Core.tyExpr env size childStart = .ok (.int integer, sizeFinish) ∧
      (match fill with
       | none => finish = sizeFinish
       | some expr => Core.tyExpr env expr sizeFinish = .ok (element, finish)) ∧
      info.contentsWritable = true ∧ output = env := by
  cases fill
  all_goals
    simp only [Core.tyStmt] at source
    have source := after_origin (after_shrink source)
    obtain ⟨info, childStart, ownerChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨element, elementFinish, elementChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
    have ownerFacts := ownerElement_ok _ _ _ _ _ elementChecked
    have same := ownerFacts.2.2
    subst elementFinish
    inv at source
  case none =>
    obtain ⟨sizeType, sizeFinish, sizeChecked, integer, sizeTypeEq, writable, outputEq, finishEq⟩ := source
    subst sizeType
    exact ⟨info, element, integer, childStart, sizeFinish, ownerChecked, ownerFacts.2.1,
      sizeChecked, finishEq, writable, outputEq⟩
  case some expr =>
    simp only [beq_iff_eq] at source
    obtain ⟨sizeType, sizeFinish, sizeChecked, integer, sizeTypeEq,
      fillType, fillFinish, fillChecked, fillTypeEq, writable, outputEq, finishEq⟩ := source
    subst sizeType
    subst fillType
    subst finish
    exact ⟨info, element, integer, childStart, sizeFinish, ownerChecked, ownerFacts.2.1,
      sizeChecked, fillChecked, writable, outputEq⟩

theorem tyStmt_assignWhole_children {env output : TEnv} {owner : Place} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole owner expr origin) start = .ok (output, finish)) :
    ∃ info element childStart,
      Core.tyPlace env owner start = .ok (info, childStart) ∧
      (info.ty = .grow element ∨ info.ty = .growshrink element) ∧
      Core.tyExpr env expr childStart = .ok (info.ty, finish) ∧
      info.bindingWritable = true ∧ info.contentsWritable = true ∧ output = env := by
  simp only [Core.tyStmt] at source
  have source := after_origin (after_shrink source)
  obtain ⟨info, childStart, ownerChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨type, binding, contents⟩ := info
  cases type <;> simp only at source
  all_goals try { inv at source }
  all_goals
    rename_i element
    obtain ⟨childType, childFinish, child, source⟩ := (st_bind_ok _ _ _ _).mp source
    inv at source
    simp only [beq_iff_eq] at source
    obtain ⟨childTypeEq, ownerFinish, ownerRun, writable, outputEq, finishEq⟩ := source
    have same := ownerRun_state ownerRun
    subst ownerFinish
    subst childType
    subst finish
    have caps : binding = true ∧ contents = true := by
      simpa only [Bool.and_eq_true] using writable
    refine ⟨_, element, childStart, ownerChecked, ?_, child, caps.1, caps.2, outputEq⟩
    simp

theorem requireShrink_profile {env : TEnv} {start finish : Nat}
    (source : requireShrink env start = .ok ((), finish)) : env.mod.profile = .shrink := by
  unfold requireShrink at source
  inv at source
  exact beq_iff_eq.mp source.1

theorem tyStmt_popN_profile {env output : TEnv} {owner : Place} {count : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.popN owner count origin) start = .ok (output, finish)) :
    env.mod.profile = .shrink := by
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact requireShrink_profile checked

theorem tyStmt_resize_profile {env output : TEnv} {owner : Place} {size : Expr} {fill : Option Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.resize owner size fill origin) start = .ok (output, finish)) :
    env.mod.profile = .shrink := by
  cases fill <;> obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  all_goals exact requireShrink_profile checked

theorem tyStmt_clear_profile {env output : TEnv} {owner : Place}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.clear owner origin) start = .ok (output, finish)) :
    env.mod.profile = .shrink := by
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact requireShrink_profile checked

theorem tyStmt_assignWhole_profile {env output : TEnv} {owner : Place} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole owner expr origin) start = .ok (output, finish)) :
    env.mod.profile = .shrink := by
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact requireShrink_profile checked

end Goose.Lower.Validation
