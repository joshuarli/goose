import Goose.Lower.Validation.ValueBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def OperandBounds (state : LS) : Prop :=
  ∀ inst ∈ state.insts, ∀ value ∈ inst.uses, value < state.vals.size

def OperandRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) →
    OperandBounds before → OperandBounds after

theorem OperandRun.pure (result : α) : OperandRun (pure result) := by
  intro le before value after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem OperandRun.bind {action : B α} {next : α → B β}
    (first : OperandRun action) (second : ∀ value, OperandRun (next value)) :
    OperandRun (action >>= next) := by
  intro le before result after run checked
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ _ secondRun (first _ _ _ _ firstRun checked)

theorem OperandRun.of_unchanged {action : B α}
    (instructions : ∀ le state, (action le state).2.insts = state.insts)
    (values : ∀ le state, state.vals.size ≤ (action le state).2.vals.size) : OperandRun action := by
  intro le before result after run checked inst member value use
  have same := instructions le before
  have grows := values le before
  rw [run] at same grows
  rw [same] at member
  exact Nat.lt_of_lt_of_le (checked inst member value use) grows

theorem operands_appendInst {before : LS} (checked : OperandBounds before)
    (block : BlockId) (inst : Inst) (bounded : ∀ value ∈ inst.uses, value < before.vals.size) :
    OperandBounds (before.appendInst block inst) := by
  intro next member value use
  change next ∈ (before.blocks.modify block fun blk =>
    { blk with insts := blk.insts.push inst }).toList.flatMap (fun blk => blk.insts.toList) at member
  obtain ⟨blk, blockMember, instructionMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  rw [Array.getElem?_modify] at lookup
  by_cases same : block = index
  · simp only [same, ↓reduceIte] at lookup
    cases previous : before.blocks[index]? with
    | none => simp [previous] at lookup
    | some old =>
      simp only [previous, Option.map_some, Option.some.injEq] at lookup
      subst blk
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at instructionMember
      rcases instructionMember with oldInstruction | fresh
      · exact checked next (List.mem_flatMap.mpr
          ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? previous), oldInstruction⟩) value use
      · subst next
        exact bounded value use
  · simp only [same, ↓reduceIte] at lookup
    exact checked next (List.mem_flatMap.mpr
      ⟨blk, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), instructionMember⟩) value use

theorem operands_emitDef {op : Op} {le before result after}
    (run : emitDef op le before = (result, after)) (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → ∀ value ∈ op.uses, value < before.vals.size) :
    OperandBounds after := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have extended := operands_appendInst checked block (.def before.vals.size op)
      (bounded (by simp [current]))
    intro inst member value use
    have bound := extended inst (by exact member) value use
    exact Nat.lt_of_lt_of_le bound (by simp [LS.appendInst])

theorem operands_emitEffect {effect : Effect} {le before result after}
    (run : emitEffect effect le before = (result, after)) (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → ∀ value ∈ effect.uses, value < before.vals.size) :
    OperandBounds after := by
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact operands_appendInst checked block (.eff effect) (bounded (by simp [current]))

theorem operands_emitTerm {term : Term} {le before result after}
    (run : emitTerm term le before = (result, after)) (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → ∀ value ∈ term.uses, value < before.vals.size) :
    OperandBounds after := by
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact operands_appendInst checked block (.term term) (bounded (by simp [current]))

theorem operands_newBlock (types : List VTy) : OperandRun (newBlock types) := by
  apply OperandRun.of_unchanged
  · intro le state
    rw [newBlock_run_general]
    simp [LS.insts]
  · intro le state
    rw [newBlock_run_general]
    simp [array_size_pushParamTypes]

theorem OperandRun.emitDefAfter {action : B α} {op : α → Op}
    (first : OperandRun action)
    (outputs : ∀ le before result after, action le before = (result, after) →
      after.cur.isSome = true → ∀ value ∈ (op result).uses, value < after.vals.size) :
    OperandRun (do let result ← action; emitDef (op result)) := by
  intro le before result after run checked
  obtain ⟨input, mid, firstRun, emitted⟩ := bind_eq.mp run
  exact operands_emitDef emitted (first _ _ _ _ firstRun checked) (outputs _ _ _ _ firstRun)

theorem OperandRun.emitDefAfterValue {action : B ValueId} {op : ValueId → Op}
    (first : OperandRun action) (bounded : ValueRun action)
    (uses : ∀ input value, value ∈ (op input).uses → value = input) :
    OperandRun (do let result ← action; emitDef (op result)) := by
  apply first.emitDefAfter
  intro le before result after run live value member
  rw [uses result value member]
  exact bounded _ _ _ _ run live

theorem OperandRun.emitDefAfterValues {action : B (List ValueId)} {op : List ValueId → Op}
    (first : OperandRun action) (bounded : ValueListRun action)
    (uses : ∀ inputs value, value ∈ (op inputs).uses → value ∈ inputs) :
    OperandRun (do let result ← action; emitDef (op result)) := by
  apply first.emitDefAfter
  intro le before result after run live value member
  exact bounded _ _ _ _ run live value (uses result value member)

theorem OperandRun.emitDefAfterTwo {left right : B ValueId}
    {inspect : ValueId → ValueId → B Op}
    (leftRun : OperandRun left) (rightRun : OperandRun right)
    (leftBound : ValueRun left) (rightBound : ValueRun right)
    (rightAdvances : AdvB right) (rightDead : DeadRun right)
    (unchanged : ∀ x y le state, (inspect x y le state).2 = state)
    (uses : ∀ x y le state value, value ∈ (inspect x y le state).1.uses →
      value = x ∨ value = y) :
    OperandRun (do
      let x ← left
      let y ← right
      let op ← inspect x y
      emitDef op) := by
  intro le before result after run checked
  obtain ⟨x, mid, first, y, next, second, op, loaded, loading, emission⟩ :=
    (by simpa only [bind_eq] using run)
  have same := unchanged x y le next
  rw [loading] at same
  simp only at same
  subst loaded
  have operator : op = (inspect x y le next).1 := by rw [loading]
  apply operands_emitDef emission (rightRun _ _ _ _ second (leftRun _ _ _ _ first checked))
  intro live value member
  rw [operator] at member
  rcases uses x y le next value member with rfl | rfl
  · exact Nat.lt_of_lt_of_le
      (leftBound _ _ _ _ first (live_before rightDead second live))
      ((rightAdvances _ _ _ _ second).vals)
  · exact rightBound _ _ _ _ second live

theorem OperandRun.emitDefAfterValueInspect {action : B ValueId}
    {inspect : ValueId → B Op}
    (first : OperandRun action) (bounded : ValueRun action)
    (unchanged : ∀ input le state, (inspect input le state).2 = state)
    (uses : ∀ input le state value, value ∈ (inspect input le state).1.uses → value = input) :
    OperandRun (do let result ← action; let op ← inspect result; emitDef op) := by
  intro le before result after run checked
  obtain ⟨input, mid, firstRun, op, loaded, loading, emission⟩ :=
    (by simpa only [bind_eq] using run)
  have same := unchanged input le mid
  rw [loading] at same
  simp only at same
  subst loaded
  have operator : op = (inspect input le mid).1 := by rw [loading]
  apply operands_emitDef emission (first _ _ _ _ firstRun checked)
  intro live value member
  rw [operator] at member
  rw [uses input le mid value member]
  exact bounded _ _ _ _ firstRun live

theorem operands_lowerExpr_lit (ty : IntTy) (number : Int) :
    OperandRun (lowerExpr (.lit ty number)) := by
  intro le before result after run checked
  exact operands_emitDef run checked (by simp [Op.uses])

theorem operands_lowerExpr_bool (value : Bool) : OperandRun (lowerExpr (.bool value)) := by
  intro le before result after run checked
  exact operands_emitDef run checked (by simp [Op.uses])

theorem operands_lowerPlace_var (varId : VarId) : OperandRun (lowerPlace (.var varId)) := by
  intro le before result after run checked
  exact operands_emitDef run checked (by simp [Op.uses])

theorem operands_lowerPlace_global (global : GlobalId) : OperandRun (lowerPlace (.global global)) := by
  intro le before result after run checked
  exact operands_emitDef run checked (by simp [Op.uses])

theorem operands_lowerExpr_read (place : Place) (child : OperandRun (lowerPlace place)) :
    OperandRun (lowerExpr (.read place)) := by
  exact child.emitDefAfterValue (value_lowerPlace place) (by simp [Op.uses])

theorem operands_lowerPlace_field (place : Place) (field : Nat)
    (child : OperandRun (lowerPlace place)) : OperandRun (lowerPlace (.field place field)) := by
  exact child.emitDefAfterValue (value_lowerPlace place) (by simp [Op.uses])

theorem operands_lowerView (view : View)
    (child : match view with
      | .of place => OperandRun (lowerPlace place)
      | .val expr => OperandRun (lowerExpr expr)) : OperandRun (lowerView view) := by
  cases view with
  | of place => exact child.emitDefAfterValue (value_lowerPlace place) (by simp [Op.uses])
  | val expr => exact child.emitDefAfterValue (value_lowerExpr expr) (by simp [Op.uses])

theorem operands_lowerExpr_not (expr : Expr) (child : OperandRun (lowerExpr expr)) :
    OperandRun (lowerExpr (.not expr)) := by
  exact child.emitDefAfterValue (value_lowerExpr expr) (by simp [Op.uses])

theorem operands_lowerExpr_fill (ty : Ty) (expr : Expr) (child : OperandRun (lowerExpr expr)) :
    OperandRun (lowerExpr (.fill ty expr)) := by
  exact child.emitDefAfterValue (value_lowerExpr expr) (by simp [Op.uses])

theorem operands_lowerExpr_arrLit (ty : Ty) (exprs : List Expr)
    (children : OperandRun (lowerExprs exprs)) : OperandRun (lowerExpr (.arrLit ty exprs)) := by
  exact children.emitDefAfterValues (values_lowerExprs exprs) (by simp [Op.uses])

theorem operands_lowerExpr_structLit (ty : Ty) (exprs : List Expr)
    (children : OperandRun (lowerExprs exprs)) : OperandRun (lowerExpr (.structLit ty exprs)) := by
  exact children.emitDefAfterValues (values_lowerExprs exprs) (by simp [Op.uses])

theorem operands_lowerExpr_len (view : View) (child : OperandRun (lowerView view)) :
    OperandRun (lowerExpr (.len view)) := by
  exact child.emitDefAfterValue (value_lowerView view) (by simp [Op.uses])

theorem operands_lowerExpr_pop (place : Place) (origin : OriginId)
    (child : OperandRun (lowerPlace place)) : OperandRun (lowerExpr (.pop place origin)) := by
  exact child.emitDefAfterValue (value_lowerPlace place) (by simp [Op.uses])

theorem operands_lowerExpr_un (op : UnOp) (expr : Expr) (origin : OriginId)
    (child : OperandRun (lowerExpr expr)) : OperandRun (lowerExpr (.un op expr origin)) := by
  apply child.emitDefAfterValueInspect (value_lowerExpr expr)
    (inspect := fun value => do pure (.un op (← intTyOf value) value (some origin)))
  · intro input le state
    simp only [bind_run, intTyOf_state, pure_run]
  · intro input le state value member
    simp only [bind_run, pure_run, Op.uses, List.mem_singleton] at member
    exact member

theorem operands_lowerExpr_bin (op : BinOp) (left right : Expr) (origin : OriginId)
    (first : OperandRun (lowerExpr left)) (second : OperandRun (lowerExpr right)) :
    OperandRun (lowerExpr (.bin op left right origin)) := by
  apply first.emitDefAfterTwo second (value_lowerExpr left) (value_lowerExpr right)
    (advB_lowerExpr right) (dead_lowerExpr right)
    (inspect := fun x y => do pure (.bin op (← intTyOf x) x y (some origin)))
  · intro x y le state
    simp only [bind_run, intTyOf_state, pure_run]
  · intro x y le state value member
    simpa [bind_run, pure_run, Op.uses] using member

theorem operands_freezeTo {mu : Mutability} {input : ValueId} {le before result after}
    (run : freezeTo mu input le before = (result, after)) (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → input < before.vals.size) : OperandBounds after := by
  rcases freezeTo_cases run with ⟨rfl, rfl⟩ | fresh
  · exact checked
  · apply operands_emitDef fresh checked
    simpa [Op.uses] using bounded

theorem operands_lowerExpr_ref (mu : Mutability) (place : Place)
    (child : OperandRun (lowerPlace place)) : OperandRun (lowerExpr (.ref mu place)) := by
  intro le before result after run checked
  obtain ⟨input, mid, placeRun, freeze⟩ := bind_eq.mp run
  exact operands_freezeTo freeze (child _ _ _ _ placeRun checked)
    (value_lowerPlace place _ _ _ _ placeRun)

theorem operands_lowerArg (arg : Arg)
    (child : match arg with
      | .byVal expr => OperandRun (lowerExpr expr)
      | .byRef _ place => OperandRun (lowerPlace place)) : OperandRun (lowerArg arg) := by
  cases arg with
  | byVal expr => exact child
  | byRef mu place => exact operands_lowerExpr_ref mu place child

theorem operands_lowerExprs (exprs : List Expr)
    (children : ∀ expr ∈ exprs, OperandRun (lowerExpr expr)) : OperandRun (lowerExprs exprs) := by
  induction exprs with
  | nil => exact OperandRun.pure _
  | cons expr rest ih =>
    exact OperandRun.bind (children expr (by simp)) fun _ =>
      OperandRun.bind (ih (by intro next member; exact children next (by simp [member])))
        fun _ => OperandRun.pure _

theorem operands_lowerArgs (args : List Arg)
    (children : ∀ arg ∈ args, OperandRun (lowerArg arg)) : OperandRun (lowerArgs args) := by
  induction args with
  | nil => exact OperandRun.pure _
  | cons arg rest ih =>
    exact OperandRun.bind (children arg (by simp)) fun _ =>
      OperandRun.bind (ih (by intro next member; exact children next (by simp [member])))
        fun _ => OperandRun.pure _

theorem operands_lowerExpr_call (context : ContextId) (args : List Arg) (origin : OriginId)
    (children : OperandRun (lowerArgs args)) :
    OperandRun (lowerExpr (.call context args origin)) := by
  intro le before result after run checked
  obtain ⟨inputs, mid, argsRun, value, emitted, emission, env, loaded, loading, remaining⟩ :=
    (by simpa only [lowerExpr, bind_eq] using run)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj loading
  have called := operands_emitDef emission (children _ _ _ _ argsRun checked)
    (by simpa [Op.uses] using values_lowerArgs args _ _ _ _ argsRun)
  cases noReturn : le.mod.noReturn context
  · simp only [noReturn, Bool.false_eq_true, ↓reduceIte] at remaining
    obtain ⟨_, rfl⟩ := pure_eq.mp remaining
    exact called
  · simp only [noReturn, ↓reduceIte, bind_eq] at remaining
    obtain ⟨_, closed, closing, pureRun⟩ := remaining
    obtain ⟨_, rfl⟩ := pure_eq.mp pureRun
    exact operands_emitTerm closing called (by simp [Term.uses])

theorem operands_coerceTo {target : Ty} {input : ValueId} {origin : OriginId}
    {le before result after}
    (run : coerceTo target input origin le before = (result, after))
    (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → input < before.vals.size) : OperandBounds after := by
  unfold coerceTo at run
  obtain ⟨ty, mid, typeRun, remaining⟩ := bind_eq.mp run
  have same := valTy_eq typeRun
  subst mid
  split at remaining
  · exact operands_emitDef remaining checked (by simpa [Op.uses] using bounded)
  · obtain ⟨view, emitted, emission, slice⟩ := bind_eq.mp remaining
    have viewed := operands_emitDef emission checked (by simpa [Op.uses] using bounded)
    exact operands_emitDef slice viewed
      (by simpa [Op.uses, Bnd.uses] using value_emitDef _ _ _ _ _ emission)
  · obtain ⟨_, rfl⟩ := pure_eq.mp remaining
    exact checked

end Goose.Lower.Validation
