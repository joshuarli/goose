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

theorem live_value_through {action : B α} (advances : AdvB action) (dead : DeadRun action)
    {le before result after value} (run : action le before = (result, after))
    (bounded : before.cur.isSome = true → value < before.vals.size)
    (live : after.cur.isSome = true) : value < after.vals.size :=
  Nat.lt_of_lt_of_le (bounded (live_before dead run live)) ((advances _ _ _ _ run).vals)

theorem operands_lowerExpr_push (place : Place) (expr : Expr) (origin : Option OriginId)
    (first : OperandRun (lowerPlace place)) (second : OperandRun (lowerExpr expr)) :
    OperandRun (lowerExpr (.push place expr origin)) := by
  apply first.emitDefAfterTwo second (value_lowerPlace place) (value_lowerExpr expr)
    (advB_lowerExpr expr) (dead_lowerExpr expr)
    (inspect := fun x y => pure (.push x y origin))
  · intros; rfl
  · intro x y le state value member
    simpa [pure_run, Op.uses] using member

theorem operands_lowerPlace_elem (view : View) (index : Expr) (origin : OriginId)
    (first : OperandRun (lowerView view)) (second : OperandRun (lowerExpr index)) :
    OperandRun (lowerPlace (.elem view index origin)) := by
  apply first.emitDefAfterTwo second (value_lowerView view) (value_lowerExpr index)
    (advB_lowerExpr index) (dead_lowerExpr index)
    (inspect := fun x y => pure (.indexChecked x y (some origin)))
  · intros; rfl
  · intro x y le state value member
    simpa [pure_run, Op.uses] using member

theorem operands_lowerExpr_cmp (op : CmpOp) (left right : Expr)
    (first : OperandRun (lowerExpr left)) (second : OperandRun (lowerExpr right)) :
    OperandRun (lowerExpr (.cmp op left right)) := by
  intro le before result after run checked
  obtain ⟨x, mid, leftRun, y, next, rightRun, ty, loaded, loading, emission⟩ :=
    (by simpa only [lowerExpr, bind_eq] using run)
  have same := valTy_eq loading
  subst loaded
  have bounds : ∀ value, value = x ∨ value = y →
      next.cur.isSome = true → value < next.vals.size := by
    intro value either live
    rcases either with rfl | rfl
    · exact live_value_through (advB_lowerExpr right) (dead_lowerExpr right) rightRun
        (value_lowerExpr left _ _ _ _ leftRun) live
    · exact value_lowerExpr right _ _ _ _ rightRun live
  cases ty with
  | data ty =>
    cases ty <;> apply operands_emitDef emission
      (second _ _ _ _ rightRun (first _ _ _ _ leftRun checked)) <;>
      simpa [Op.uses] using (fun live value member => bounds value member live)
  | view _ _ =>
    apply operands_emitDef emission (second _ _ _ _ rightRun (first _ _ _ _ leftRun checked))
    simpa [Op.uses] using (fun live value member => bounds value member live)

theorem operands_lowerExpr_conv (kind : ConvKind) (target : Ty) (expr : Expr) (origin : OriginId)
    (child : OperandRun (lowerExpr expr)) :
    OperandRun (lowerExpr (.conv kind target expr origin)) := by
  apply child.emitDefAfterValueInspect (value_lowerExpr expr)
    (inspect := fun value => do
      let source ← intTyOf value
      pure (.conv kind source (match target with | .int dest => dest | _ => source) value (some origin)))
  · intro input le state
    simp only [bind_run, intTyOf_state, pure_run]
  · intro input le state value member
    simpa only [bind_run, pure_run, Op.uses, List.mem_singleton] using member

theorem operands_lowerBound (bound : Bound)
    (child : match bound with
      | .omitted => True
      | .expr expr | .fromEnd expr => OperandRun (lowerExpr expr)) :
    OperandRun (lowerBound bound) := by
  cases bound with
  | omitted => exact OperandRun.pure _
  | expr expr | fromEnd expr => exact OperandRun.bind child fun _ => OperandRun.pure _

theorem operands_lowerExpr_slice (mu : Mutability) (view : View) (lo hi : Bound) (origin : OriginId)
    (first : OperandRun (lowerView view)) (low : OperandRun (lowerBound lo))
    (high : OperandRun (lowerBound hi)) : OperandRun (lowerExpr (.slice mu view lo hi origin)) := by
  intro le before result after run checked
  obtain ⟨input, viewed, viewRun, lower, lowed, lowRun, upper, highed, highRun, emission⟩ :=
    (by simpa only [lowerExpr, bind_eq] using run)
  apply operands_emitDef emission (high _ _ _ _ highRun
    (low _ _ _ _ lowRun (first _ _ _ _ viewRun checked)))
  intro live value member
  simp only [Op.uses, List.mem_cons, List.mem_append] at member
  rcases member with rfl | lowMember | highMember
  · exact live_value_through (advB_lowerBound hi) (dead_lowerBound hi) highRun
      (live_value_through (advB_lowerBound lo) (dead_lowerBound lo) lowRun
        (value_lowerView view _ _ _ _ viewRun)) live
  · exact live_value_through (advB_lowerBound hi) (dead_lowerBound hi) highRun
      (fun liveLow => values_lowerBound lo lowRun liveLow value lowMember) live
  · exact values_lowerBound hi highRun live value highMember

theorem operands_patchTerm {block : BlockId} {term : Term} {le before result after}
    (run : patchTerm block term le before = (result, after)) (checked : OperandBounds before)
    (bounded : ∀ value ∈ term.uses, value < before.vals.size) : OperandBounds after := by
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact operands_appendInst checked block (.term term) bounded

theorem operands_setCur (current : Option BlockId) : OperandRun (setCur current) := by
  apply OperandRun.of_unchanged <;> intros <;> rw [setCur_run]
  · rfl
  · exact Nat.le_refl _

theorem operands_read : OperandRun (read : B LEnv) := by
  exact OperandRun.of_unchanged (by intros; rfl) (by intros; exact Nat.le_refl _)

theorem operands_get : OperandRun (get : B LS) := by
  exact OperandRun.of_unchanged (by intros; rfl) (by intros; exact Nat.le_refl _)

theorem operands_curBlock : OperandRun curBlock := by
  exact OperandRun.of_unchanged (by intros; rw [curBlock_run]) (by intros; rw [curBlock_run]; exact Nat.le_refl _)

theorem OperandRun.inScope (scope : ScopeId) {action : B α} (child : OperandRun action) :
    OperandRun (inScope scope action) := by
  intro le before result after run checked
  obtain ⟨mid, actionRun, rfl⟩ := inScope_eq run
  exact child le _ result mid actionRun checked

theorem operands_patchBrs (target : BlockId) :
    ∀ incoming le before result after, patchBrs target incoming le before = (result, after) →
      OperandBounds before →
      (∀ pair ∈ incoming, pair.2 < before.vals.size) → OperandBounds after
  | [], le, before, result, after, run, checked, _ => by
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  | (block, value) :: rest, le, before, result, after, run, checked, bounded => by
    obtain ⟨_, mid, patch, tail⟩ := bind_eq.mp run
    have next := operands_patchTerm patch checked (by simpa [Term.uses] using bounded (block, value) (by simp))
    have same : mid.vals = before.vals := by
      rw [patchTerm_run] at patch
      exact congrArg (fun pair => pair.2.vals) patch.symm
    exact operands_patchBrs target rest _ _ _ _ tail next (by
      intro pair member
      rw [same]
      exact bounded pair (by simp [member]))

theorem operands_joinValue {endT endF : Option BlockId} {vt vf : ValueId} {le before result after}
    (run : joinValue endT vt endF vf le before = (result, after)) (checked : OperandBounds before)
    (trueBound : endT.isSome = true → vt < before.vals.size)
    (falseBound : endF.isSome = true → vf < before.vals.size) : OperandBounds after := by
  unfold joinValue at run
  cases endT <;> cases endF
  · obtain ⟨_, mid, change, remaining⟩ := bind_eq.mp run
    obtain ⟨_, rfl⟩ := pure_eq.mp remaining
    exact operands_setCur _ _ _ _ _ change checked
  all_goals
    simp only [bind_eq] at run
    obtain ⟨ty, mid, typeRun, ⟨block, params⟩, allocated, allocation,
      _, patched, patch, _, resumed, resume, pureRun⟩ := run
    have same := valTy_eq typeRun
    subst mid
    have allocatedBounds := operands_newBlock _ _ _ _ _ allocation checked
    have growth := (adv_newBlock1 allocation).vals
    have patchedBounds := operands_patchBrs _ _ _ _ _ _ patch allocatedBounds (by
      intro pair member
      simp at member
      rcases member with rfl | rfl <;>
        first
        | exact Nat.lt_of_lt_of_le (trueBound rfl) growth
        | exact Nat.lt_of_lt_of_le (falseBound rfl) growth)
    obtain ⟨_, rfl⟩ := pure_eq.mp pureRun
    exact operands_setCur _ _ _ _ _ resume patchedBounds

theorem operands_fork {condition : ValueId} {le before result after}
    (run : fork condition le before = (result, after)) (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → condition < before.vals.size) : OperandBounds after := by
  obtain ⟨⟨left, _⟩, first, allocateLeft, ⟨right, _⟩, second, allocateRight,
    _, closed, closing, remaining⟩ := (by simpa only [fork, bind_eq] using run)
  have firstBounds := operands_newBlock _ _ _ _ _ allocateLeft checked
  have secondBounds := operands_newBlock _ _ _ _ _ allocateRight firstBounds
  rw [newBlock0_run] at allocateLeft allocateRight
  obtain ⟨_, rfl⟩ := Prod.mk.inj allocateLeft
  obtain ⟨_, rfl⟩ := Prod.mk.inj allocateRight
  obtain ⟨_, rfl⟩ := pure_eq.mp remaining
  exact operands_emitTerm closing secondBounds (by simpa [Term.uses] using bounded)

theorem operands_scFork {isAnd : Bool} {condition : ValueId} {le before result after}
    (run : scFork isAnd condition le before = (result, after)) (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → condition < before.vals.size) : OperandBounds after := by
  unfold scFork at run
  obtain ⟨⟨right, _⟩, first, allocateRight, ⟨join, params⟩, second, allocateJoin, remaining⟩ :=
    (by simpa only [bind_eq] using run)
  have firstBounds := operands_newBlock _ _ _ _ _ allocateRight checked
  have secondBounds := operands_newBlock _ _ _ _ _ allocateJoin firstBounds
  rw [newBlock0_run] at allocateRight
  obtain ⟨_, rfl⟩ := Prod.mk.inj allocateRight
  rw [newBlock1_run] at allocateJoin
  obtain ⟨_, rfl⟩ := Prod.mk.inj allocateJoin
  cases isAnd <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_eq] at remaining <;>
    obtain ⟨_, closed, closing, pureRun⟩ := remaining <;>
    obtain ⟨_, rfl⟩ := pure_eq.mp pureRun <;>
    apply operands_emitTerm closing secondBounds <;>
    intro live value member <;>
    simp [Term.uses] at member <;>
    subst value <;>
    simpa using Nat.lt_succ_of_lt (bounded live)

theorem operands_shortCircuit {isAnd : Bool} {condition : ValueId} {rhs : B ValueId}
    (child : OperandRun rhs) (valueBound : ValueRun rhs) {le before result after}
    (run : shortCircuit isAnd condition rhs le before = (result, after))
    (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → condition < before.vals.size) : OperandBounds after := by
  cases current : before.cur with
  | none =>
    rw [shortCircuit, whenLive_none _ _ le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [shortCircuit, whenLive_some _ _ le current] at run
    obtain ⟨⟨right, join, param⟩, forked, forkRun, _, selected, select,
      value, evaluated, evaluate, _, closed, close, _, resumed, resume, pureRun⟩ :=
      (by simpa only [bind_eq] using run)
    have forkedBounds := operands_scFork forkRun checked bounded
    have selectedBounds := operands_setCur _ _ _ _ _ select forkedBounds
    have evaluatedBounds := child _ _ _ _ evaluate selectedBounds
    have closedBounds := operands_emitTerm close evaluatedBounds
      (by simpa [Term.uses] using valueBound _ _ _ _ evaluate)
    obtain ⟨_, rfl⟩ := pure_eq.mp pureRun
    exact operands_setCur _ _ _ _ _ resume closedBounds

theorem operands_lowerExpr_shortCircuit (isAnd : Bool) (left right : Expr)
    (first : OperandRun (lowerExpr left)) (second : OperandRun (lowerExpr right)) :
    OperandRun (do let condition ← lowerExpr left; shortCircuit isAnd condition (lowerExpr right)) := by
  intro le before result after run checked
  obtain ⟨condition, mid, leftRun, remaining⟩ := bind_eq.mp run
  exact operands_shortCircuit second (value_lowerExpr right) remaining
    (first _ _ _ _ leftRun checked) (value_lowerExpr left _ _ _ _ leftRun)

theorem operands_lowerExpr_ifE (condition : Expr) (trueArm falseArm : Core.Block)
    (conditionRun : OperandRun (lowerExpr condition))
    (trueRun : OperandRun (lowerBlock none [] true trueArm))
    (falseRun : OperandRun (lowerBlock none [] true falseArm)) :
    OperandRun (lowerExpr (.ifE condition trueArm falseArm)) := by
  intro le before result after run checked
  obtain ⟨cv, tested, testRun, remaining⟩ := bind_eq.mp run
  have testedBounds := conditionRun _ _ _ _ testRun checked
  cases current : tested.cur with
  | none =>
    rw [whenLive_none _ _ le current] at remaining
    obtain ⟨_, rfl⟩ := Prod.mk.inj remaining
    exact testedBounds
  | some block =>
    rw [whenLive_some _ _ le current] at remaining
    obtain ⟨⟨left, right⟩, forked, forkRun, _, selectedT, selectT,
      vt, trueEnd, runT, endT, savedT, saveT, _, selectedF, selectF,
      vf, falseEnd, runF, endF, savedF, saveF, joinRun⟩ :=
      (by simpa only [bind_eq] using remaining)
    have forkedBounds := operands_fork forkRun testedBounds
      (value_lowerExpr condition _ _ _ _ testRun)
    have selectedTBounds := operands_setCur _ _ _ _ _ selectT forkedBounds
    have trueEndBounds := trueRun _ _ _ _ runT selectedTBounds
    rw [curBlock_run] at saveT saveF
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveT
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveF
    have selectedFBounds := operands_setCur _ _ _ _ _ selectF trueEndBounds
    have falseEndBounds := falseRun _ _ _ _ runF selectedFBounds
    apply operands_joinValue joinRun falseEndBounds
    · intro live
      have firstBound := value_lowerBlock none [] trueArm _ _ _ _ runT live
      have growth := (advB_lowerBlock none [] true falseArm _ _ _ _ runF).vals
      rw [setCur_run] at selectF
      obtain ⟨_, rfl⟩ := Prod.mk.inj selectF
      exact Nat.lt_of_lt_of_le firstBound growth
    · exact value_lowerBlock none [] falseArm _ _ _ _ runF

end Goose.Lower.Validation
