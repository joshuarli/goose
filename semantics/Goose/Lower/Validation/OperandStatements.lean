import Goose.Lower.Validation.OperandBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def LoopOperandBounds (context : Option LoopCtx) (state : LS) : Prop :=
  match context with
  | some ⟨_, _, .next _ _ value⟩ => value < state.vals.size
  | _ => True

theorem LoopOperandBounds.mono {context : Option LoopCtx} {before after : LS}
    (bounded : LoopOperandBounds context before) (growth : before.vals.size ≤ after.vals.size) :
    LoopOperandBounds context after := by
  cases context with
  | none => trivial
  | some context =>
    obtain ⟨depth, target, kind⟩ := context
    cases kind <;> simp only [LoopOperandBounds] at bounded ⊢
    exact Nat.lt_of_lt_of_le bounded growth

def PreOperandBounds (pre : List (SlotId × ValueId × OriginId)) (state : LS) : Prop :=
  ∀ binding ∈ pre, binding.2.1 < state.vals.size

theorem operands_initSlots : ∀ pre le before result after,
    initSlots pre le before = (result, after) → OperandBounds before →
      PreOperandBounds pre before → OperandBounds after
  | [], le, before, result, after, run, checked, _ => by
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  | (slot, value, origin) :: rest, le, before, result, after, run, checked, bounded => by
    obtain ⟨_, mid, emission, remaining⟩ := bind_eq.mp run
    have next := operands_emitEffect emission checked
      (by simpa [Effect.uses] using (fun _ => bounded (slot, value, origin) (by simp)))
    apply operands_initSlots rest _ _ _ _ remaining next
    intro binding member
    exact Nat.lt_of_lt_of_le (bounded binding (by simp [member]))
      ((advB_emitEffect _ _ _ _ _ emission).vals)

theorem operands_leaveAll (scopes : List ScopeId) : OperandRun (leaveAll scopes) := by
  induction scopes with
  | nil => exact OperandRun.pure _
  | cons scope rest ih =>
    apply OperandRun.bind (action := emitEffect (.leave scope))
    · intro le before result after run checked
      exact operands_emitEffect run checked (by simp [Effect.uses])
    · intro _; exact ih

theorem operands_leaveTo (depth : Nat) : OperandRun (leaveTo depth) := by
  exact OperandRun.bind operands_get fun state => operands_leaveAll _

theorem operands_coerceSlot {slot : SlotId} {input : ValueId} {origin : OriginId}
    {le before result after}
    (run : coerceSlot slot input origin le before = (result, after))
    (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → input < before.vals.size) : OperandBounds after := by
  unfold coerceSlot at run
  simp only [bind_run, read_apply] at run
  cases destination : le.slots[slot]? with
  | none =>
    simp only [destination] at run
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  | some destination =>
    simp only [destination] at run
    exact operands_coerceTo run checked bounded

theorem operands_coerceResult {input : ValueId} {origin : OriginId} {le before result after}
    (run : coerceResult input origin le before = (result, after))
    (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → input < before.vals.size) : OperandBounds after := by
  unfold coerceResult at run
  simp only [bind_run, read_apply] at run
  cases destination : le.results.head? with
  | none =>
    simp only [destination] at run
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  | some destination =>
    simp only [destination] at run
    exact operands_coerceTo run checked bounded

theorem value_coerceTo {target : Ty} {input : ValueId} {origin : OriginId} {le before result after}
    (run : coerceTo target input origin le before = (result, after))
    (bounded : before.cur.isSome = true → input < before.vals.size)
    (live : after.cur.isSome = true) : result < after.vals.size := by
  unfold coerceTo at run
  obtain ⟨ty, mid, typeRun, remaining⟩ := bind_eq.mp run
  have same := valTy_eq typeRun
  subst mid
  split at remaining
  · exact value_emitDef _ _ _ _ _ remaining live
  · obtain ⟨view, emitted, emission, slice⟩ := bind_eq.mp remaining
    exact value_emitDef _ _ _ _ _ slice live
  · obtain ⟨rfl, rfl⟩ := pure_eq.mp remaining
    exact bounded live

theorem value_coerceSlot {slot : SlotId} {input : ValueId} {origin : OriginId} {le before result after}
    (run : coerceSlot slot input origin le before = (result, after))
    (bounded : before.cur.isSome = true → input < before.vals.size)
    (live : after.cur.isSome = true) : result < after.vals.size := by
  unfold coerceSlot at run
  simp only [bind_run, read_apply] at run
  cases destination : le.slots[slot]? with
  | none =>
    simp only [destination] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact bounded live
  | some destination =>
    simp only [destination] at run
    exact value_coerceTo run bounded live

theorem OperandRun.emitEffectAfterValue {action : B ValueId} {effect : ValueId → Effect}
    (first : OperandRun action) (bounded : ValueRun action)
    (uses : ∀ input value, value ∈ (effect input).uses → value = input) :
    OperandRun (do let input ← action; emitEffect (effect input)) := by
  intro le before result after run checked
  obtain ⟨input, mid, firstRun, emission⟩ := bind_eq.mp run
  apply operands_emitEffect emission (first _ _ _ _ firstRun checked)
  intro live value member
  rw [uses input value member]
  exact bounded _ _ _ _ firstRun live

theorem OperandRun.emitEffectAfterTwo {left right : B ValueId} {effect : ValueId → ValueId → Effect}
    (first : OperandRun left) (second : OperandRun right)
    (leftBound : ValueRun left) (rightBound : ValueRun right)
    (rightAdvances : AdvB right) (rightDead : DeadRun right)
    (uses : ∀ x y value, value ∈ (effect x y).uses → value = x ∨ value = y) :
    OperandRun (do let x ← left; let y ← right; emitEffect (effect x y)) := by
  intro le before result after run checked
  obtain ⟨x, mid, firstRun, y, next, secondRun, emission⟩ :=
    (by simpa only [bind_eq] using run)
  apply operands_emitEffect emission (second _ _ _ _ secondRun (first _ _ _ _ firstRun checked))
  intro live value member
  rcases uses x y value member with rfl | rfl
  · exact live_value_through rightAdvances rightDead secondRun
      (leftBound _ _ _ _ firstRun) live
  · exact rightBound _ _ _ _ secondRun live

theorem operands_lowerStmt_assign (context : Option LoopCtx) (place : Place) (expr : Expr)
    (origin : OriginId) (first : OperandRun (lowerPlace place))
    (second : OperandRun (lowerExpr expr)) : OperandRun (lowerStmt context (.assign place expr origin)) := by
  exact first.emitEffectAfterTwo second (value_lowerPlace place) (value_lowerExpr expr)
    (advB_lowerExpr expr) (dead_lowerExpr expr) (by simp [Effect.uses])

theorem operands_lowerStmt_append (context : Option LoopCtx) (place : Place) (view : View)
    (origin : OriginId) (first : OperandRun (lowerPlace place))
    (second : OperandRun (lowerView view)) : OperandRun (lowerStmt context (.append place view origin)) := by
  exact first.emitEffectAfterTwo second (value_lowerPlace place) (value_lowerView view)
    (advB_lowerView view) (dead_lowerView view) (by simp [Effect.uses])

theorem operands_lowerStmt_popN (context : Option LoopCtx) (place : Place) (expr : Expr)
    (origin : OriginId) (first : OperandRun (lowerPlace place))
    (second : OperandRun (lowerExpr expr)) : OperandRun (lowerStmt context (.popN place expr origin)) := by
  exact first.emitEffectAfterTwo second (value_lowerPlace place) (value_lowerExpr expr)
    (advB_lowerExpr expr) (dead_lowerExpr expr) (by simp [Effect.uses])

theorem operands_lowerStmt_clear (context : Option LoopCtx) (place : Place) (origin : OriginId)
    (child : OperandRun (lowerPlace place)) : OperandRun (lowerStmt context (.clear place origin)) := by
  exact child.emitEffectAfterValue (value_lowerPlace place) (by simp [Effect.uses])

theorem operands_lowerStmt_expr (context : Option LoopCtx) (expr : Expr) (origin : OriginId)
    (child : OperandRun (lowerExpr expr)) : OperandRun (lowerStmt context (.expr expr origin)) := by
  exact OperandRun.bind child fun _ => OperandRun.pure _

theorem operands_lowerStmt_letS (context : Option LoopCtx) (slot : SlotId) (expr : Expr)
    (origin : OriginId) (child : OperandRun (lowerExpr expr)) :
    OperandRun (lowerStmt context (.letS slot expr origin)) := by
  intro le before result after run checked
  obtain ⟨input, evaluated, expression, coerced, converted, conversion, emission⟩ :=
    (by simpa only [lowerStmt, bind_eq] using run)
  have bound := value_lowerExpr expr _ _ _ _ expression
  have convertedBounds := operands_coerceSlot conversion (child _ _ _ _ expression checked) bound
  exact operands_emitEffect emission convertedBounds
    (by simpa [Effect.uses] using value_coerceSlot conversion bound)

theorem operands_lowerStmt_exit (context : Option LoopCtx) (expr : Expr) (origin : OriginId)
    (child : OperandRun (lowerExpr expr)) : OperandRun (lowerStmt context (.exit expr origin)) := by
  intro le before result after run checked
  obtain ⟨input, mid, expression, emission⟩ := bind_eq.mp run
  exact operands_emitTerm emission (child _ _ _ _ expression checked)
    (by simpa [Term.uses] using value_lowerExpr expr _ _ _ _ expression)

theorem dead_leaveAll (scopes : List ScopeId) : DeadRun (leaveAll scopes) := by
  induction scopes with
  | nil => exact DeadRun.pure _
  | cons scope rest ih => exact DeadRun.bind (dead_emitEffect _) fun _ => ih

theorem dead_leaveTo (depth : Nat) : DeadRun (leaveTo depth) := by
  apply DeadRun.bind
  · exact DeadRun.of_cur_unchanged (by intros; rfl)
  · intro state; exact dead_leaveAll _

theorem value_coerceResult {input : ValueId} {origin : OriginId} {le before result after}
    (run : coerceResult input origin le before = (result, after))
    (bounded : before.cur.isSome = true → input < before.vals.size)
    (live : after.cur.isSome = true) : result < after.vals.size := by
  unfold coerceResult at run
  simp only [bind_run, read_apply] at run
  cases destination : le.results.head? with
  | none =>
    simp only [destination] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact bounded live
  | some destination =>
    simp only [destination] at run
    exact value_coerceTo run bounded live

theorem operands_lowerStmt_brk (context : Option LoopCtx) (origin : OriginId) :
    OperandRun (lowerStmt context (.brk origin)) := by
  cases context with
  | none => exact OperandRun.pure _
  | some context =>
    apply OperandRun.bind (operands_leaveTo _)
    intro _ le before result after run checked
    exact operands_emitTerm run checked (by simp [Term.uses])

theorem operands_lowerStmt_cont (context : Option LoopCtx) (origin : OriginId)
    {le before result after} (run : lowerStmt context (.cont origin) le before = (result, after))
    (checked : OperandBounds before) (counter : LoopOperandBounds context before) :
    OperandBounds after := by
  cases context with
  | none =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  | some context =>
    obtain ⟨depth, exit, kind⟩ := context
    obtain ⟨_, mid, leave, remaining⟩ := bind_eq.mp run
    have left := operands_leaveTo _ _ _ _ _ leave checked
    cases kind with
    | jump header => exact operands_emitTerm remaining left (by simp [Term.uses])
    | next header ty value =>
      have bound : value < mid.vals.size :=
        Nat.lt_of_lt_of_le counter ((advB_leaveTo depth _ _ _ _ leave).vals)
      obtain ⟨next, emitted, emission, term⟩ := bind_eq.mp remaining
      have nextBounds := operands_emitDef emission left (by simpa [Op.uses] using (fun _ => bound))
      exact operands_emitTerm term nextBounds
        (by simpa [Term.uses] using value_emitDef _ _ _ _ _ emission)

theorem operands_lowerStmt_ret (context : Option LoopCtx) (expr : Option Expr) (origin : OriginId)
    (child : ∀ value, expr = some value → OperandRun (lowerExpr value)) :
    OperandRun (lowerStmt context (.ret expr origin)) := by
  intro le before result after run checked
  cases expr with
  | none =>
    obtain ⟨values, prepared, prepare, _, left, leave, emission⟩ :=
      (by simpa only [lowerStmt, bind_eq] using run)
    obtain ⟨rfl, rfl⟩ := pure_eq.mp prepare
    exact operands_emitTerm emission (operands_leaveTo _ _ _ _ _ leave checked)
      (by simp [Term.uses])
  | some expr =>
    obtain ⟨input, evaluated, expression, converted, coerced, coercion,
      values, prepared, prepare, _, left, leave, emission⟩ :=
      (by simpa only [lowerStmt, bind_eq] using run)
    obtain ⟨rfl, rfl⟩ := pure_eq.mp prepare
    have bound := value_lowerExpr expr _ _ _ _ expression
    have ready := operands_coerceResult coercion (child expr rfl _ _ _ _ expression checked) bound
    apply operands_emitTerm emission (operands_leaveTo _ _ _ _ _ leave ready)
    intro live value member
    have equality : value = converted := by simpa [Term.uses] using member
    subst value
    exact live_value_through (advB_leaveTo 0) (dead_leaveTo 0) leave
      (value_coerceResult coercion bound) live

theorem operands_lowerStmt_rebind (context : Option LoopCtx) (slot : SlotId) (expr : Expr)
    (origin : OriginId) (child : OperandRun (lowerExpr expr)) :
    OperandRun (lowerStmt context (.rebind slot expr origin)) := by
  intro le before result after run checked
  obtain ⟨input, evaluated, expression, converted, coerced, coercion,
    address, addressed, allocation, emission⟩ :=
    (by simpa only [lowerStmt, bind_eq] using run)
  have bound := value_lowerExpr expr _ _ _ _ expression
  have convertedBounds := operands_coerceSlot coercion (child _ _ _ _ expression checked) bound
  have addressedBounds := operands_emitDef allocation convertedBounds (by simp [Op.uses])
  apply operands_emitEffect emission addressedBounds
  intro live value member
  have either : value = address ∨ value = converted := by simpa [Effect.uses] using member
  rcases either with rfl | rfl
  · exact value_emitDef _ _ _ _ _ allocation live
  · exact live_value_through (advB_emitDef _) (dead_emitDef _) allocation
      (value_coerceSlot coercion bound) live

theorem operands_lowerStmt_assignWhole (context : Option LoopCtx) (place : Place) (expr : Expr)
    (origin : OriginId) (first : OperandRun (lowerPlace place))
    (second : OperandRun (lowerExpr expr)) :
    OperandRun (lowerStmt context (.assignWhole place expr origin)) := by
  intro le before result after run checked
  obtain ⟨address, addressed, placeRun, _, cleared, clear, replacement, evaluated, expression, emission⟩ :=
    (by simpa only [lowerStmt, bind_eq] using run)
  have bound := value_lowerPlace place _ _ _ _ placeRun
  have clearedBounds := operands_emitEffect clear (first _ _ _ _ placeRun checked)
    (by simpa [Effect.uses] using bound)
  apply operands_emitEffect emission (second _ _ _ _ expression clearedBounds)
  intro live value member
  have either : value = address ∨ value = replacement := by simpa [Effect.uses] using member
  rcases either with rfl | rfl
  · exact live_value_through (advB_lowerExpr expr) (dead_lowerExpr expr) expression
      (live_value_through (advB_emitEffect _) (dead_emitEffect _) clear bound) live
  · exact value_lowerExpr expr _ _ _ _ expression live

theorem operands_lowerStmt_assignOp (context : Option LoopCtx) (op : BinOp) (place : Place) (expr : Expr)
    (origin : OriginId) (first : OperandRun (lowerPlace place))
    (second : OperandRun (lowerExpr expr)) :
    OperandRun (lowerStmt context (.assignOp op place expr origin)) := by
  intro le before result after run checked
  obtain ⟨address, addressed, placeRun, old, loaded, load, rhs, evaluated, expression,
    ty, inspected, inspection, value, emitted, binary, emission⟩ :=
    (by simpa only [lowerStmt, bind_eq] using run)
  have same : inspected = evaluated := by
    have equality := intTyOf_state old le evaluated
    rw [inspection] at equality
    exact equality
  subst inspected
  have addressBound := value_lowerPlace place _ _ _ _ placeRun
  have loadedBounds := operands_emitDef load (first _ _ _ _ placeRun checked)
    (by simpa [Op.uses] using addressBound)
  have oldBound := value_emitDef _ _ _ _ _ load
  have evaluatedBounds := second _ _ _ _ expression loadedBounds
  have binaryBounds := operands_emitDef binary evaluatedBounds (by
    intro live used member
    have either : used = old ∨ used = rhs := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact live_value_through (advB_lowerExpr expr) (dead_lowerExpr expr) expression oldBound live
    · exact value_lowerExpr expr _ _ _ _ expression live)
  apply operands_emitEffect emission binaryBounds
  intro live used member
  have either : used = address ∨ used = value := by simpa [Effect.uses] using member
  rcases either with rfl | rfl
  · exact live_value_through (advB_emitDef _) (dead_emitDef _) binary
      (live_value_through (advB_lowerExpr expr) (dead_lowerExpr expr) expression
        (live_value_through (advB_emitDef _) (dead_emitDef _) load addressBound)) live
  · exact value_emitDef _ _ _ _ _ binary live

theorem operands_lowerStmt_resize (context : Option LoopCtx) (place : Place) (size : Expr)
    (fill : Option Expr) (origin : OriginId) (first : OperandRun (lowerPlace place))
    (second : OperandRun (lowerExpr size))
    (third : ∀ expr, fill = some expr → OperandRun (lowerExpr expr)) :
    OperandRun (lowerStmt context (.resize place size fill origin)) := by
  intro le before result after run checked
  cases fill with
  | none =>
    simp only [lowerStmt] at run
    obtain ⟨address, addressed, placeRun, remaining⟩ := bind_eq.mp run
    obtain ⟨count, evaluated, sizeRun, remaining⟩ := bind_eq.mp remaining
    have sizeBounds := second _ _ _ _ sizeRun (first _ _ _ _ placeRun checked)
    have addressBound := live_value_through (advB_lowerExpr size) (dead_lowerExpr size) sizeRun
      (value_lowerPlace place _ _ _ _ placeRun)
    have sizeBound := value_lowerExpr size _ _ _ _ sizeRun
    obtain ⟨option, prepared, prepare, emission⟩ := bind_eq.mp remaining
    obtain ⟨rfl, rfl⟩ := pure_eq.mp prepare
    apply operands_emitEffect emission sizeBounds
    intro live value member
    have either : value = address ∨ value = count := by simpa [Effect.uses] using member
    rcases either with rfl | rfl
    · exact addressBound live
    · exact sizeBound live
  | some expr =>
    simp only [lowerStmt] at run
    obtain ⟨address, addressed, placeRun, remaining⟩ := bind_eq.mp run
    obtain ⟨count, evaluated, sizeRun, remaining⟩ := bind_eq.mp remaining
    have sizeBounds := second _ _ _ _ sizeRun (first _ _ _ _ placeRun checked)
    have addressBound := live_value_through (advB_lowerExpr size) (dead_lowerExpr size) sizeRun
      (value_lowerPlace place _ _ _ _ placeRun)
    have sizeBound := value_lowerExpr size _ _ _ _ sizeRun

    obtain ⟨input, filled, fillRun, option, prepared, prepare, emission⟩ :=
      (by simpa only [bind_eq] using remaining)
    obtain ⟨rfl, rfl⟩ := pure_eq.mp prepare
    apply operands_emitEffect emission (third expr rfl _ _ _ _ fillRun sizeBounds)
    intro live value member
    have either : value = address ∨ value = count ∨ value = input := by
      simpa [Effect.uses] using member
    rcases either with rfl | rfl | rfl
    · exact live_value_through (advB_lowerExpr expr) (dead_lowerExpr expr) fillRun addressBound live
    · exact live_value_through (advB_lowerExpr expr) (dead_lowerExpr expr) fillRun sizeBound live
    · exact value_lowerExpr expr _ _ _ _ fillRun live

theorem dead_lowerPrintArgs : ∀ args, DeadRun (lowerPrintArgs args)
  | [] => DeadRun.pure _
  | .text _ :: rest => DeadRun.bind (dead_lowerPrintArgs rest) fun _ => DeadRun.pure _
  | .expr expr :: rest => DeadRun.bind (dead_lowerExpr expr) fun _ =>
      DeadRun.bind (dead_lowerPrintArgs rest) fun _ => DeadRun.pure _

theorem operands_lowerPrintArgs (args : List PrintArg)
    (children : ∀ expr, PrintArg.expr expr ∈ args → OperandRun (lowerExpr expr)) :
    OperandRun (lowerPrintArgs args) ∧
      (∀ le before parts after, lowerPrintArgs args le before = (parts, after) →
        after.cur.isSome = true → ∀ value ∈ parts.flatMap PrintPart.uses, value < after.vals.size) := by
  induction args with
  | nil =>
    exact ⟨OperandRun.pure _, by
      intro le before parts after run live value member
      obtain ⟨rfl, rfl⟩ := pure_eq.mp run
      simp at member⟩
  | cons arg rest ih =>
    have tail := ih (by intro expr member; exact children expr (by simp [member]))
    cases arg with
    | text text =>
      refine ⟨OperandRun.bind tail.1 (fun _ => OperandRun.pure _), ?_⟩
      intro le before parts after run live value member
      obtain ⟨parts, mid, restRun, pureRun⟩ := bind_eq.mp run
      obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
      exact tail.2 _ _ _ _ restRun live value (by simpa [PrintPart.uses] using member)
    | expr expr =>
      refine ⟨OperandRun.bind (children expr (by simp)) (fun _ =>
        OperandRun.bind tail.1 (fun _ => OperandRun.pure _)), ?_⟩
      intro le before parts after run live value member
      obtain ⟨input, evaluated, exprRun, parts, prepared, partsRun, pureRun⟩ :=
        (by simpa only [lowerPrintArgs, bind_eq] using run)
      obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
      have either : value = input ∨ value ∈ parts.flatMap PrintPart.uses := by
        simpa [PrintPart.uses] using member
      rcases either with rfl | member
      · exact live_value_through (advB_lowerPrintArgs rest) (dead_lowerPrintArgs rest) partsRun
          (value_lowerExpr expr _ _ _ _ exprRun) live
      · exact tail.2 _ _ _ _ partsRun live value member

theorem operands_lowerStmt_print (context : Option LoopCtx) (args : List PrintArg) (origin : OriginId)
    (children : ∀ expr, PrintArg.expr expr ∈ args → OperandRun (lowerExpr expr)) :
    OperandRun (lowerStmt context (.print args origin)) := by
  intro le before result after run checked
  obtain ⟨parts, mid, argsRun, emission⟩ := bind_eq.mp run
  have partsBounds := operands_lowerPrintArgs args children
  exact operands_emitEffect emission (partsBounds.1 _ _ _ _ argsRun checked)
    (by simpa [Effect.uses] using partsBounds.2 _ _ _ _ argsRun)

theorem operands_lowerBlock (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (want : Bool) (scope : ScopeId) (stmts : List Stmt) (tail : Option Expr)
    (stmtsRun : ∀ le before result after,
      lowerStmts context stmts le before = (result, after) → OperandBounds before →
        LoopOperandBounds context before → OperandBounds after)
    (tailRun : ∀ expr, tail = some expr → OperandRun (lowerExpr expr))
    {le before result after}
    (run : lowerBlock context pre want (.mk scope stmts tail) le before = (result, after))
    (checked : OperandBounds before) (counter : LoopOperandBounds context before)
    (preBounds : PreOperandBounds pre before) : OperandBounds after := by
  obtain ⟨_, entered, entry, innerRun⟩ := bind_eq.mp run
  have enteredBounds := operands_emitEffect entry checked (by simp [Effect.uses])
  have enterAdvance := advB_emitEffect _ _ _ _ _ entry
  obtain ⟨finished, bodyRun, rfl⟩ := inScope_eq innerRun
  obtain ⟨_, initialized, initialization, _, executed, execution,
    value, evaluated, evaluation, _, left, leave, pureRun⟩ :=
    (by simpa only [bind_eq] using bodyRun)
  have initialBounds := operands_initSlots pre _ _ _ _ initialization enteredBounds (by
    intro binding member
    exact Nat.lt_of_lt_of_le (preBounds binding member) enterAdvance.vals)
  have initializedAdvance := advB_initSlots pre _ _ _ _ initialization
  have executedBounds := stmtsRun _ _ _ _ execution initialBounds
    ((counter.mono enterAdvance.vals).mono initializedAdvance.vals)
  have evaluatedBounds : OperandBounds evaluated := by
    cases tail with
    | none =>
      cases want
      · obtain ⟨_, rfl⟩ := pure_eq.mp evaluation
        exact executedBounds
      · exact operands_emitDef evaluation executedBounds (by simp [Op.uses])
    | some expr => exact tailRun expr rfl _ _ _ _ evaluation executedBounds
  have leftBounds := operands_emitEffect leave evaluatedBounds (by simp [Effect.uses])
  obtain ⟨_, rfl⟩ := pure_eq.mp pureRun
  exact leftBounds

end Goose.Lower.Validation
