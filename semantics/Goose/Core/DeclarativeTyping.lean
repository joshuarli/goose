import Goose.Core.DeclarativeTables

namespace Goose.Core
namespace Declarative

abbrev Judgment (α : Type) := α → Prop

instance : Monad Judgment where
  pure a := fun b => b = a
  bind a f := fun b => ∃ x, a x ∧ f x b

instance : LawfulMonad Judgment := LawfulMonad.mk' Judgment
  (by intro α value; funext result; simp [Functor.map, instMonadJudgment])
  (by intro α β value next; funext result; simp [bind, pure, instMonadJudgment])
  (by
    intro α β γ value first second
    funext result
    apply propext
    change (∃ middle, (∃ initial, value initial ∧ first initial middle) ∧ second middle result) ↔
      ∃ initial, value initial ∧ ∃ middle, first initial middle ∧ second middle result
    constructor
    · rintro ⟨middle, ⟨initial, present, firstStep⟩, secondStep⟩
      exact ⟨initial, present, middle, firstStep, secondStep⟩
    · rintro ⟨initial, present, middle, firstStep, secondStep⟩
      exact ⟨middle, ⟨initial, present, firstStep⟩, secondStep⟩)

private def impossible : Judgment α := fun _ => False
abbrev Typing := StateT Nat Judgment

private def impossibleTyping : Typing α := fun _ _ => False

def referenceCapabilities (p : Place) (info : PlaceInfo) : Typing Unit :=
  unless info.canReference p do impossibleTyping

def resolved (env : TEnv) (type : Ty) : Typing Unit :=
  fun state result => Goose.Core.ResolvedType env.mod type ∧ result = ((), state)

def shrinkProfile (env : TEnv) : Typing Unit :=
  unless env.mod.profile == .shrink do impossibleTyping

def ownerElement (env : TEnv) (t : Ty) : Typing Ty := do
  resolved env t
  match t.ownerElem? with
  | some e => pure e
  | none => impossibleTyping

def freshOwner (env : TEnv) (e : Expr) (t : Ty) : Typing Unit :=
  if env.mod.profile == .shrink && t.ownerElem?.isSome && !e.freshOwner then
    impossibleTyping
  else pure ()

def recordType (env : TEnv) (t : Ty) : Typing StructDef := do
  unless env.mod.profile == .shrink do impossibleTyping
  match t with
  | .structT sid _ =>
    unless t.flat do impossibleTyping
    unless env.mod.structType? sid == some t do impossibleTyping
    let some d := env.mod.structs[sid]? | impossibleTyping
    pure d
  | _ => impossibleTyping

def recordField (env : TEnv) (t : Ty) (i : Nat) : Typing StructField := do
  let d ← recordType env t
  let some f := d.fields[i]? | impossibleTyping
  pure f

def origin (env : TEnv) (o : OriginId) : Typing Unit :=
  if o < env.mod.origins.size then pure () else impossibleTyping

def visibleVariable (env : TEnv) (x : VarId) : Typing LocalVar :=
  if !env.visible.contains x then impossibleTyping
  else match env.vars[x]? with
    | some lv => pure lv
    | none => impossibleTyping

def declaration (env : TEnv) (x : VarId) (scope : Nat) : Typing LocalVar := do
  let next ← get
  unless x = next do impossibleTyping
  match env.vars[x]? with
  | none => impossibleTyping
  | some lv =>
    unless lv.scope = scope do
      impossibleTyping
    unless lv.ty.storable do impossibleTyping
    set (next + 1)
    pure lv

def integerType (_what : String) (t : Ty) : Typing IntTy :=
  match t with
  | .int i => pure i
  | _ => impossibleTyping

def booleanType (_what : String) (t : Ty) : Typing Unit :=
  match t with
  | .bool => pure ()
  | _ => impossibleTyping

def writable (_what : String) (mutable : Bool) : Typing Unit :=
  if mutable then pure () else impossibleTyping

def predeclarations (env : TEnv) (sc : Nat) : List (VarId × Ty) → Typing TEnv
  | [] => pure env
  | (x, ty) :: rest => do
    let lv ← declaration env x sc
    unless lv.ty == ty do impossibleTyping
    predeclarations { env with visible := x :: env.visible } sc rest

def initializerCall (env : TEnv) (callee : Impl) : Typing Unit :=
  match env.initializing with
  | none => pure ()
  | some gi =>
    match callee.summary with
    | .unknown => impossibleTyping
    | .known s =>
      let later (t : Target) : Bool :=
        match t with | .global g => g ≥ gi | .param _ => false
      if (s.reads ++ s.writes ++ s.grows ++ s.shrinks).any later then
        impossibleTyping
      else pure ()

def callResult (callee : Impl) : Typing Ty :=
  match callee.results.toList with
  | [] => pure .unit
  | [t] => pure t
  | _ => impossibleTyping

def iterationVariable (lv : LocalVar) (byRef : Bool) (el : Ty) (mu : Bool) : Typing Unit :=
  if byRef then
    match lv.ty with
    | .ref mx t => do
      unless t == el do impossibleTyping
      if mx == .mutable then writable "a mutable loop reference" mu else pure ()
    | _ => impossibleTyping
  else
    if lv.ty == el then pure ()
    else impossibleTyping

def iterationIndex (env : TEnv) (sc : Nat) : Option VarId → Typing Unit
  | none => pure ()
  | some j => do
    let lj ← declaration env j sc
    if lj.ty == .int .i64 then pure ()
    else impossibleTyping

def returnUnit (env : TEnv) : Typing Unit := do
  if env.inExpr then impossibleTyping
  match env.impl with
  | none => impossibleTyping
  | some impl =>
    match impl.results.toList with
    | [] => pure ()
    | _ => impossibleTyping

def returnType (env : TEnv) : Typing Ty := do
  if env.inExpr then impossibleTyping
  match env.impl with
  | none => impossibleTyping
  | some impl =>
    match impl.results.toList with
    | [t] => pure t
    | _ => impossibleTyping

mutual
def place (env : TEnv) : Place → Typing PlaceInfo
  | .var x => do
    let lv ← visibleVariable env x
    pure ⟨lv.ty, lv.kind == .mutable, true⟩
  | .global g => do
    if g < env.globalLimit then
      match env.mod.globals[g]? with
      | some gl => pure ⟨gl.ty, gl.kind == .mutable, true⟩
      | none => impossibleTyping
    else impossibleTyping
  | .deref e => do
    let src ← (match sliceRefTy env e with
      | some t => pure t
      | none => do
        let t ← expression env e
        if t.isRefSlice then impossibleTyping else pure t)
    match src with
    | .ref m t => pure ⟨t, m == .mutable, m == .mutable⟩
    | _ => impossibleTyping
  | .elem v i o => do
    origin env o
    let (el, mu) ← view env v
    let _ ← integerType "an index" (← expression env i)
    pure ⟨el, mu, mu⟩
  | .field owner i => do
    let ownerInfo ← place env owner
    let f ← recordField env ownerInfo.ty i
    pure ⟨f.ty, ownerInfo.contentsWritable && f.binding == .mutable,
      ownerInfo.contentsWritable && f.contents == .mutable⟩

def view (env : TEnv) : View → Typing (Ty × Bool)
  | .of p => do
    let placeInfo ← place env p
    let t := placeInfo.ty
    let mu := placeInfo.contentsWritable
    match t with
    | .arr el _ => pure (el, mu)
    | .grow el | .growshrink el | .limited el _ => pure (el, mu)
    | _ => impossibleTyping
  | .val e => do
    match (← expression env e) with
    | .slice m el => pure (el, m == .mutable)
    | _ => impossibleTyping

def bound (env : TEnv) : Bound → Typing Unit
  | .omitted => pure ()
  | .expr e => do let _ ← integerType "a slice bound" (← expression env e)
  | .fromEnd e => do let _ ← integerType "a slice bound" (← expression env e)

def expression (env : TEnv) : Expr → Typing Ty
  | .lit t n =>
    if t.inRange n then pure (.int t) else impossibleTyping
  | .bool _ => pure .bool
  | .read p => do
    let placeInfo ← place env p
    let t := placeInfo.ty
    if t.readable then pure t else impossibleTyping
  | .ref m p => do
    let placeInfo ← place env p
    let t := placeInfo.ty
    let mu := placeInfo.referenceWritable env.mod.profile
    referenceCapabilities p placeInfo
    unless t.refTarget do impossibleTyping
    if m == .mutable then writable "a mutable reference" mu
    pure (.ref m t)
  | .slice m v lo hi o => do
    origin env o
    let (el, mu) ← view env v
    bound env lo
    bound env hi
    if m == .mutable then writable "a mutable slice" mu
    pure (.slice m el)
  | .len v => do
    let _ ← view env v
    pure (.int .i64)
  | .un op a o => do
    origin env o
    let t ← integerType "a unary operand" (← expression env a)
    match op with
    | .neg =>
      if t.signed then pure (.int t) else impossibleTyping
    | .bitnot => pure (.int t)
  | .bin _ a b o => do
    origin env o
    let t ← integerType "a binary operand" (← expression env a)
    let u ← integerType "a binary operand" (← expression env b)
    unless t = u do impossibleTyping
    pure (.int t)
  | .cmp op a b => do
    match (← expression env a), (← expression env b) with
    | .int t, .int u =>
      unless t = u do impossibleTyping
      pure .bool
    | .bool, .bool =>
      match op with
      | .eq | .ne => pure .bool
      | _ => impossibleTyping
    | _, _ => impossibleTyping
  | .and a b => do
    booleanType "an operand of `and`" (← expression env a)
    booleanType "an operand of `and`" (← expression env b)
    pure .bool
  | .or a b => do
    booleanType "an operand of `or`" (← expression env a)
    booleanType "an operand of `or`" (← expression env b)
    pure .bool
  | .not a => do
    booleanType "the operand of `not`" (← expression env a)
    pure .bool
  | .conv k target a o => do
    origin env o
    let s ← integerType "a converted value" (← expression env a)
    match target with
    | .int d =>
      match k with
      | .widen =>
        unless d.minVal ≤ s.minVal ∧ s.maxVal ≤ d.maxVal do
          impossibleTyping
        pure (.int d)
      | _ => pure (.int d)
    | _ => impossibleTyping
  | .call c args o => do
    origin env o
    let some ctx := env.mod.contexts[c]? | impossibleTyping
    let some callee := env.mod.impls[ctx.impl]? | impossibleTyping
    unless callee.params.size = args.length do
      impossibleTyping
    arguments env callee callee.params.toList args
    initializerCall env callee
    callResult callee
  | .push owner a org => do
    match env.mod.profile, org with
    | .pilot, none => pure ()
    | .shrink, some o => origin env o
    | _, _ => impossibleTyping
    let placeInfo ← place env owner
    let t := placeInfo.ty
    let el ← ownerElement env t
    let argTy ← expression env a
    unless argTy == el do impossibleTyping
    writable "push" (placeInfo.ownerMutationWritable env.mod.profile)
    pure (.ref .mutable el)
  | .pop owner org => do
    shrinkProfile env
    origin env org
    let placeInfo ← place env owner
    let el ← ownerElement env placeInfo.ty
    writable "pop" placeInfo.contentsWritable
    pure el
  | .ifE c t f => do
    booleanType "the condition of `if`" (← expression env c)
    let tt ← block (exprEnv env) [] t
    let ft ← block (exprEnv env) [] f
    unless tt == ft do impossibleTyping
    pure tt
  | .blockE b => block (exprEnv env) [] b
  | .arrLit t es => do
    resolved env t
    match t with
    | .arr el k =>
      unless el.flat do impossibleTyping
      unless es.length = k do impossibleTyping
      arrayExpressions env el es
      pure t
    | .grow el | .growshrink el =>
      unless el.flat do impossibleTyping
      arrayExpressions env el es
      pure t
    | .limited el capacity =>
      unless el.flat && es.length ≤ capacity do impossibleTyping
      arrayExpressions env el es
      pure t
    | _ => impossibleTyping
  | .fill t a => do
    resolved env t
    match t with
    | .arr el _ =>
      unless el.flat do impossibleTyping
      let argTy ← expression env a
      unless argTy == el do impossibleTyping
      pure t
    | _ => impossibleTyping
  | .structLit t es => do
    let d ← recordType env t
    unless d.fields.size == es.length do impossibleTyping
    recordExpressions env (d.fields.toList.map (·.ty)) es
    pure t

def recordExpressions (env : TEnv) : List Ty → List Expr → Typing Unit
  | [], [] => pure ()
  | t :: ts, e :: es => do
    unless (← expression env e) == t do impossibleTyping
    recordExpressions env ts es
  | _, _ => impossibleTyping

def arrayExpressions (env : TEnv) (el : Ty) : List Expr → Typing Unit
  | [] => pure ()
  | e :: rest => do
    let t ← expression env e
    unless t == el do impossibleTyping
    arrayExpressions env el rest

def arguments (env : TEnv) (callee : Impl) : List Param → List Arg → Typing Unit
  | p :: ps, a :: as => do
    unless argMode a == p.mode do
      impossibleTyping
    let some pv := callee.vars[p.var]? | impossibleTyping
    match a with
    | .byVal e =>
      let argTy ← expression env e
      unless argTy.passableTo pv.ty do impossibleTyping
    | .byRef m p' =>
      let placeInfo ← place env p'
      let t := placeInfo.ty
      let mu := placeInfo.referenceWritable env.mod.profile
      referenceCapabilities p' placeInfo
      unless t.refTarget || (t.isSlice && mu && p'.sliceArg) do
        impossibleTyping
      if m == .mutable then writable "a mutable argument" mu
      unless (Ty.ref m t).passableTo pv.ty do
        impossibleTyping
    arguments env callee ps as
  | _, _ => pure ()

def block (env : TEnv) (pre : List (VarId × Ty)) : Block → Typing Ty
  | .mk sc stmts value => do
    if env.scopes.contains sc then impossibleTyping
    let env1 ← predeclarations { env with scopes := sc :: env.scopes } sc pre
    let env2 ← statements env1 sc stmts
    match value with
    | none => pure .unit
    | some e => expression env2 e

def statements (env : TEnv) (sc : Nat) : List Stmt → Typing TEnv
  | [] => pure env
  | s :: rest => do
    let env' ← statement env sc s
    statements env' sc rest

def printArguments (env : TEnv) : List PrintArg → Typing Unit
  | [] => pure ()
  | .text _ :: rest => printArguments env rest
  | .expr e :: rest => do
    match (← expression env e) with
    | .int _ | .bool => printArguments env rest
    | _ => impossibleTyping

def statement (env : TEnv) (sc : Nat) : Stmt → Typing TEnv
  | .letS x e o => do
    origin env o
    let lv ← declaration env x sc
    let t ← expression env e
    freshOwner env e lv.ty
    unless t.passableTo lv.ty do impossibleTyping
    pure { env with visible := x :: env.visible }
  | .assign p e o => do
    origin env o
    let placeInfo ← place env p
    let t := placeInfo.ty
    let mu := placeInfo.bindingWritable
    unless t.flat || (t.isSlice && p.derefVar?.isSome) do
      impossibleTyping
    let et ← expression env e
    unless et == t do impossibleTyping
    writable "assignment" mu
    pure env
  | .assignOp _ p e o => do
    origin env o
    let placeInfo ← place env p
    let t := placeInfo.ty
    let mu := placeInfo.bindingWritable
    let i ← integerType "the target of a compound assignment" t
    let u ← integerType "the right side of a compound assignment" (← expression env e)
    unless i = u do impossibleTyping
    writable "compound assignment" mu
    pure env
  | .rebind x e o => do
    origin env o
    let lv ← visibleVariable env x
    unless lv.ty.isRefLike do impossibleTyping
    unless lv.kind == .mutable do impossibleTyping
    let et ← expression env e
    unless et.passableTo lv.ty do impossibleTyping
    pure env
  | .expr e o => do
    origin env o
    let _ ← expression env e
    pure env
  | .append owner src o => do
    origin env o
    let placeInfo ← place env owner
    let t := placeInfo.ty
    let el ← ownerElement env t
    let (sel, _) ← view env src
    unless sel == el do impossibleTyping
    writable "append" (placeInfo.ownerMutationWritable env.mod.profile)
    pure env
  | .popN owner count org => do
    shrinkProfile env
    origin env org
    let info ← place env owner
    let _ ← ownerElement env info.ty
    let _ ← integerType "pop_n count" (← expression env count)
    writable "pop_n" info.contentsWritable
    pure env
  | .resize owner size fill org => do
    shrinkProfile env
    origin env org
    let info ← place env owner
    let el ← ownerElement env info.ty
    let _ ← integerType "resize size" (← expression env size)
    match fill with
    | none => pure ()
    | some e => unless (← expression env e) == el do impossibleTyping
    writable "resize" info.contentsWritable
    pure env
  | .clear owner org => do
    shrinkProfile env
    origin env org
    let info ← place env owner
    let _ ← ownerElement env info.ty
    writable "clear" info.contentsWritable
    pure env
  | .assignWhole owner replacement org => do
    shrinkProfile env
    origin env org
    let info ← place env owner
    match info.ty with
    | .grow _ | .growshrink _ => pure ()
    | _ => impossibleTyping
    let rt ← expression env replacement
    unless rt == info.ty do impossibleTyping
    freshOwner env replacement info.ty
    writable "whole replacement" (info.bindingWritable && info.contentsWritable)
    pure env
  | .ifS c t f o => do
    origin env o
    booleanType "the condition of `if`" (← expression env c)
    let _ ← block env [] t
    match f with
    | some b => do let _ ← block env [] b
    | none => pure ()
    pure env
  | .while c b o => do
    origin env o
    booleanType "the condition of `while`" (← expression env c)
    let _ ← block { env with loops := env.loops + 1 } [] b
    pure env
  | .forRange x lo hi b o => do
    origin env o
    let lv ← declaration env x b.scope
    let t ← integerType "a range bound" (← expression env lo)
    let u ← integerType "a range bound" (← expression env hi)
    unless t = u do impossibleTyping
    (if lv.ty == .int t then pure ()
      else impossibleTyping : Typing Unit)
    let _ ← block { env with loops := env.loops + 1, visible := x :: env.visible } [] b
    pure env
  | .forEach x idx v byRef b o => do
    origin env o
    let lv ← declaration env x b.scope
    iterationIndex env b.scope idx
    let (el, mu) ← view env v
    iterationVariable lv byRef el mu
    let _ ← block { env with loops := env.loops + 1, visible := x :: idx.toList ++ env.visible } [] b
    pure env
  | .ret none o => do
    origin env o
    returnUnit env
    pure env
  | .ret (some e) o => do
    origin env o
    let t ← returnType env
    let et ← expression env e
    unless et.passableTo t do impossibleTyping
    pure env
  | .brk o => do
    origin env o
    if env.loops = 0 then impossibleTyping else pure env
  | .cont o => do
    origin env o
    if env.loops = 0 then impossibleTyping else pure env
  | .print args o => do
    origin env o
    printArguments env args
    pure env
  | .assertS e o => do
    origin env o
    booleanType "an asserted value" (← expression env e)
    pure env
  | .abort _ o => do
    origin env o
    pure env
  | .exit e o => do
    origin env o
    let _ ← integerType "an exit code" (← expression env e)
    pure env
end


private def reflects (x : Except ε α) : Judgment α := fun a => x = .ok a

private def reflectsState (x : StateT σ (Except ε) α) : StateT σ Judgment α :=
  fun state => reflects (x state)

private theorem reflects_pure (a : α) :
    reflects (pure a : Except ε α) = (pure a : Judgment α) := by
  funext b
  change (Except.ok a = Except.ok b) = (b = a)
  exact propext (by simp [eq_comm])

private theorem reflects_bind (x : Except ε α) (f : α → Except ε β) :
    reflects (x >>= f) = (reflects x >>= fun a => reflects (f a)) := by
  funext b
  cases x <;> simp [reflects, bind, Except.bind, instMonadJudgment]

private theorem reflectsState_pure (a : α) :
    reflectsState (pure a : StateT σ (Except ε) α) = (pure a : StateT σ Judgment α) := by
  funext state
  exact reflects_pure (a, state)

private theorem reflectsState_bind (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) :
    reflectsState (x >>= f) = (reflectsState x >>= fun a => reflectsState (f a)) := by
  funext state
  exact reflects_bind (x state) (fun result => f result.1 result.2)

private theorem reflectsState_map (f : α → β) (value : StateT σ (Except ε) α) :
    reflectsState (f <$> value) = f <$> reflectsState value := by
  simp only [← bind_pure_comp, reflectsState_bind, reflectsState_pure]

@[simp] private theorem impossibleTyping_bind (next : α → Typing β) :
    (impossibleTyping >>= next) = (impossibleTyping : Typing β) := by
  funext state result
  simp [impossibleTyping, bind, StateT.bind, instMonadJudgment]

@[simp] private theorem impossibleTyping_apply (state : Nat) (result : α × Nat) :
    impossibleTyping state result = False := rfl

private theorem reflectsState_rej (rule : Rule) (message : String) :
    reflectsState (rej rule message : T α) = (impossibleTyping : Typing α) := by
  funext state result
  exact propext (Sound.rej_ok rule message state result)

private theorem reflectsState_ite (condition : Prop) [Decidable condition]
    (yes no : StateT σ (Except ε) α) :
    reflectsState (if condition then yes else no) =
      (if condition then reflectsState yes else reflectsState no) := by
  by_cases h : condition <;> simp [h]


private theorem reflectsState_get :
    reflectsState (get : StateT σ (Except ε) σ) = (get : StateT σ Judgment σ) := by
  funext state
  exact reflects_pure (state, state)

private theorem reflectsState_set (state : σ) :
    reflectsState (set state : StateT σ (Except ε) PUnit) =
      (set state : StateT σ Judgment PUnit) := by
  funext previous
  exact reflects_pure (PUnit.unit, state)


private theorem referenceCapabilities_correct (p : Place) (info : PlaceInfo) :
    reflectsState (checkFieldReference p info) = referenceCapabilities p info := by
  simp only [checkFieldReference, referenceCapabilities, reflectsState_ite,
    reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem origin_correct (env : TEnv) (o : OriginId) :
    reflectsState (checkOrg env o) = origin env o := by
  simp only [checkOrg, origin, reflectsState_ite, reflectsState_rej, reflectsState_pure, reflectsState_map]



private theorem resolved_correct (env : TEnv) (type : Ty) :
    reflectsState (checkType env type) = resolved env type := by
  funext state result
  rcases result with ⟨unit, next⟩
  cases unit
  apply propext
  simp [reflectsState, reflects, resolved, Sound.checkType_ok, resolvedType_iff]

private theorem shrinkProfile_correct (env : TEnv) :
    reflectsState (requireShrink env) = shrinkProfile env := by
  simp only [requireShrink, shrinkProfile, reflectsState_ite,
    reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem integerType_correct (what : String) (t : Ty) :
    reflectsState (requireInt what t) = integerType what t := by
  cases t <;> simp only [requireInt, integerType, reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem booleanType_correct (what : String) (t : Ty) :
    reflectsState (requireBool what t) = booleanType what t := by
  cases t <;> simp only [requireBool, booleanType, reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem writable_correct (what : String) (mutable : Bool) :
    reflectsState (requireWrite what mutable) = writable what mutable := by
  simp only [requireWrite, writable, reflectsState_ite, reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem freshOwner_correct (env : TEnv) (e : Expr) (t : Ty) :
    reflectsState (checkOwnerRun env e t) = freshOwner env e t := by
  simp only [checkOwnerRun, freshOwner, reflectsState_ite, reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem visibleVariable_correct (env : TEnv) (x : VarId) :
    reflectsState (varOf env x) = visibleVariable env x := by
  cases h : env.vars[x]? <;>
    simp [varOf, visibleVariable, h, reflectsState_ite, reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem declaration_correct (env : TEnv) (x : VarId) (scope : Nat) :
    reflectsState (declare env x scope) = declaration env x scope := by
  cases h : env.vars[x]? <;>
    simp [declare, declaration, h, reflectsState_bind, reflectsState_get,
      reflectsState_set, reflectsState_ite, reflectsState_rej, reflectsState_pure,
      reflectsState_map]

private theorem ownerElement_correct (env : TEnv) (t : Ty) :
    reflectsState (Goose.Core.ownerElement env t) = ownerElement env t := by
  cases h : t.ownerElem? <;>
    simp [Goose.Core.ownerElement, ownerElement, h, reflectsState_bind,
    reflectsState_rej, reflectsState_pure, reflectsState_map, resolved_correct]

private theorem recordType_correct (env : TEnv) (t : Ty) :
    reflectsState (structDef env t) = recordType env t := by
  cases t <;> first
    | (simp [structDef, recordType, reflectsState_bind, reflectsState_ite,
        reflectsState_rej, reflectsState_pure, reflectsState_map]; done)
    | (rename_i sid fields
       cases h : env.mod.structs[sid]? <;>
        simp [structDef, recordType, h, reflectsState_bind, reflectsState_ite,
          reflectsState_rej, reflectsState_pure, reflectsState_map])

private theorem recordField_correct (env : TEnv) (t : Ty) (i : Nat) :
    reflectsState (structField env t i) = recordField env t i := by
  simp only [structField, recordField, reflectsState_bind, recordType_correct]
  congr 1
  funext descriptor
  cases h : descriptor.fields[i]? <;>
    simp [h, reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem callResult_correct (callee : Impl) :
    reflectsState (callResultTy callee) = callResult callee := by
  rcases h : callee.results.toList with _ | ⟨t, _ | ts⟩ <;>
    simp [callResultTy, callResult, h, reflectsState_pure, reflectsState_rej]

private theorem initializerCall_correct (env : TEnv) (callee : Impl) :
    reflectsState (checkInitCall env callee) = initializerCall env callee := by
  cases h : env.initializing <;> cases hs : callee.summary <;>
    simp [checkInitCall, initializerCall, h, hs, reflectsState_ite,
      reflectsState_rej, reflectsState_pure, reflectsState_map] <;> rfl

private theorem returnUnit_correct (env : TEnv) :
    reflectsState (retUnit env) = returnUnit env := by
  cases hi : env.impl
  · simp [retUnit, returnUnit, hi, reflectsState_bind, reflectsState_ite,
      reflectsState_rej, reflectsState_pure, reflectsState_map]
  · rename_i impl
    rcases hr : impl.results.toList with _ | ⟨t, ts⟩ <;>
      simp [retUnit, returnUnit, hi, hr, reflectsState_bind, reflectsState_ite,
        reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem returnType_correct (env : TEnv) :
    reflectsState (retTy env) = returnType env := by
  cases hi : env.impl
  · simp [retTy, returnType, hi, reflectsState_bind, reflectsState_ite,
      reflectsState_rej, reflectsState_pure, reflectsState_map]
  · rename_i impl
    rcases hr : impl.results.toList with _ | ⟨t, _ | ts⟩ <;>
      simp [retTy, returnType, hi, hr, reflectsState_bind, reflectsState_ite,
        reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem iterationVariable_correct (lv : LocalVar) (byRef : Bool) (el : Ty) (mu : Bool) :
    reflectsState (loopVarOk lv byRef el mu) = iterationVariable lv byRef el mu := by
  cases byRef <;> cases ht : lv.ty <;>
    simp [loopVarOk, iterationVariable, ht, Bool.false_eq_true, Bool.true_eq,
      ite_false, ite_true, reflectsState_bind, reflectsState_ite,
      reflectsState_rej, reflectsState_pure, writable_correct]

private theorem iterationIndex_correct (env : TEnv) (sc : Nat) (idx : Option VarId) :
    reflectsState (declareIndex env sc idx) = iterationIndex env sc idx := by
  cases idx <;>
    simp [declareIndex, iterationIndex, reflectsState_bind, declaration_correct,
      reflectsState_ite, reflectsState_rej, reflectsState_pure, reflectsState_map]

private theorem predeclarations_correct (env : TEnv) (sc : Nat) : ∀ (pre : List (VarId × Ty)),
    reflectsState (declarePre env sc pre) = predeclarations env sc pre
  | [] => by simp [declarePre, predeclarations, reflectsState_pure]
  | (x, ty) :: rest => by
    simp [declarePre, predeclarations, reflectsState_bind, declaration_correct,
      reflectsState_ite, reflectsState_rej, reflectsState_pure,
      predeclarations_correct _ sc rest]

syntax "typing_reflection" "["
  (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),*
  "]" : tactic

macro_rules
  | `(tactic| typing_reflection [$lemmas,*]) =>
    `(tactic| simp only [reflectsState_bind,
        reflectsState_map,
        reflectsState_pure,
        reflectsState_ite,
        impossibleTyping_bind,
        reflectsState_rej,
        origin_correct,
        visibleVariable_correct,
        declaration_correct,
        resolved_correct,
        shrinkProfile_correct,
        ownerElement_correct,
        freshOwner_correct,
        recordType_correct,
        recordField_correct,
        integerType_correct,
        booleanType_correct,
        writable_correct,
        referenceCapabilities_correct,
        initializerCall_correct,
        callResult_correct,
        iterationVariable_correct,
        iterationIndex_correct,
        returnUnit_correct,
        returnType_correct,
        predeclarations_correct,
        pure_bind, $lemmas,*])

set_option maxHeartbeats 1600000 in
mutual
private theorem place_correct (env : TEnv) : ∀ (p : Place),
    reflectsState (tyPlace env p) = place env p
  | .var x => by
    typing_reflection [tyPlace, place]
    all_goals try rfl
  | .global g => by
    cases hg : env.mod.globals[g]? <;>
    typing_reflection [tyPlace, place, hg]
    all_goals try rfl
  | .deref e => by
    cases hs : sliceRefTy env e with
    | none =>
      typing_reflection [tyPlace, place, hs, expression_correct _ e] <;> try rfl
      congr 1
      funext source
      cases source <;>
        typing_reflection [] <;> try rfl
    | some source =>
      cases source <;>
        typing_reflection [tyPlace, place, hs] <;> try rfl

  | .elem v e o => by
    typing_reflection [tyPlace, place, view_correct _ v, expression_correct _ e]
    all_goals try rfl
  | .field p i => by
    typing_reflection [tyPlace, place, place_correct _ p]
    all_goals try rfl
termination_by p => sizeOf p

private theorem view_correct (env : TEnv) : ∀ (v : View),
    reflectsState (tyView env v) = view env v
  | .of p => by
    typing_reflection [tyView, view, place_correct _ p]
    all_goals try rfl
    congr 1
    funext info
    cases h : info.ty <;>
      typing_reflection [h]
  | .val e => by
    typing_reflection [tyView, view, expression_correct _ e]
    all_goals try rfl
    congr 1
    funext source
    cases source <;> typing_reflection []
termination_by v => sizeOf v

private theorem bound_correct (env : TEnv) : ∀ (b : Bound),
    reflectsState (tyBound env b) = bound env b
  | .omitted => by
    typing_reflection [tyBound, bound]
    all_goals try rfl
  | .expr e => by
    typing_reflection [tyBound, bound, expression_correct _ e]
    all_goals try rfl
  | .fromEnd e => by
    typing_reflection [tyBound, bound, expression_correct _ e]
    all_goals try rfl
termination_by b => sizeOf b

private theorem expression_correct (env : TEnv) : ∀ (e : Expr),
    reflectsState (tyExpr env e) = expression env e
  | .lit t n => by
    typing_reflection [tyExpr, expression]
    all_goals try rfl
  | .bool b => by
    typing_reflection [tyExpr, expression]
    all_goals try rfl
  | .read p => by
    typing_reflection [tyExpr, expression, place_correct _ p]
    all_goals try rfl
  | .ref mu p => by
    typing_reflection [tyExpr, expression, place_correct _ p]
    all_goals try rfl
  | .slice mu v lo hi o => by
    typing_reflection [tyExpr, expression, view_correct _ v, bound_correct _ lo, bound_correct _ hi]
    all_goals try rfl
  | .len v => by
    typing_reflection [tyExpr, expression, view_correct _ v]
    all_goals try rfl
  | .un op e o => by
    cases op <;>
    typing_reflection [tyExpr, expression, expression_correct _ e]
    all_goals try rfl
  | .bin op a b o => by
    typing_reflection [tyExpr, expression, expression_correct _ a, expression_correct _ b]
    all_goals try rfl
  | .cmp op a b => by
    typing_reflection [tyExpr, expression, expression_correct _ a, expression_correct _ b]
    all_goals try rfl
    congr 1
    funext firstType
    congr 1
    funext secondType
    cases firstType <;> cases secondType <;> cases op <;>
      simp only [reflectsState_ite, reflectsState_bind, reflectsState_map,
        reflectsState_rej, reflectsState_pure, impossibleTyping_bind]
  | .and a b => by
    typing_reflection [tyExpr, expression, expression_correct _ a, expression_correct _ b]
    all_goals try rfl
  | .or a b => by
    typing_reflection [tyExpr, expression, expression_correct _ a, expression_correct _ b]
    all_goals try rfl
  | .not e => by
    typing_reflection [tyExpr, expression, expression_correct _ e]
    all_goals try rfl
  | .conv kind target e o => by
    cases target <;> cases kind <;>
    typing_reflection [tyExpr, expression, expression_correct _ e]
    all_goals try rfl
  | .call c args o => by
    cases hc : env.mod.contexts[c]? with
    | none =>
      typing_reflection [tyExpr, expression, hc] <;> try rfl
    | some context =>
      cases hi : env.mod.impls[context.impl]? <;>
        typing_reflection [tyExpr, expression, hc, hi, arguments_correct _ _ _ args] <;> try rfl

  | .push p e o => by
    cases hp : env.mod.profile <;> cases o <;>
    typing_reflection [tyExpr, expression, hp, place_correct _ p, expression_correct _ e]
    all_goals try rfl
  | .pop p o => by
    typing_reflection [tyExpr, expression, place_correct _ p]
    all_goals try rfl
  | .ifE c t f => by
    typing_reflection [tyExpr, expression, expression_correct _ c, block_correct _ [] t, block_correct _ [] f]
    all_goals try rfl
  | .blockE b => by
    typing_reflection [tyExpr, expression, block_correct _ [] b]
    all_goals try rfl
  | .arrLit t es => by
    cases t <;>
    typing_reflection [tyExpr, expression, arrayExpressions_correct _ _ es]
    all_goals try rfl
  | .fill t e => by
    cases t <;>
    typing_reflection [tyExpr, expression, expression_correct _ e]
    all_goals try rfl
  | .structLit t es => by
    typing_reflection [tyExpr, expression, recordExpressions_correct _ _ es]
    all_goals try rfl
termination_by e => sizeOf e

private theorem recordExpressions_correct (env : TEnv) (types : List Ty) : ∀ (es : List Expr),
    reflectsState (tyStructExprs env types es) = recordExpressions env types es
  | [] => by
    cases types <;>
    typing_reflection [tyStructExprs, recordExpressions]
    all_goals try rfl
  | e :: es => by
    cases types <;>
    typing_reflection [tyStructExprs, recordExpressions, expression_correct _ e, recordExpressions_correct _ _ es]
    all_goals try rfl
termination_by es => sizeOf es

private theorem arrayExpressions_correct (env : TEnv) (el : Ty) : ∀ (es : List Expr),
    reflectsState (tyExprsAs env el es) = arrayExpressions env el es
  | [] => by
    typing_reflection [tyExprsAs, arrayExpressions]
    all_goals try rfl
  | e :: es => by
    typing_reflection [tyExprsAs, arrayExpressions, expression_correct _ e, arrayExpressions_correct _ _ es]
    all_goals try rfl
termination_by es => sizeOf es

private theorem arguments_correct (env : TEnv) (callee : Impl) (params : List Param) :
    ∀ (args : List Arg), reflectsState (tyArgs env callee params args) = arguments env callee params args
  | [] => by
    cases params <;>
      typing_reflection [tyArgs, arguments] <;> try rfl
  | a :: args => by
    cases params with
    | nil =>
      typing_reflection [tyArgs, arguments] <;> try rfl
    | cons param rest =>
      cases a with
      | byVal e =>
        cases hp : callee.vars[param.var]? <;>
          typing_reflection [tyArgs, arguments, hp, expression_correct _ e, arguments_correct _ _ rest args] <;> try rfl
      | byRef mu p =>
        cases hp : callee.vars[param.var]? <;>
          typing_reflection [tyArgs, arguments, hp, place_correct _ p, arguments_correct _ _ rest args] <;> try rfl
termination_by args => sizeOf args

private theorem block_correct (env : TEnv) (pre : List (VarId × Ty)) : ∀ (b : Block),
    reflectsState (tyBlock env pre b) = block env pre b
  | .mk sc stmts value => by
    cases value with
    | none =>
      typing_reflection [tyBlock, block, statements_correct _ sc stmts]
    | some e =>
      typing_reflection [tyBlock, block, statements_correct _ sc stmts, expression_correct _ e]

termination_by b => sizeOf b

private theorem statements_correct (env : TEnv) (sc : Nat) : ∀ (stmts : List Stmt),
    reflectsState (tyStmts env sc stmts) = statements env sc stmts
  | [] => by
    typing_reflection [tyStmts, statements]
    all_goals try rfl
  | st :: stmts => by
    typing_reflection [tyStmts, statements, statement_correct _ sc st, statements_correct _ sc stmts]
    all_goals try rfl
termination_by stmts => sizeOf stmts

private theorem printArguments_correct (env : TEnv) : ∀ (args : List PrintArg),
    reflectsState (tyPrintArgs env args) = printArguments env args
  | [] => by
    typing_reflection [tyPrintArgs, printArguments]
    all_goals try rfl
  | a :: args => by
    cases a with
    | text text =>
      typing_reflection [tyPrintArgs, printArguments, printArguments_correct _ args] <;> try rfl
    | expr e =>
      typing_reflection [tyPrintArgs, printArguments, expression_correct _ e, printArguments_correct _ args] <;> try rfl
      congr 1
      funext source
      cases source <;>
        typing_reflection [printArguments_correct _ args] <;> try rfl

termination_by args => sizeOf args

private theorem statement_correct (env : TEnv) (sc : Nat) : ∀ (st : Stmt),
    reflectsState (tyStmt env sc st) = statement env sc st
  | .letS x e o => by
    typing_reflection [tyStmt, statement, expression_correct _ e]
    all_goals try rfl
  | .assign p e o => by
    typing_reflection [tyStmt, statement, place_correct _ p, expression_correct _ e]
    all_goals try rfl
  | .assignOp op p e o => by
    typing_reflection [tyStmt, statement, place_correct _ p, expression_correct _ e]
    all_goals try rfl
  | .rebind x e o => by
    typing_reflection [tyStmt, statement, expression_correct _ e]
    all_goals try rfl
  | .expr e o => by
    typing_reflection [tyStmt, statement, expression_correct _ e]
    all_goals try rfl
  | .append p v o => by
    typing_reflection [tyStmt, statement, place_correct _ p, view_correct _ v]
    all_goals try rfl
  | .popN p e o => by
    typing_reflection [tyStmt, statement, place_correct _ p, expression_correct _ e]
    all_goals try rfl
  | .resize p e fill o => by
    cases fill with
    | none =>
      typing_reflection [tyStmt, statement, place_correct _ p, expression_correct _ e] <;> try rfl
    | some value =>
      typing_reflection [tyStmt, statement, place_correct _ p, expression_correct _ e, expression_correct _ value] <;> try rfl

  | .clear p o => by
    typing_reflection [tyStmt, statement, place_correct _ p]
    all_goals try rfl
  | .assignWhole p e o => by
    typing_reflection [tyStmt, statement, place_correct _ p, expression_correct _ e] <;> try rfl
    congr 1
    funext profileGuard
    congr 1
    funext originGuard
    congr 1
    funext info
    cases ht : info.ty <;>
      typing_reflection [ht, expression_correct _ e] <;> try rfl

  | .ifS c t f o => by
    cases f with
    | none =>
      typing_reflection [tyStmt, statement, expression_correct _ c, block_correct _ [] t] <;> try rfl
    | some value =>
      typing_reflection [tyStmt, statement, expression_correct _ c, block_correct _ [] t, block_correct _ [] value] <;> try rfl

  | .while c b o => by
    typing_reflection [tyStmt, statement, expression_correct _ c, block_correct _ [] b]
    all_goals try rfl
  | .forRange x lo hi b o => by
    typing_reflection [tyStmt, statement, expression_correct _ lo, expression_correct _ hi, block_correct _ [] b]
    all_goals try rfl
  | .forEach x idx v byRef b o => by
    typing_reflection [tyStmt, statement, view_correct _ v, block_correct _ [] b]
    all_goals try rfl
  | .ret value o => by
    cases value with
    | none =>
      typing_reflection [tyStmt, statement] <;> try rfl
    | some value =>
      typing_reflection [tyStmt, statement, expression_correct _ value] <;> try rfl

  | .brk o => by
    typing_reflection [tyStmt, statement]
    all_goals try rfl
  | .cont o => by
    typing_reflection [tyStmt, statement]
    all_goals try rfl
  | .print args o => by
    typing_reflection [tyStmt, statement, printArguments_correct _ args]
    all_goals try rfl
  | .assertS e o => by
    typing_reflection [tyStmt, statement, expression_correct _ e]
    all_goals try rfl
  | .abort message o => by
    typing_reflection [tyStmt, statement]
    all_goals try rfl
  | .exit e o => by
    typing_reflection [tyStmt, statement, expression_correct _ e]
    all_goals try rfl
termination_by st => sizeOf st

end

def ExprTyping (env : TEnv) (expr : Expr) (before : Nat) (type : Ty) (after : Nat) : Prop :=
  expression env expr before (type, after)

def BlockTyping (env : TEnv) (pre : List (VarId × Ty)) (body : Block)
    (before : Nat) (type : Ty) (after : Nat) : Prop :=
  block env pre body before (type, after)

theorem exprTyping_iff (env : TEnv) (expr : Expr) (before : Nat) (type : Ty) (after : Nat) :
    ExprTyping env expr before type after ↔ tyExpr env expr before = .ok (type, after) := by
  unfold ExprTyping
  rw [← expression_correct env expr]
  rfl

def PlaceTyping (env : TEnv) (source : Place) (before : Nat) (info : PlaceInfo) (after : Nat) : Prop :=
  place env source before (info, after)

def ViewTyping (env : TEnv) (source : View) (before : Nat) (info : Ty × Bool) (after : Nat) : Prop :=
  view env source before (info, after)

def StatementTyping (env : TEnv) (scope : Nat) (source : Stmt) (before : Nat)
    (next : TEnv) (after : Nat) : Prop :=
  statement env scope source before (next, after)

def StatementsTyping (env : TEnv) (scope : Nat) (source : List Stmt) (before : Nat)
    (next : TEnv) (after : Nat) : Prop :=
  statements env scope source before (next, after)

theorem placeTyping_iff (env : TEnv) (source : Place) (before : Nat) (info : PlaceInfo) (after : Nat) :
    PlaceTyping env source before info after ↔ tyPlace env source before = .ok (info, after) := by
  unfold PlaceTyping
  rw [← place_correct env source]
  rfl

theorem viewTyping_iff (env : TEnv) (source : View) (before : Nat) (info : Ty × Bool) (after : Nat) :
    ViewTyping env source before info after ↔ tyView env source before = .ok (info, after) := by
  unfold ViewTyping
  rw [← view_correct env source]
  rfl

theorem statementTyping_iff (env : TEnv) (scope : Nat) (source : Stmt) (before : Nat)
    (next : TEnv) (after : Nat) :
    StatementTyping env scope source before next after ↔
      tyStmt env scope source before = .ok (next, after) := by
  unfold StatementTyping
  rw [← statement_correct env scope source]
  rfl

theorem stmtsTyping_iff (env : TEnv) (scope : Nat) (source : List Stmt) (before : Nat)
    (next : TEnv) (after : Nat) :
    StatementsTyping env scope source before next after ↔
      tyStmts env scope source before = .ok (next, after) := by
  unfold StatementsTyping
  rw [← statements_correct env scope source]
  rfl

theorem exprTyping_sound (env : TEnv) (expr : Expr) (before : Nat) (type : Ty) (after : Nat)
    (accepted : tyExpr env expr before = .ok (type, after)) :
    ExprTyping env expr before type after := by
  unfold ExprTyping
  rw [← expression_correct env expr]
  exact accepted

theorem blockTyping_iff (env : TEnv) (pre : List (VarId × Ty)) (body : Block)
    (before : Nat) (type : Ty) (after : Nat) :
    BlockTyping env pre body before type after ↔ tyBlock env pre body before = .ok (type, after) := by
  unfold BlockTyping
  rw [← block_correct env pre body]
  rfl

theorem blockTyping_sound (env : TEnv) (pre : List (VarId × Ty)) (body : Block)
    (before : Nat) (type : Ty) (after : Nat)
    (accepted : tyBlock env pre body before = .ok (type, after)) :
    BlockTyping env pre body before type after := by
  unfold BlockTyping
  rw [← block_correct env pre body]
  exact accepted

structure ImplementationTyping (m : Module) (impl : Impl) : Prop where
  body : ∃ type after, BlockTyping (Sound.implEnv m impl) [] impl.body impl.params.size type after ∧
    ((impl.results.toList = [] ∧ type = .unit) ∨
      ∃ result, impl.results.toList = [result] ∧
        (impl.body.value.isSome = true → type = result) ∧
        (impl.body.value.isSome = false → impl.body.diverges m.noReturn = true))

structure GlobalTyping (m : Module) (index : GlobalId) (global : Global) : Prop where
  storage : global.ty.storable = true ∧ global.ty.isRefLike = false
  initializer : ∃ after, ExprTyping (Sound.initEnv m index) global.init 0 global.ty after
  ownerFresh : m.profile = .shrink → global.ty.ownerElem?.isSome = true →
    global.init.freshOwner = true

theorem implementationTyping_sound (m : Module) (impl : Impl)
    (accepted : checkImpl m impl = .ok ()) : ImplementationTyping m impl := by
  obtain ⟨type, after, typed, result⟩ := (Sound.checkImpl_ok m impl accepted).body
  exact ⟨type, after, blockTyping_sound _ _ _ _ _ _ typed, result⟩

theorem globalTyping_sound (m : Module) (index : GlobalId) (global : Global)
    (accepted : checkGlobal m index global = .ok ()) : GlobalTyping m index global := by
  obtain ⟨storage, after, typed⟩ := Sound.checkGlobal_ok m index global accepted
  refine ⟨storage, ⟨after, exprTyping_sound _ _ _ _ _ typed⟩, ?_⟩
  intro profile owner
  cases fresh : global.init.freshOwner with
  | true => rfl
  | false =>
    cases scopes : scopeOrderError (exprScopes none global.init) 0 with
    | some message =>
      simp only [checkGlobal, scopes] at accepted
      inv at accepted
    | none =>
      have typed' : tyExpr (Sound.initEnv m index) global.init 0 = .ok (global.ty, after) := typed
      simp [checkGlobal, Sound.initEnv, scopes, typed', checkOwnerRun, profile, owner,
        fresh, StateT.run, chk] at accepted

theorem accepted_implementationTyping (m : Module) (accepted : validate m = .ok ())
    (index : ImplId) (impl : Impl) (lookup : m.impls[index]? = some impl) :
    ImplementationTyping m impl := by
  obtain ⟨type, after, typed, result⟩ := (Sound.validate_modOk m accepted).impl index impl lookup |>.body
  exact ⟨type, after, blockTyping_sound _ _ _ _ _ _ typed, result⟩

theorem accepted_globalTyping (m : Module) (accepted : validate m = .ok ())
    (index : GlobalId) (global : Global) (lookup : m.globals[index]? = some global) :
    GlobalTyping m index global := by
  unfold validate at accepted
  inv at accepted
  obtain ⟨_, _, _, globals, _, _, _, _⟩ := accepted
  have indexBound : index < m.globals.size := (Array.getElem?_eq_some_iff.mp lookup).1
  have checked := (Sound.forAll_ok _ _).mp globals index (List.mem_range.mpr indexBound)
  simp only [lookup] at checked
  exact globalTyping_sound m index global checked

end Declarative
end Goose.Core
