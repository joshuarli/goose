import Goose.Lower.Validation.SourceReplacementWriterLedgerChildSpansPlaces

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

def OrdinaryExpression : Expr → Prop
  | .and .. | .or .. | .ifE .. | .blockE .. => False
  | _ => True

private theorem comparison_tail_advances (operation : CmpOp) (left right : ValueId) :
    AdvB (do
      match (← valTy left) with
      | .data (.int type) => emitDef (.cmp operation type left right)
      | _ => emitDef (.boolCmp operation left right)) := by
  apply AdvB.bind (advB_valTy left)
  intro type
  cases type with
  | data type => cases type <;> exact advB_emitDef _
  | view _ _ => exact advB_emitDef _

private theorem call_tail_advances (function : ContextId) (arguments : List ValueId) (origin : OriginId) :
    AdvB (do
      let returned ← emitDef (.call function arguments (some origin))
      if (← read).mod.noReturn function then emitTerm .unreachable
      pure returned) := by
  exact AdvB.bind (advB_emitDef _) fun returned => AdvB.bind advB_read fun env => by
    cases env.mod.noReturn function <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact AdvB.pure _ | exact AdvB.bind (advB_emitTerm _) fun _ => AdvB.pure _

theorem Fragment.expression_child_span {expression : Expr} {child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (ordinary : OrdinaryExpression expression)
    (row : (Fragment.expression expression).child? env before index = some (child, start)) :
    before.Ext start ∧ (child.finish env start).Ext ((Fragment.expression expression).finish env before) := by
  have member := Fragment.child_member row
  cases expression with
  | lit type value => simp [Fragment.children] at member
  | bool value => simp [Fragment.children] at member
  | and left right => exact False.elim ordinary
  | or left right => exact False.elim ordinary
  | ifE condition yes no => exact False.elim ordinary
  | blockE block => exact False.elim ordinary
  | read place =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerPlace place)
      (fun address => do
        let value ← emitDef (.load address)
        recordReadValueRootRecipe value place
        pure value)
      (fun address => AdvB.bind (advB_emitDef (.load address)) fun value =>
        AdvB.bind (advB_recordReadValueRootRecipe value place) fun _ => AdvB.pure _) env _⟩
  | ref mutability place =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerPlace place) (borrowTo mutability) (advB_borrowTo mutability) env _⟩
  | slice mutability view low high origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext (lowerView view)
        (fun viewed => do
          let first ← lowerBound low
          let last ← lowerBound high
          emitDef (.viewSlice mutability viewed first last (some origin)))
        (fun _ => AdvB.bind (advB_lowerBound low) fun _ =>
          AdvB.bind (advB_lowerBound high) fun _ => advB_emitDef _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(advB_lowerView view env before _ _ rfl).ext,
        bind_suffix_ext (lowerBound low)
          (fun first => do
            let last ← lowerBound high
            emitDef (.viewSlice mutability (lowerView view env before).1 first last (some origin)))
          (fun _ => AdvB.bind (advB_lowerBound high) fun _ => advB_emitDef _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(advB_lowerView view env before _ _ rfl).ext.trans
          (advB_lowerBound low env (lowerView view env before).2 _ _ rfl).ext,
        bind_suffix_ext (lowerBound high)
          (fun last => emitDef (.viewSlice mutability (lowerView view env before).1
            (lowerBound low env (lowerView view env before).2).1 last (some origin)))
          (fun _ => advB_emitDef _) env _⟩
  | len view =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerView view) (fun value => emitDef (.viewLen value))
      (fun _ => advB_emitDef _) env _⟩
  | un operation expression origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerExpr expression)
      (fun value => do let type ← intTyOf value; emitDef (.un operation type value (some origin)))
      (fun value => AdvB.bind (advB_intTyOf value) fun _ => advB_emitDef _) env _⟩
  | bin operation left right origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext (lowerExpr left)
        (fun x => do let y ← lowerExpr right; let type ← intTyOf x; emitDef (.bin operation type x y (some origin)))
        (fun x => AdvB.bind (advB_lowerExpr right) fun y => AdvB.bind (advB_intTyOf x) fun _ => advB_emitDef _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(advB_lowerExpr left env before _ _ rfl).ext,
        bind_suffix_ext (lowerExpr right)
          (fun y => do let type ← intTyOf (lowerExpr left env before).1
                       emitDef (.bin operation type (lowerExpr left env before).1 y (some origin)))
          (fun _ => AdvB.bind (advB_intTyOf _) fun _ => advB_emitDef _) env _⟩
  | cmp operation left right =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext (lowerExpr left)
        (fun x => do
          let y ← lowerExpr right
          match (← valTy x) with
          | .data (.int type) => emitDef (.cmp operation type x y)
          | _ => emitDef (.boolCmp operation x y))
        (fun x => AdvB.bind (advB_lowerExpr right) fun y => comparison_tail_advances operation x y) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(advB_lowerExpr left env before _ _ rfl).ext,
        bind_suffix_ext (lowerExpr right)
          (fun y => do
            match (← valTy (lowerExpr left env before).1) with
            | .data (.int type) => emitDef (.cmp operation type (lowerExpr left env before).1 y)
            | _ => emitDef (.boolCmp operation (lowerExpr left env before).1 y))
          (fun y => comparison_tail_advances operation (lowerExpr left env before).1 y) env _⟩
  | not expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerExpr expression) (fun value => emitDef (.boolNot value))
      (fun _ => advB_emitDef _) env _⟩
  | conv kind target expression origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    cases target <;> exact ⟨.refl _, bind_suffix_ext (lowerExpr expression)
      (fun value => do
        let source ← intTyOf value
        emitDef (.conv kind source _ value (some origin)))
      (fun value => AdvB.bind (advB_intTyOf value) fun _ => advB_emitDef _) env _⟩
  | call function arguments origin =>
    have span := argumentChildren_span member
    refine ⟨span.1, span.2.trans ?_⟩
    exact bind_suffix_ext (lowerArgs arguments)
      (fun args => do
        let returned ← emitDef (.call function args (some origin))
        if (← read).mod.noReturn function then emitTerm .unreachable
        pure returned)
      (fun args => call_tail_advances function args origin) env before
  | push place expression origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext (lowerPlace place)
        (fun address => do let value ← lowerExpr expression; emitDef (.push address value origin))
        (fun _ => AdvB.bind (advB_lowerExpr expression) fun _ => advB_emitDef _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(advB_lowerPlace place env before _ _ rfl).ext,
        bind_suffix_ext (lowerExpr expression)
          (fun value => emitDef (.push (lowerPlace place env before).1 value origin)) (fun _ => advB_emitDef _) env _⟩
  | pop place origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerPlace place) (fun address => emitDef (.pop address origin))
      (fun _ => advB_emitDef _) env _⟩
  | arrLit type expressions =>
    have span := expressionChildren_span member
    exact ⟨span.1, span.2.trans (bind_suffix_ext (lowerExprs expressions)
      (fun values => emitDef (.arrLit type values)) (fun _ => advB_emitDef _) env before)⟩
  | fill type expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerExpr expression) (fun value => emitDef (.arrFill type value))
      (fun _ => advB_emitDef _) env _⟩
  | structLit type expressions =>
    have span := expressionChildren_span member
    exact ⟨span.1, span.2.trans (bind_suffix_ext (lowerExprs expressions)
      (fun values => emitDef (.structLit type values)) (fun _ => advB_emitDef _) env before)⟩

#print axioms Fragment.expression_child_span

end Goose.Lower.Validation.SourceReplacementWriterLedger
