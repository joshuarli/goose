import Goose.Lower.Validation.SourceReplacementWriterLedgerChildTypesBlocks

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

def OrdinaryStatement_types : Stmt → Prop
  | .ifS .. | .while .. | .forRange .. | .forEach .. => False
  | _ => True

theorem Fragment.statement_ordinary_child_span_types {loop : Option LoopCtx} {statement : Stmt} {child : Fragment}
    {env : LEnv} {before start : LS} {index : Nat} (ordinary : OrdinaryStatement_types statement)
    (row : (Fragment.statement loop statement).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) ((Fragment.statement loop statement).finish env before) := by
  have member := Fragment.child_member row
  cases statement with
  | ifS condition yes no origin => exact False.elim ordinary
  | «while» condition body origin => exact False.elim ordinary
  | forRange varId low high body origin => exact False.elim ordinary
  | forEach varId index view byRef body origin => exact False.elim ordinary
  | brk origin => simp [Fragment.children] at member
  | cont origin => simp [Fragment.children] at member
  | abort kind origin => simp [Fragment.children] at member
  | letS slot expression origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression)
      (fun value => do let converted ← coerceSlot slot value origin; emitEffect (.slotInit slot converted (some origin)))
      (fun value => TypeRun.bind (types_coerceSlot slot value origin) fun _ => types_emitEffect _) env _⟩
  | rebind slot expression origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression)
      (fun value => do
        let converted ← coerceSlot slot value origin
        let address ← emitDef (.slotAddr slot)
        emitEffect (.store address converted (some origin)))
      (fun value => TypeRun.bind (types_coerceSlot slot value origin) fun _ =>
        TypeRun.bind (types_emitDef _) fun _ => types_emitEffect _) env _⟩
  | assign place expression origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext_types (lowerPlace place)
        (fun address => do let value ← lowerExpr expression; emitEffect (.store address value (some origin)))
        (fun _ => TypeRun.bind (types_lowerExpr expression) fun _ => types_emitEffect _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(types_lowerPlace place env before _ _ rfl),
        bind_suffix_ext_types (lowerExpr expression)
          (fun value => emitEffect (.store (lowerPlace place env before).1 value (some origin)))
          (fun _ => types_emitEffect _) env _⟩
  | assignOp operation place expression origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext_types (lowerPlace place)
        (fun address => do
          let old ← emitDef (.load address)
          let value ← lowerExpr expression
          let type ← intTyOf old
          let result ← emitDef (.bin operation type old value (some origin))
          emitEffect (.store address result (some origin)))
        (fun _ => TypeRun.bind (types_emitDef _) fun old => TypeRun.bind (types_lowerExpr expression) fun _ =>
          TypeRun.bind (types_intTyOf old) fun _ => TypeRun.bind (types_emitDef _) fun _ => types_emitEffect _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      let addressed := lowerPlace place env before
      let loaded := emitDef (.load addressed.1) env addressed.2
      exact ⟨(types_lowerPlace place env before _ _ rfl).trans (types_emitDef _ env addressed.2 _ _ rfl),
        bind_suffix_ext_types (lowerExpr expression)
          (fun value => do
            let type ← intTyOf loaded.1
            let result ← emitDef (.bin operation type loaded.1 value (some origin))
            emitEffect (.store addressed.1 result (some origin)))
          (fun _ => TypeRun.bind (types_intTyOf loaded.1) fun _ => TypeRun.bind (types_emitDef _) fun _ => types_emitEffect _) env _⟩
  | assignWhole place expression origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext_types (lowerPlace place)
        (fun address => do
          emitEffect (.clear address (some origin))
          let value ← lowerExpr expression
          emitEffect (.replace address value (some origin)))
        (fun _ => TypeRun.bind (types_emitEffect _) fun _ => TypeRun.bind (types_lowerExpr expression) fun _ => types_emitEffect _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(types_lowerPlace place env before _ _ rfl).trans (types_emitEffect _ env _ _ _ rfl),
        bind_suffix_ext_types (lowerExpr expression)
          (fun value => emitEffect (.replace (lowerPlace place env before).1 value (some origin)))
          (fun _ => types_emitEffect _) env _⟩
  | expr expression origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression) (fun _ => pure ()) (fun _ => TypeRun.pure _) env _⟩
  | append place view origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext_types (lowerPlace place)
        (fun address => do let value ← lowerView view; emitEffect (.append address value (some origin)))
        (fun _ => TypeRun.bind (types_lowerView view) fun _ => types_emitEffect _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(types_lowerPlace place env before _ _ rfl),
        bind_suffix_ext_types (lowerView view)
          (fun value => emitEffect (.append (lowerPlace place env before).1 value (some origin)))
          (fun _ => types_emitEffect _) env _⟩
  | popN place expression origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext_types (lowerPlace place)
        (fun address => do let value ← lowerExpr expression; emitEffect (.popN address value (some origin)))
        (fun _ => TypeRun.bind (types_lowerExpr expression) fun _ => types_emitEffect _) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      exact ⟨(types_lowerPlace place env before _ _ rfl),
        bind_suffix_ext_types (lowerExpr expression)
          (fun value => emitEffect (.popN (lowerPlace place env before).1 value (some origin)))
          (fun _ => types_emitEffect _) env _⟩
  | resize place size fill origin =>
    cases fill with
    | none =>
      simp only [Fragment.children, Option.map_none, List.mem_cons, List.not_mem_nil, or_false,
        Option.some_ne_none, or_false] at member
      rcases member with same | same
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        exact ⟨.refl _, bind_suffix_ext_types (lowerPlace place)
          (fun address => do let count ← lowerExpr size; emitEffect (.resize address count none (some origin)))
          (fun _ => TypeRun.bind (types_lowerExpr size) fun _ => types_emitEffect _) env _⟩
      · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
        subst start
        exact ⟨(types_lowerPlace place env before _ _ rfl),
          bind_suffix_ext_types (lowerExpr size)
            (fun count => emitEffect (.resize (lowerPlace place env before).1 count none (some origin)))
            (fun _ => types_emitEffect _) env _⟩
    | some expression =>
      simp only [Fragment.children, Option.map_some, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        exact ⟨.refl _, bind_suffix_ext_types (lowerPlace place)
          (fun address => do
            let count ← lowerExpr size
            let value ← lowerExpr expression
            emitEffect (.resize address count (some value) (some origin)))
          (fun _ => TypeRun.bind (types_lowerExpr size) fun _ =>
            TypeRun.bind (types_lowerExpr expression) fun _ => types_emitEffect _) env _⟩
      · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
        subst start
        exact ⟨(types_lowerPlace place env before _ _ rfl),
          bind_suffix_ext_types (lowerExpr size)
            (fun count => do let value ← lowerExpr expression
                             emitEffect (.resize (lowerPlace place env before).1 count (some value) (some origin)))
            (fun _ => TypeRun.bind (types_lowerExpr expression) fun _ => types_emitEffect _) env _⟩
      · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
        subst start
        exact ⟨(types_lowerPlace place env before _ _ rfl).trans (types_lowerExpr size env _ _ _ rfl),
          bind_suffix_ext_types (lowerExpr expression)
            (fun value => emitEffect (.resize (lowerPlace place env before).1
              (lowerExpr size env (lowerPlace place env before).2).1 (some value) (some origin)))
            (fun _ => types_emitEffect _) env _⟩
  | clear place origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerPlace place) (fun address => emitEffect (.clear address (some origin)))
      (fun _ => types_emitEffect _) env _⟩
  | ret value origin =>
    cases value with
    | none => simp [Fragment.children] at member
    | some expression =>
      simp only [Fragment.children, Option.map_some, List.mem_singleton] at member
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
      exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression)
        (fun value => do let converted ← coerceResult value origin; leaveTo 0; emitTerm (.ret [converted] (some origin)))
        (fun value => TypeRun.bind (types_coerceResult value origin) fun _ =>
          TypeRun.bind (types_leaveTo 0) fun _ => types_emitTerm _) env _⟩
  | print arguments origin =>
    have span := printChildren_span_types member
    exact ⟨span.1, span.2.trans (bind_suffix_ext_types (lowerPrintArgs arguments)
      (fun values => emitEffect (.print values (some origin))) (fun _ => types_emitEffect _) env before)⟩
  | assertS expression origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression) _ (fun value => types_assert_core value origin) env _⟩
  | exit expression origin =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression) (fun value => emitTerm (.exit value (some origin)))
      (fun _ => types_emitTerm _) env _⟩

#print axioms Fragment.statement_ordinary_child_span_types

end Goose.Lower.Validation.SourceReplacementWriterLedger
