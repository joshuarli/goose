import Goose.Construct.Runtime

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct

private theorem encoding_bind_success {α β : Type} (action : Except Core.Stop α)
    (next : α → Except Core.Stop β) (result : β) :
    (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

private theorem encoding_forIn_invariant {α β : Type} (rows : List α) (initial : β)
    (body : α → β → Except Core.Stop (ForInStep β)) (invariant : β → Prop)
    (valid : invariant initial)
    (preserved : ∀ row before step, invariant before → body row before = .ok step → invariant step.value)
    (final : β) (checked : forIn rows initial body = .ok final) : invariant final := by
  induction rows generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at checked
    subst final
    exact valid
  | cons row rows ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, evaluated, remaining⟩ := (encoding_bind_success _ _ _).mp checked
    have nextValid := preserved row initial step valid evaluated
    cases step with
    | done value =>
      simp only [pure, Except.pure, Except.ok.injEq] at remaining
      subst final
      exact nextValid
    | yield value => exact ih value nextValid remaining

private theorem intBytes_size (ty : Core.IntTy) (value : Int) :
    (intBytes ty value).size = ty.bits / 8 := by
  cases ty <;> simp [intBytes, Core.IntTy.bits, Std.Legacy.Range.forIn_eq_forIn_range', List.range'_succ]

private theorem encoding_parts_size (encode : Value → Except Core.Stop ByteArray) (width : Nat)
    (sized : ∀ value bytes, encode value = .ok bytes → bytes.size = width)
    (values : List Value) (parts : List ByteArray) (initial : ByteArray)
    (encoded : values.mapM encode = .ok parts) :
    (parts.foldl (· ++ ·) initial).size = initial.size + values.length * width := by
  induction values generalizing parts initial with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at encoded
    subst parts
    simp
  | cons value values ih =>
    simp only [List.mapM_cons] at encoded
    obtain ⟨part, first, rest⟩ := (encoding_bind_success _ _ _).mp encoded
    obtain ⟨remaining, tail, completed⟩ := (encoding_bind_success _ _ _).mp rest
    simp only [pure, Except.pure, Except.ok.injEq] at completed
    subst parts
    simp only [List.foldl_cons]
    rw [ih remaining (initial ++ part) tail, ByteArray.size_append, sized value part first]
    simp only [List.length_cons, Nat.add_mul]
    omega

theorem fixedBytes_size (fuel : Nat) (layout : LayoutEnv) (ty : Ty) (value : Value)
    (bytes : ByteArray) (width : Nat) (sized : fixedByteSize? layout ty = some width)
    (encoded : fixedBytes fuel layout ty value = .ok bytes) : bytes.size = width := by
  induction fuel generalizing ty value bytes width with
  | zero => cases encoded
  | succ fuel ih =>
    cases ty with
    | int type =>
      cases value <;> simp only [fixedBytes, beq_iff_eq] at encoded
      all_goals try { cases encoded }
      split at encoded
      · rename_i equal
        cases equal
        cases encoded
        simpa only [fixedByteSize?, Option.some.injEq] using (intBytes_size type _).trans (Option.some.inj sized)
      · cases encoded
    | bool =>
      cases value <;> simp only [fixedBytes] at encoded
      all_goals try { cases encoded }
      cases encoded
      simp only [fixedByteSize?, Option.some.injEq] at sized
      simpa [ByteArray.size] using sized
    | arr element count =>
      cases elementLayout : fixedByteSize? layout element with
      | none => simp [fixedByteSize?, elementLayout] at sized
      | some elementWidth =>
        have widthEq : width = count * elementWidth := by simpa [fixedByteSize?, elementLayout] using sized.symm
        subst width
        cases value <;> simp only [fixedBytes] at encoded
        all_goals try { cases encoded }
        split at encoded
        · cases encoded
        · rename_i elements countEq
          obtain ⟨parts, partsEncoded, completed⟩ := (encoding_bind_success _ _ _).mp encoded
          simp only [pure, Except.pure, Except.ok.injEq] at completed
          subst bytes
          have partsSize := encoding_parts_size (fixedBytes fuel layout element) elementWidth
            (fun value bytes encoded => ih element value bytes elementWidth elementLayout encoded)
          have countSame : elements.size = count := by simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using countEq
          simpa only [ByteArray.size_empty, Nat.zero_add, Array.length_toList, countSame] using
            partsSize elements.toList parts ByteArray.empty partsEncoded
    | structT id fields =>
      cases value <;> simp only [fixedBytes] at encoded
      all_goals try { cases encoded }
      split at encoded
      · cases encoded
      · rename_i actual values sameId
        cases descriptorAt : layout.structs[id]? with
        | none => simp [descriptorAt] at encoded
        | some descriptor =>
          simp only [descriptorAt] at encoded
          split at encoded
          · cases encoded
          · have widthEq : descriptor.byteSize = width := by
              unfold fixedByteSize? at sized
              split at sized
              · cases sized
              · simpa only [descriptorAt, Option.map_some, Option.some.injEq] using sized
            obtain ⟨final, loop, completed⟩ := (encoding_bind_success _ _ _).mp encoded
            simp only [pure, Except.pure, Except.ok.injEq] at completed
            subst bytes
            have preserved := encoding_forIn_invariant _ _ _
              (fun bytes : ByteArray => bytes.size = descriptor.byteSize) (by simp [ByteArray.size])
              (by
                intro row before step valid checked
                obtain ⟨part, partEncoded, remaining⟩ := (encoding_bind_success _ _ _).mp checked
                split at remaining
                · cases remaining
                · obtain ⟨next, loop, completed⟩ := (encoding_bind_success _ _ _).mp remaining
                  simp only [pure, Except.pure, Except.ok.injEq] at completed
                  subst step
                  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at loop
                  have inner := encoding_forIn_invariant _ _ _
                    (fun bytes : ByteArray => bytes.size = descriptor.byteSize) valid
                    (by
                      intro index before step valid checked
                      split at checked
                      · simp only [pure, Except.pure, Except.ok.injEq] at checked
                        subst step
                        simpa using valid
                      · cases checked) next loop
                  exact inner) final loop
            exact preserved.trans widthEq
    | _ => simp [fixedByteSize?] at sized

end Goose.Proofs.ConstructionAcceptedExecution

#print axioms Goose.Proofs.ConstructionAcceptedExecution.fixedBytes_size
