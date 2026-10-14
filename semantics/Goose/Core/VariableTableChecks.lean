import Goose.Core.Validate

namespace Goose.Core.VariableTableChecks

def refSliceTy : Ty := .ref .mutable (.slice .mutable (.int .i64))

def emptyEntry : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [] none, summary := .unknown }

def sliceReceiver : Impl :=
  { name := "receiver", params := #[⟨0, .byRef⟩], results := #[],
    vars := #[⟨"p", refSliceTy, .immutable, 0, 0⟩],
    body := .mk 0 [] none, summary := .unknown }

def parameterSlice : Module :=
  { files := #["reference-slice.goose"], types := #[], globals := #[],
    impls := #[emptyEntry, sliceReceiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "receiver", [(0, [.param 0])], [], [(0, [.param 0])]⟩],
    entry := 0, origins := #[⟨0, 1, "test"⟩] }

def undeclaredSliceSlot : Module :=
  { parameterSlice with
    impls := #[{ emptyEntry with vars := sliceReceiver.vars }],
    contexts := #[⟨0, "main", [(0, [])], [], []⟩] }

def unusedStorableSlot : Module :=
  { parameterSlice with
    impls := #[{ emptyEntry with vars := #[⟨"unused", .int .i64, .immutable, 0, 0⟩] }],
    contexts := #[⟨0, "main", [], [], []⟩] }

#guard match validate undeclaredSliceSlot with
  | .error r => r.rule == .type
  | _ => false

#guard match validate parameterSlice with
  | .ok () => true
  | _ => false

#guard match validate unusedStorableSlot with
  | .ok () => true
  | _ => false

end Goose.Core.VariableTableChecks
