# Decisions

Each entry records one disagreement between the Lean model and the legacy
compiler, and how it was resolved. Where the language specification states the
behavior, it wins; where it is silent, the legacy compiler's behavior wins.

Entry shape:

```text
## D-<number> <short title>

- Specification: the quoted text, or "silent".
- Legacy compiler: the observed behavior.
- Model: the behavior chosen.
- Reproducer: the minimized program, path under `test/`.
- Status: open | resolved.
```

## D-1 `print` writes its line after all arguments are evaluated

- Specification: `docs/goose_spec.md` section 3.7: the builtins "evaluate and
  render their arguments in order, each just before its text", and `print`
  "writes the forms to standard output followed by a newline, as one write".
  The text does not say when the bytes of an earlier argument reach the
  output relative to output produced while evaluating a later argument.
- Legacy compiler: all arguments are evaluated first and the line is written
  once, so output a later argument produces comes before the whole line. On
  the reproducer, `goose --jit` prints `inner` and then `a5b`. An eager
  reading would print `a` before the callee's line.
- Model: follows the compiler. `execStmt` renders every `print` argument,
  then appends the joined line and a line feed to the trace in one step.
- Reproducer: `test/semantics/malformed/print_argument_order.goose`.
- Status: resolved.
