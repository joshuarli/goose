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

No entries yet.
