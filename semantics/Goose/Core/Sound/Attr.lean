import Lean

/-- Rewrite rules that turn "this validator computation succeeded" into the
facts its steps checked. -/
register_simp_attr chk
