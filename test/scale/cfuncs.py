"""Functions in the C that goose writes, and what two emissions share.

The compiler writes every function of a program after the marker below, each
as a definition starting in column 0 and ending at a lone closing brace. A
function is named after its source function, then `_g`, then the
specialization number (absent for the first), then `_er` for the form that
requests an element run. The numbers follow creation order, so adding one
specialization renames others; every comparison here masks them.
"""

import re

CODE_MARKER = "/* ---- code ---- */"
DEFINITION = re.compile(r"^(?:static |GS_API )?[A-Za-z_][\w \*]*?\b(\w+)\([^;]*\) \{$")
# `name_g`, `name_g_12`, `name_g_12_er`; a nested function keeps the same shape.
NAME = re.compile(r"\b([A-Za-z_]\w*?)_g(?:_\d+)?(?:_er)?\b")
# The source line a runtime check reports, as the generated code passes it.
LINE = re.compile(r"(gs_file\d+), \d+\)")


def functions(c_text):
    """{C function name: body text} for the program's own functions."""
    start = c_text.find(CODE_MARKER)
    if start < 0:
        raise ValueError("no code section in the C text")
    found, name, lines = {}, None, []
    for line in c_text[start:].splitlines():
        if name is None:
            m = DEFINITION.match(line)
            if m and "(" in line:
                name, lines = m.group(1), [line]
        else:
            lines.append(line)
            if line == "}":
                found[name] = "\n".join(lines)
                name = None
    return found


def source_name(c_name):
    """The source function a C function was emitted for, or None for a
    function the compiler wrote on its own (globals, program entry)."""
    m = re.fullmatch(r"(.+?)_g(?:_\d+)?(?:_er)?", c_name)
    return m.group(1) if m else None


def mask(body, lines=True):
    """A body with creation-order numbers masked; with `lines`, also the
    source line numbers of its runtime checks."""
    body = re.sub(r"\b(\w+?_g)(?:_\d+)?((?:_er)?)\b", r"\1_#\2", body)
    return LINE.sub(r"\1, #)", body) if lines else body


def by_source(c_text, lines=True):
    """{source function: sorted list of masked bodies}, one body per emitted
    function. A function the compiler wrote on its own is keyed by its C
    name."""
    found = {}
    for name, body in functions(c_text).items():
        found.setdefault(source_name(name) or name, []).append(mask(body, lines))
    return {k: sorted(v) for k, v in found.items()}


def outside_functions(c_text):
    """The C text without the bodies of the program's own functions: the
    runtime, type and data declarations."""
    start = c_text.find(CODE_MARKER)
    kept, inside = [c_text[:start]], False
    for line in c_text[start:].splitlines():
        if not inside and DEFINITION.match(line) and "(" in line:
            inside = True
        if not inside:
            kept.append(line)
        elif line == "}":
            inside = False
    return "\n".join(kept)


def classes(c_text):
    """{C function name: class} where two functions share a class when
    their bodies are equal once each callee is replaced by its class.
    Starts with one class per source function and refines until stable, so
    mutually recursive functions compare as components do."""
    funcs = functions(c_text)
    cls = {n: (source_name(n) or n, 0) for n in funcs}

    def canon(body):
        def sub(m):
            return "@%s:%d" % cls[m.group(0)] if m.group(0) in cls else m.group(0)

        return re.sub(r"\b\w+_g(?:_\d+)?(?:_er)?\b", sub, LINE.sub(r"\1, #)", body))

    while True:
        ids, refined = {}, {}
        for n in sorted(funcs):
            key = (cls[n], canon(funcs[n]))
            refined[n] = (cls[n][0], ids.setdefault(key, len(ids)))
        if len(set(refined.values())) == len(set(cls.values())):
            return refined
        cls = refined


def implementations(c_text):
    """{source function: number of distinct implementations}: the classes
    of `classes` counted per source function."""
    count = {}
    for name, cl in classes(c_text).items():
        src = source_name(name)
        if src is not None:
            count.setdefault(src, set()).add(cl)
    return {k: len(v) for k, v in sorted(count.items())}
