"""Parse Isla's textual trace output into nested lists of strings."""

from __future__ import annotations

import re

from .errors import Unsupported

# Whitespace, comments, parentheses, strings, |quoted symbols|, and plain atoms.
_TOKEN = re.compile(r'\s+|;[^\n]*|\(|\)|"(?:[^"\\]|\\.)*"|\|[^|]*\||[^\s()";]+')

SExpr = str | list["SExpr"]


def _restore_commented_closers(text: str) -> str:
    """Isla can print closing parentheses inside a trailing `;` comment; move them out."""
    lines = []
    for line in text.splitlines():
        lines.append(line)
        comment = line.find(";")
        if comment >= 0 and (m := re.search(r"(\)+)\s*$", line[comment + 1 :])):
            lines.append(m.group(1))
    return "\n".join(lines)


def parse(text: str) -> list[SExpr]:
    """Return the top-level expressions; `|name|` symbols lose their bars."""
    stack: list[list[SExpr]] = [[]]
    for m in _TOKEN.finditer(_restore_commented_closers(text)):
        tok = m.group(0)
        if tok.isspace() or tok.startswith(";"):
            continue
        if tok == "(":
            stack.append([])
        elif tok == ")":
            if len(stack) == 1:
                raise Unsupported("unbalanced ')' in trace")
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok.strip("|"))
    if len(stack) != 1:
        raise Unsupported("unbalanced '(' in trace")
    return stack[0]


def render(e: SExpr) -> str:
    return e if isinstance(e, str) else "(" + " ".join(render(x) for x in e) + ")"
