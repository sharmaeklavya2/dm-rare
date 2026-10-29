#!/usr/bin/env python3
"""Print Lean declarations with proof bodies stripped.

Keeps `def`/`abbrev`/`instance`/`structure`/`inductive` bodies (those *are*
the definition) and replaces the proof of every `theorem`/`lemma`/`example`
with ` := by sorry /- proof omitted -/` (syntactically valid, so the output
still compiles). Docstrings, attributes, `variable`, `import`, `open`,
section headers, and comments are all kept so signatures stay readable.

Usage:  lean-sig.py FILE.lean [FILE.lean ...]

Heuristics (no full Lean parse): a declaration begins at a line whose first
token is a decl keyword (after leading whitespace). We only strip *tactic*
proofs, detected by ` := by` (same line, or `:=` at end of a line with `by`
starting the next non-blank line). Term-mode proofs (` := <term>`) are left
intact — they are usually short, and this makes the split robust to `let ... :=`
and other `:=` occurrences inside the statement. The proof body is the run of
lines indented deeper than the keyword; we drop it but preserve the blank line
that separates one declaration from the next.
"""
import re
import sys

STRIP = {"theorem", "lemma", "example"}
# All decl keywords we recognize as "starts a new declaration".
DECL = STRIP | {
    "def", "abbrev", "instance", "structure", "inductive", "class",
    "opaque", "axiom", "noncomputable",  # noncomputable handled as modifier below
}
KEYWORD_RE = re.compile(r"^(\s*)((?:@\[[^\]]*\]\s*)*)"
                        r"(?:(?:private|protected|public|noncomputable|scoped|local)\s+)*"
                        r"(theorem|lemma|example|def|abbrev|instance|structure|inductive|class|opaque|axiom)\b")


def indent_of(line: str) -> int:
    return len(line) - len(line.lstrip())


ASSIGN_BY = re.compile(r":=\s*by\b")     # tactic proof on a single line
ASSIGN_EOL = re.compile(r":=\s*(--.*)?$")  # ":=" at end of a (possibly commented) line
BY_START = re.compile(r"by\b")


def find_tactic_proof(lines, i, base, n):
    """Locate the start of a tactic (` := by`) proof for the declaration at `i`.

    Returns `(split_idx, kind)` where `kind` is 'inline' (`:= by` on one line) or
    'nextline' (`:=` ends line `split_idx`, `by` begins the next non-blank line),
    or `None` if this is a term-mode proof / no proof was found before the
    statement region ends (a dedent to `base`).
    """
    j = i
    while j < n:
        cur = lines[j]
        if j > i and cur.strip() and indent_of(cur) <= base:
            return None                    # dedented out of the statement: term proof / next decl
        if ASSIGN_BY.search(cur):
            return (j, "inline")
        if ASSIGN_EOL.search(cur):         # ":=" dangles; is the proof `by` on the next line?
            k = j + 1
            while k < n and lines[k].strip() == "":
                k += 1
            if k < n and BY_START.match(lines[k].strip()):
                return (j, "nextline")
            return None                    # ":=" followed by a term → term-mode proof
        j += 1
    return None


def skip_proof_body(lines, j, base, n):
    """Advance past proof-body lines (indent > base), keeping interior blanks but
    stopping *before* the blank line that separates this decl from the next."""
    while j < n:
        cur = lines[j]
        if cur.strip() == "":
            k = j + 1
            while k < n and lines[k].strip() == "":
                k += 1
            if k < n and indent_of(lines[k]) > base:
                j += 1                     # blank sits inside the proof body
                continue
            break                          # blank belongs to the separation → preserve it
        if indent_of(cur) > base:
            j += 1
        else:
            break
    return j


def process(lines):
    out = []
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        m = KEYWORD_RE.match(line)
        if not m or m.group(3) not in STRIP:
            out.append(line)               # non-decl line, or a def/etc. kept verbatim
            i += 1
            continue

        base = len(m.group(1))             # indent of the keyword
        res = find_tactic_proof(lines, i, base, n)
        if res is None:
            out.append(line)               # term-mode proof / no proof → keep verbatim
            i += 1
            continue

        split_idx, kind = res
        out.extend(lines[i:split_idx])     # statement lines before the split line
        last = lines[split_idx]
        if kind == "inline":
            head = last[:ASSIGN_BY.search(last).start()].rstrip()
        else:                              # 'nextline': trim the dangling ":="
            head = ASSIGN_EOL.sub("", last).rstrip()
        out.append(head + " := by sorry /- proof omitted -/")
        i = skip_proof_body(lines, split_idx + 1, base, n)
    return out


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    for path in argv[1:]:
        with open(path) as f:
            lines = f.read().splitlines()
        if len(argv) > 2:
            print(f"\n==== {path} ====")
        print("\n".join(process(lines)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
