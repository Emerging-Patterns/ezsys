# ezsys specification

This is the list of every behavior ezsys guarantees, each under a stable requirement ID. Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in `LAWS.bend` that passes the proof gate. A **Trusted** requirement is an assumption ezsys cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose laws have not all landed has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: the first line `bend PROOF.bend` prints is exactly `ALL PROOFS CHECK`. Tests and fixtures are never evidence for a requirement.

No requirement is listed yet, so this file promises nothing.

## Format

A requirement table is any table whose header row is exactly `| ID | Requirement | Level | Status | Law |`. An ID is uppercase segments joined by hyphens, at least two (`[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`), unique within the requirement tables, and never reused once released. Level is `Proved` or `Trusted`. Status is `proved` or `pending` for a Proved row and empty for a Trusted row. A Law cell holds `<path> <law>` entries, paths relative to this file, separated by `; `. A proved row names one or more laws, and together they prove it. A pending row may name laws that each prove part of it; the row stays pending until its requirement is proved in full, and "Left to prove" says what is missing.

A law proves a requirement when a comment line `# <ID>`, alone on its line, sits in the unbroken comment block directly above its `law` line. A law may carry several tags, one per line:

```
# LAW: a template with no marker is left unchanged
# SYS-TEXT-1
law fill_unmarked:
```

A tag may name a proved or a pending requirement, never a Trusted one or an ID no requirement table lists. bolt's `trace` rule checks all of this over the whole tree, and its `closed` rule rejects a law with no binder; both are errors in `bolt.bend`.

## Requirements

None yet.

## Trust boundary

None yet.
