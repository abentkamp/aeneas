#!/usr/bin/env python3
"""
Rename UScalar/IScalar accessor methods across Lean files:
  - UScalar.bv  -> UScalar.toBitVec  (struct field)
  - IScalar.bv  -> IScalar.toBitVec  (struct field)
  - UScalar.val -> UScalar.toNat     (def)
  - IScalar.val -> IScalar.toInt     (def)

Also renames theorem/def names that embed these as segments.
"""

import re
import sys
from pathlib import Path

SIGNED_TYPES   = ["IScalar", "I8", "I16", "I32", "I64", "I128", "Isize"]
UNSIGNED_TYPES = ["UScalar", "U8", "U16", "U32", "U64", "U128", "Usize"]
ALL_SCALAR_TYPES = SIGNED_TYPES + UNSIGNED_TYPES

# Matches From<X><Y> where Y is a known scalar type
FROM_PREFIX_RE = re.compile(
    r'^From[A-Z][a-zA-Z0-9]*('
    + '|'.join(re.escape(t) for t in ALL_SCALAR_TYPES)
    + r')$'
)


def classify_prefix(prefix: str) -> str | None:
    """Return 'signed', 'unsigned', or None."""
    if prefix in SIGNED_TYPES:
        return "signed"
    if prefix in UNSIGNED_TYPES:
        return "unsigned"
    # From<X><Y> pattern — classify by the output type Y
    m = FROM_PREFIX_RE.match(prefix)
    if m:
        target = m.group(1)
        if target in SIGNED_TYPES:
            return "signed"
        if target in UNSIGNED_TYPES:
            return "unsigned"
    return None


def rename_name_part(name: str, context: str | None) -> str:
    """Rename _val_/_bv_ segments in a name (the part after the last dot)."""
    # bv segments -> toBitVec (unambiguous)
    name = re.sub(r'(?<![a-zA-Z0-9])bv_', 'toBitVec_', name)
    name = re.sub(r'_bv(?![a-zA-Z0-9])',  '_toBitVec', name)
    name = re.sub(r'^bv$', 'toBitVec', name)

    # val segment -> toNat or toInt
    if context == "signed":
        name = re.sub(r'(?<![a-zA-Z0-9])val_', 'toInt_', name)
        name = re.sub(r'_val(?![a-zA-Z0-9])',  '_toInt', name)
        name = re.sub(r'^val$', 'toInt', name)
    elif context == "unsigned":
        name = re.sub(r'(?<![a-zA-Z0-9])val_', 'toNat_', name)
        name = re.sub(r'_val(?![a-zA-Z0-9])',  '_toNat', name)
        name = re.sub(r'^val$', 'toNat', name)

    return name


# ---------------------------------------------------------------------------
# Pass A: qualified name replacement (e.g. UScalar.val_eq, U8.bv_toNat, ...)
# Matches  <ScalarPrefix>.<ident>  and renames the ident part.
# ---------------------------------------------------------------------------

# Build pattern for all scalar prefixes plus From<X><Y> prefixes
_PREFIXES_ALT = '|'.join(re.escape(t) for t in ALL_SCALAR_TYPES)
# Also match From<X><Y> where X and Y are any capitalized identifiers
QUAL_RE = re.compile(
    r'\b((?:From[A-Z][a-zA-Z0-9]*|' + _PREFIXES_ALT + r'))\.([a-zA-Z_][a-zA-Z0-9_]*)\b'
)


def _rename_qual(m: re.Match) -> str:
    prefix = m.group(1)
    name   = m.group(2)
    ctx    = classify_prefix(prefix)
    new_name = rename_name_part(name, ctx)
    if new_name == name:
        return m.group(0)
    return prefix + "." + new_name


def pass_a_qualified_names(text: str) -> str:
    """Rename idents in qualified scalar names (covers both declarations and proof bodies)."""
    return QUAL_RE.sub(_rename_qual, text)


# ---------------------------------------------------------------------------
# Pass B: struct field .bv -> .toBitVec
# ---------------------------------------------------------------------------

def pass_b_bv_field(text: str) -> str:
    # Structure field declaration:  "bv : BitVec"
    text = re.sub(r'\bbv(\s*:\s*BitVec\b)', r'toBitVec\1', text)
    # Named constructor field:  "{ bv :="  or  "⟨ bv :="
    text = re.sub(r'(\{[^}]*?\s)bv(\s*:=)', r'\1toBitVec\2', text)
    # Field access: .bv (the dot already prevents mid-word matching)
    text = re.sub(r'\.bv\b', '.toBitVec', text)
    # Bare theorem names that start with bv_ (used in simp/rw lists without qualification).
    # These are all scalar-specific theorem names; the .bv field accesses are already
    # handled above.  Apply ONLY when not preceded by . (field access) or letter.
    text = re.sub(r'(?<![.\w])bv_', 'toBitVec_', text)
    return text


# ---------------------------------------------------------------------------
# Pass C: unqualified .val -> .toNat or .toInt based on declaration context
# ---------------------------------------------------------------------------

DECL_RE = re.compile(
    r'^\s*'
    r'(?:@\[.*?\]\s*)*'                              # attributes (greedy line-level)
    r'(?:private\s+|protected\s+)?'
    r'(?:noncomputable\s+)?'
    r'(?:theorem|def|abbrev|instance|lemma|irreducible_def)\s+'
    r'((?:From[A-Z][a-zA-Z0-9]*|' + _PREFIXES_ALT + r')'  # prefix
    r'(?:\.[a-zA-Z_][a-zA-Z0-9_]*)*)'               # dotted name tail
)


_SIGNED_RE   = re.compile(r'\b(?:' + '|'.join(re.escape(t) for t in SIGNED_TYPES)   + r')\b')
_UNSIGNED_RE = re.compile(r'\b(?:' + '|'.join(re.escape(t) for t in UNSIGNED_TYPES) + r')\b')


def get_decl_context(line: str) -> str | None:
    """Extract the scalar context from a declaration line, if any."""
    m = DECL_RE.match(line)
    if m:
        full_name = m.group(1)
        prefix = full_name.split('.')[0]
        ctx = classify_prefix(prefix)
        if ctx is not None:
            return ctx

    # For declarations whose name doesn't carry a scalar prefix (e.g. instance),
    # look for scalar type mentions anywhere in the line.
    stripped = line.lstrip()
    if stripped.startswith(('theorem ', 'def ', 'abbrev ', 'instance ', 'lemma ', 'irreducible_def ')):
        has_signed   = bool(_SIGNED_RE.search(line))
        has_unsigned = bool(_UNSIGNED_RE.search(line))
        if has_unsigned and not has_signed:
            return "unsigned"
        if has_signed and not has_unsigned:
            return "signed"

    return None


def pass_c_unqualified_val(lines: list[str]) -> list[str]:
    """Replace .val and bare val (in lemma lists) using per-declaration context."""
    result = []
    ctx: str | None = None

    for line in lines:
        # Update context if this is a declaration line
        new_ctx = get_decl_context(line)
        if new_ctx is not None:
            ctx = new_ctx

        repl_dot = '.toInt' if ctx == "signed" else '.toNat' if ctx == "unsigned" else None
        repl_bare = 'toInt' if ctx == "signed" else 'toNat' if ctx == "unsigned" else None

        if repl_dot:
            # Replace all remaining .val occurrences.
            # Pass A already renamed UScalar.val -> UScalar.toNat and
            # IScalar.val -> IScalar.toInt, so only unqualified .val remains.
            line = re.sub(r'\.val\b', repl_dot, line)

        if repl_bare:
            # Replace bare 'val' when used as a lemma/def name inside [...] tactic lists.
            # Matches: [val, ...], [..., val, ...], [..., val], also ← val
            # We look for val at word boundaries preceded by [, comma, ←, or space
            # and followed by ], comma, or space.
            line = re.sub(r'(?<=[\[,\s←])val(?=[\],\s])', repl_bare, line)

        result.append(line)
    return result


# ---------------------------------------------------------------------------
# Main file processor
# ---------------------------------------------------------------------------

def process_file(path: Path, dry_run: bool = False) -> bool:
    original = path.read_text(encoding='utf-8')

    text = original
    text = pass_a_qualified_names(text)
    text = pass_b_bv_field(text)

    lines = text.splitlines(keepends=True)
    lines = pass_c_unqualified_val(lines)
    text = ''.join(lines)

    if text == original:
        return False
    if not dry_run:
        path.write_text(text, encoding='utf-8')
    return True


def find_lean_files(roots: list[Path]) -> list[Path]:
    files = []
    for root in roots:
        if root.exists():
            files.extend(root.rglob('*.lean'))
    return sorted(files)


def main():
    repo = Path(__file__).parent.parent
    lean_roots = [
        repo / 'backends' / 'lean',
        repo / 'tests'   / 'lean',
    ]

    dry_run = '--dry-run' in sys.argv
    verbose = '--verbose' in sys.argv or dry_run

    files = find_lean_files(lean_roots)
    modified = 0
    for f in files:
        changed = process_file(f, dry_run=dry_run)
        if changed:
            modified += 1
            if verbose:
                print(f'  modified: {f.relative_to(repo)}')

    action = '[DRY RUN] Would modify' if dry_run else 'Modified'
    print(f'{action} {modified} / {len(files)} files.')


if __name__ == '__main__':
    main()
