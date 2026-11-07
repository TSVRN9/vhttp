# citations.py: the citation gate (C1: an RFC-derived rule or close code with no RFC citation). Run as python3 -I.
#   cite ROOT        every allowed_*err / *_allowed_err spec fn and every exec fn that pins a close code carries, in the
#                    contiguous comment block above it (doc comment and attributes included), a
#                    `//= https://www.rfc-editor.org/rfc/rfcN#section` line followed by a `//#` quote line. The quote text
#                    is checked against the RFC by scripts/check-quotes.sh.
#   closes ROOT TSV  every exec fn that pins a close code is the fn column (crate module fn) of some row of TSV.
# A close-code fn is an exec fn (tools/acceptance.py's scanner) whose ensures contain `close_spec() == Some((app, code, reason))`
# with a numeric literal, a codes.rs constant or a call (a mapping spec fn such as report_code, cited too) in `code`; a code
# passed in as a parameter pins nothing here (its callers do).
# Fails closed: no allowed predicate, no close-code fn, no codes.rs constant or an unreadable input is an error.
import importlib.util
import os
import re
import sys


def die(msg):
    print('citations: ' + msg, file=sys.stderr)
    sys.exit(1)


def load_acc():
    sys.dont_write_bytecode = True  # no tools/__pycache__ in the caller's tree
    spec = importlib.util.spec_from_file_location('acceptance', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'acceptance.py'))
    acc = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(acc)
    return acc


def scan(root):
    """(allowed predicates [(file, line, label)], close-code fns [(file, line, fn path)])"""
    acc = load_acc()
    try:
        _, _, _, _, _, sites, apos = acc.scan(root)
        codes = os.path.join(root, 'crates', 'quic', 'src', 'codes.rs')
        consts = set(re.findall(r'(?<![A-Za-z0-9_])const\s+([A-Z][A-Z0-9_]*)\s*:', acc.strip(open(codes, encoding='utf-8').read())))
    except (ValueError, OSError) as e:
        die('cannot scan crates/: %s' % e)
    if not consts:
        die('no constants found in crates/quic/src/codes.rs')
    line = lambda f, off: open(f, encoding='utf-8').read().count('\n', 0, off) + 1
    preds = [(f, line(f, off), name) for f, off, name in apos]
    cname = re.compile(r'(?<![A-Za-z0-9_])(?:%s)(?![A-Za-z0-9_])|(?<![A-Za-z0-9_])(?:0x[0-9a-fA-F_]+|[0-9]+)(?![A-Za-z0-9_])' % '|'.join(sorted(consts)))
    if not preds:
        die('no allowed_*err spec fn found under crates/')
    closes, maps = [], set()
    for f, off, path, cl, ex in sites:
        e = re.search(r'\bensures\b', cl)
        if not ex or not e:
            continue
        ens = cl[e.start():]
        for m in re.finditer(r'close_spec\s*\(\s*\)\s*==\s*Some\s*\(', ens):
            j = acc.match_paren(ens, m.end() - 1)
            if j < 0:
                die('%s: fn %s: unbalanced Some(..) after close_spec' % (f, path))
            tup = ens[m.end():j - 1].strip().rstrip(',').strip()
            if not tup.startswith('('):
                continue  # a variable, not a (app, code, reason) tuple
            if acc.match_paren(tup, 0) != len(tup):
                die('%s: fn %s: cannot parse the tuple in close_spec() == Some(..)' % (f, path))
            parts = acc.split_top(tup[1:-1])
            if len(parts) != 3:
                die('%s: fn %s: close_spec() == Some(..) is not an (app, code, reason) tuple' % (f, path))
            code = parts[1]
            calls = set(re.findall(r'(?<![A-Za-z0-9_:.])([a-z_][A-Za-z0-9_]*)\s*\(', code))
            if cname.search(code) or calls:
                closes.append((f, line(f, off), path))
                maps |= calls
                break
    # a spec fn that maps a code to the close code (report_code) is a close-code mapping: cited like the fn that uses it
    for n in sorted(maps):
        hit = [(f, line(f, off), n) for f, off, path, cl, ex in sites if not ex and path.split('::')[-1] == n]
        if not hit:
            die('close code computed by %s(..), which is not a spec fn in a scanned verus! block' % n)
        preds += hit
    if not closes:
        die('no close-code fn found under crates/')
    return preds, closes


CITE = re.compile(r'^\s*//= https://www\.rfc-editor\.org/rfc/rfc\d+#\S+\s*$')


def cited(f, ln):
    lines = open(f, encoding='utf-8').read().split('\n')
    blk, i = [], ln - 2  # the line above the fn's own line
    while i >= 0 and re.match(r'\s*(//|#\[)', lines[i]):
        blk.append(lines[i]); i -= 1
    blk.reverse()
    for n, l in enumerate(blk):
        if CITE.match(l):
            rest = [x for x in blk[n + 1:] if not re.match(r'\s*//= \w+=', x)]
            if rest and re.match(r'\s*//#', rest[0]):
                return True
    return False


def cite(root):
    preds, closes = scan(root)
    bad = ['%s:%d: %s has no `//= https://www.rfc-editor.org/rfc/..#..` citation with a `//#` quote in the comment block above it'
           % (os.path.relpath(f, root), ln, n) for f, ln, n in preds + closes if not cited(f, ln)]
    if bad:
        die('\n'.join(bad))
    print('citations: ok (%d allowed predicates and %d close-code fns, each cited)' % (len(preds), len(closes)))


def rows(root, tsv):
    _, closes = scan(root)
    try:
        t = open(tsv, encoding='utf-8').read()
    except OSError as e:
        die('cannot read %s: %s' % (tsv, e))
    have = {'::'.join(f[1:4]) for f in (l.split('\t') for l in t.split('\n') if l.strip() and not l.startswith('#')) if len(f) > 3}
    bad = ['%s:%d: close-code fn %s has no row in tools/mutants.tsv (crate module fn); add a delete-the-close or wrong-code mutant'
           % (os.path.relpath(f, root), ln, p) for f, ln, p in closes if p not in have]
    if bad:
        die('\n'.join(bad))
    print('citations: %d close-code fns, each named by a mutant row' % len(closes))


def main(a):
    if a[:1] == ['cite'] and len(a) == 2:
        cite(a[1])
    elif a[:1] == ['closes'] and len(a) == 3:
        rows(a[1], a[2])
    else:
        die('usage: see the header of tools/citations.py')


main(sys.argv[1:])
