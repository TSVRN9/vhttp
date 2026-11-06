"""Check every Duvet `//#` quote in the given .rs files against the RFC text.

Usage: python3 -I check_quotes.py [--spec-dir DIR] FILE.rs...
Each `//= <url>#<section>` line starts a citation; the `//#` lines that follow, up to the first
other line, are its quote. The quote, with whitespace runs collapsed to one space, must occur in
the named section of DIR/<host>/<path>.txt (default: the repo's .duvet/specifications), whose page
headers and footers are dropped. Prints each bad citation, then `N citations, B bad`; exit 1 if B > 0 (a `//#` line outside any citation counts as bad),
if there are no files or no citations, or if DIR is missing (fail closed).
"""
import os, re, sys

HEAD = re.compile(r'^(?:Appendix )?([A-Z]|\d+)((?:\.\d+)*)\.\s{2}\S')
PAGE = re.compile(r'^(RFC \d+ .* \d{4}|.*\[Page \d+\])$')

def norm(s):
    return ' '.join(s.split())

def sections(path):
    out, cur, buf = {}, None, []
    for line in open(path, encoding='utf-8').read().replace('\f', '\n').split('\n'):
        if PAGE.match(line):
            continue
        m = HEAD.match(line)
        if m:
            if cur:
                out[cur] = norm(' '.join(buf))
            kind = 'section' if m.group(1).isdigit() else 'appendix'
            cur, buf = f'{kind}-{m.group(1)}{m.group(2)}', [line]
        elif cur:
            buf.append(line)
    if cur:
        out[cur] = norm(' '.join(buf))
    return out

def main(argv):
    spec_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '.duvet', 'specifications')
    if argv[:1] == ['--spec-dir']:
        spec_dir, argv = argv[1], argv[2:]
    if not argv:
        print('check_quotes: no input files', file=sys.stderr)
        return 1
    if not os.path.isdir(spec_dir):
        print(f'check_quotes: no spec dir {spec_dir}', file=sys.stderr)
        return 1
    cache, n, bad = {}, 0, 0
    for f in argv:
        lines = open(f, encoding='utf-8').read().split('\n')
        i = 0
        while i < len(lines):
            m = re.match(r'^\s*//= (https?://([^#\s]+))#(\S+)\s*$', lines[i])
            if not m:
                if re.match(r'^\s*//#', lines[i]):
                    n += 1
                    bad += 1
                    print(f'{f}:{i + 1}: //# line not preceded by a recognised //= <url>#<section> citation: {lines[i].strip()[:100]}')
                i += 1
                continue
            start, host_path, sec = i + 1, m.group(2), m.group(3)
            i += 1
            while i < len(lines) and re.match(r'^\s*//= \w+=', lines[i]):
                i += 1
            quote = []
            while i < len(lines) and re.match(r'^\s*//#', lines[i]):
                quote.append(re.sub(r'^\s*//# ?', '', lines[i]))
                i += 1
            n += 1
            txt = os.path.join(spec_dir, host_path + '.txt')
            if txt not in cache:
                cache[txt] = sections(txt) if os.path.exists(txt) else None
            secs, q = cache[txt], norm(' '.join(quote))
            why = None
            if secs is None:
                why = f'no spec file {txt}'
            elif sec not in secs:
                why = f'no {sec} in {host_path}'
            elif not q:
                why = 'empty quote'
            elif q not in secs[sec]:
                why = 'quote not in section'
            if why:
                bad += 1
                print(f'{f}:{start}: {host_path}#{sec}: {why}: {q[:100]}')
    print(f'{n} citations, {bad} bad')
    return 1 if bad or n == 0 else 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
