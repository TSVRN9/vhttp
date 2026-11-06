# mut.py FILE OLD NEW: replace the single occurrence of OLD with NEW in FILE (mutant maker; asserts exactly one match; \n etc. are unescaped).
# Run as: python3 -I tools/mut.py FILE OLD NEW
import sys
p,a,b=sys.argv[1],sys.argv[2].encode().decode('unicode_escape'),sys.argv[3].encode().decode('unicode_escape')
s=open(p).read()
assert s.count(a)==1,(p,a,s.count(a))
open(p,'w').write(s.replace(a,b))
