"""Extract the MSO (+ `now`) of every example in longfellow-zk's mdoc_examples.h.
usage: python extract_mdoc_examples.py mdoc_examples.h > validuntil_mdoc_data.txt
Output line: <idx> <now ISO> <validUntil ISO> <mso hex>"""
import re, sys
txt = open(sys.argv[1], encoding="utf-8").read()
txt = re.sub(r"//[^\n]*", "", txt)
body = txt[txt.index("mdoc_tests[] = {") + len("mdoc_tests[] = {"):]
# split top-level entries by brace depth
entries, depth, start = [], 0, None
for i, ch in enumerate(body):
    if ch == "{":
        if depth == 0: start = i
        depth += 1
    elif ch == "}":
        depth -= 1
        if depth == 0: entries.append(body[start:i + 1])
        if depth < 0: break
for idx, e in enumerate(entries):
    now = re.search(r'\(uint8_t\*\)"([^"]+)"', e).group(1)
    arrays = re.findall(r"\{((?:\s*0x[0-9a-fA-F]{2},?\s*)+)\}", e)
    mdoc = bytes(int(x, 16) for x in re.findall(r"0x([0-9a-fA-F]{2})", arrays[-1]))
    pat = b"\x6avalidUntil\xc0\x74"
    p = mdoc.find(pat)
    if p < 0:
        print(f"# {idx}: no validUntil", file=sys.stderr); continue
    until = mdoc[p + len(pat): p + len(pat) + 20].decode()
    # enclosing MSO: nearest preceding tag24 bstr (d8 18 58/59) that covers p
    mso = None
    for q in range(p, 0, -1):
        if mdoc[q] == 0xd8 and mdoc[q + 1] == 0x18 and mdoc[q + 2] in (0x58, 0x59):
            if mdoc[q + 2] == 0x58: hl, ln = 3, mdoc[q + 3]; hl = 4
            else: ln = int.from_bytes(mdoc[q + 3:q + 5], "big"); hl = 5
            if q + hl <= p < q + hl + ln:
                mso = mdoc[q + hl: q + hl + ln]; break
    if mso is None:
        print(f"# {idx}: MSO not found", file=sys.stderr); continue
    print(idx, now, until, mso.hex())
