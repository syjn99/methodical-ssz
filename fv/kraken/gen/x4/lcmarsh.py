"""ListC marshal (X4): the hand proof text of Fk/LcMarshal.lean as an anchored template (lcm_tpl.py).

Weaker than lcacc.py: there is no per-directive walker here. What the code decides: the position of every
label of MarshalSSZTo.S, and from it every directive number in the text (anchor @A<j>+<o>@ = label j plus
o). Every anchored directive must have the instruction text that it had in the hand case (CHECK), and
the function must have the same number of labels; otherwise the template is refused. Statements,
loop lemmas (lcm1..4), definitions and all tactic text are hand text.
"""
import re

import lcm_tpl as T


def resolve(D, code):
    labs = [i for i, (_, k, _) in enumerate(D) if k == "label"]
    want = 1 + max(int(m[1]) for m in re.finditer(r"@A(\d+)\+\d+@", T.PRE + T.STMT + T.PROOF))
    if len(labs) < want:
        raise ValueError(f"{len(labs)} labels, the template anchors {want}")
    txt = [t for _, _, t in D]
    pos = {}
    for tok, ins in T.CHECK.items():
        j, o = map(int, re.fullmatch(r"@A(\d+)\+(\d+)@", tok).groups())
        n = labs[j] + o
        if n >= len(txt) or txt[n] != ins:
            raise ValueError(f"anchor {tok} = directive {n} is `{txt[n] if n < len(txt) else None}`, the template needs `{ins}`")
        pos[tok] = n

    def sub(s):
        s = s.replace("@CODE@", code)
        return re.sub(r"@A\d+\+\d+@", lambda m: str(pos[m[0]]), s)
    return sub


def block(D, code, intro_line):
    sub = resolve(D, code)
    pre = sub(T.PRE).rstrip().split("\n")
    while pre and pre[-1].startswith("set_option "):
        pre.pop()
    stmt = sub(T.STMT)
    proof = [x[2:] if x.startswith("  ") else x for x in sub(T.PROOF).split("\n")]
    return (["-- marshal: hand text of Fk/LcMarshal.lean with directive numbers from the label positions (lcmarsh.py)"]
            + pre + ["", stmt, "set_option maxHeartbeats 16000000 in", "set_option maxRecDepth 200000 in",
                     "theorem marshal [Host] : marshal_stmt := by", *["  " + x for x in [intro_line(stmt)] + proof], ""])
