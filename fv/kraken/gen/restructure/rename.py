#!/usr/bin/env python3
"""Apply a restructuring map to the fv/ tree, or undo it.

Usage (from any cwd; Python 3 standard library only):

    python3 -I -B fv/kraken/gen/restructure/rename.py forward MAPS [--root REPO]
    python3 -I -B fv/kraken/gen/restructure/rename.py inverse MAPS [--root REPO]

MAPS is a directory with these files (see README.md in this directory):

* files.tsv      old path, new path, meaning (repository-relative). The tool moves each file.
                 A `.lean` file under fv/kraken/lean/ gives a module rename (path -> module name).
* names.tsv      kind, old name, new name, library, fifth column. A `namespace` row applies in the modules of its
                 library (longest old prefix wins); its fifth column is `whole` when the namespace moves as a whole
                 (then the row is also a prefix rule for qualified names in any text) or `part`. A `declaration` row
                 names one declaration; its fifth column is the new module of the declaration.
* manual-edits.tsv (optional)  new path, line, text after the automatic rewrite, final text.
* protect.txt    (optional) glob patterns of repository-relative paths whose text the tool does not change.

The forward mode:
1. checks that no new name or path of the maps already occurs in the old text (else the inverse is not exact);
2. moves the files of files.tsv;
3. rewrites every text file under fv/ (except protected files and this directory):
   `import` lines (module map), qualified identifiers and module names (longest prefix), renamed short names,
   paths of moved files under fv/kraken/lean/; in Lean files also `namespace` / `end` / `open` lines;
4. expands an `open` of a split namespace to the new namespaces that the imports of the file declare,
   and inserts an `open` line before the first `namespace` line of a file whose old namespace was split;
5. applies manual-edits.tsv;
   (an `open` of a merged namespace gets a `hiding` clause for the names that the old `open` did not show and that
   the file uses);
6. writes MAPS/applied-lines.tsv: every namespace / end / open line that it changed, inserted or deleted.
The inverse mode reads applied-lines.tsv and manual-edits.tsv and undoes the steps in the reverse order.
Exit 0 on success, 1 on a check failure, 2 on a usage error.
"""
import fnmatch
import json
import os
import re
import sys

LEAN_REL = "fv/kraken/lean/"
SKIP_DIRS = {".lake", ".git", "__pycache__"}
# A Lean identifier component: letters and digits (Unicode \w: Latin, Greek, ...), `_`, `'`, `!`, `?`, subscripts,
# or a «quoted» component. Symbols such as ⟨ ⋆ ∀ → are not identifier characters.
IDC = r"[\w'!?\u2080-\u209c\u1d62-\u1d6a\u2c7c]"
COMP = r"(?:«[^»\n]*»|[^\W\d]" + IDC + r"*)"
TOKEN = re.compile(r"(?<![\w.])" + COMP + r"(?:\." + COMP + r")*")
IMPORT = re.compile(r"^(\s*(?:public\s+)?(?:meta\s+)?import\s+)(\S+)(\s*)$")
OPEN = re.compile(r"^(\s*)open((?:\s+[A-Za-z_][A-Za-z0-9_.']*)+?)(\s+in)?(\s*)$")
NAMESPACE = re.compile(r"^(\s*)namespace\s+(\S+)(\s*)$")
END = re.compile(r"^(\s*)end(?:\s+(\S+))?(\s*)$")
SECTION = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section\b")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public|partial|unsafe)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([A-Za-z_][\w'.!?]*)")


def die(msg, code=1):
    print("rename.py: " + msg, file=sys.stderr)
    sys.exit(code)


def read_tsv(path, ncols, optional=False):
    if not os.path.exists(path):
        if optional:
            return []
        die(f"missing {path}", 2)
    rows = []
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            cols = line.split("\t")
            if len(cols) < ncols:
                die(f"{path}:{n}: expected {ncols} columns", 2)
            rows.append(cols)
    return rows


def read_lines(path):
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8") as f:
        return [x.strip() for x in f if x.strip() and not x.startswith("#")]


def module_of(path):
    if path.startswith(LEAN_REL) and path.endswith(".lean"):
        return path[len(LEAN_REL):-5].replace("/", ".")
    return None


class Maps:
    def __init__(self, d):
        self.dir = d
        self.files = [(r[0], r[1]) for r in read_tsv(os.path.join(d, "files.tsv"), 2)]
        names = read_tsv(os.path.join(d, "names.tsv"), 5)
        self.manual = [(r[0], int(r[1]), r[2], r[3]) for r in read_tsv(os.path.join(d, "manual-edits.tsv"), 4, True)]
        self.protect = []
        p = os.path.join(d, "protect.txt")
        if os.path.exists(p):
            with open(p, encoding="utf-8") as f:
                self.protect = [x.strip() for x in f if x.strip() and not x.startswith("#")]
        self.ns_rows = [(r[1], r[2], r[3]) for r in names if r[0] == "namespace"]
        whole = {r[1]: r[2] for r in names if r[0] == "namespace" and r[4] == "whole"}
        self.decl_rows = [(r[1], r[2], r[3], r[4]) for r in names if r[0] == "declaration"]
        # reference mode (a map with `type` rows, see README.md section 2): renames keyed on the full old name and
        # the declaring module, short references resolved by the scope of each Lean line
        self.types = sorted((r[1] for r in names if r[0] == "type"), key=len, reverse=True)
        self.ref = bool(self.types)
        self.ns_rows4 = [(r[1], r[2], r[3], r[4]) for r in names if r[0] == "namespace"]
        self.open_rows = [(r[1], r[2], r[3]) for r in names if r[0] == "open"]
        self.declared = set(read_lines(os.path.join(d, "declared.txt")))
        if self.ref:
            # an old name that two modules declare (different libraries) is not a text prefix rule
            cnt = {}
            for o, _, _, _ in self.decl_rows:
                cnt[o] = cnt.get(o, 0) + 1
            self.dup_old = {o for o, c in cnt.items() if c > 1}
            self.decl_rows_all = self.decl_rows
            self.decl_rows = [r for r in self.decl_rows if r[0] not in self.dup_old]
        # module map and path map (paths relative to fv/kraken/lean/)
        self.modules, self.paths = {}, {}
        for o, n in self.files:
            mo, mn = module_of(o), module_of(n)
            if mo and mn:
                self.modules[mo] = mn
            if o.startswith(LEAN_REL) and n.startswith(LEAN_REL):
                self.paths[o[len(LEAN_REL):]] = n[len(LEAN_REL):]
        # namespace rows: old -> list of (library, new); a 1:1 row has one target
        self.ns_targets = {}
        for o, n, lib in self.ns_rows:
            self.ns_targets.setdefault(o, []).append((lib, n))
        # token table: modules first (they win over a declaration of the same old name), then declarations,
        # then the namespaces that move as a whole, as prefixes
        self.tok = {}
        self.conflicts = []
        for o, n in self.modules.items():
            self.tok[o] = n
        for o, n, _, _ in self.decl_rows:
            if o in self.tok and self.tok[o] != n:
                self.conflicts.append((o, self.tok[o], n))
                continue
            self.tok[o] = n
        for o, n in whole.items():
            self.tok.setdefault(o, n)
        self.short = {}
        for o, n, _, _ in self.decl_rows:
            so, sn = o.split(".")[-1], n.split(".")[-1]
            if so != sn:
                self.short[so] = sn
        if self.ref:
            self.short = {}     # reference mode: no rule on the last name component alone
            # the new names of the namespace rows that the declarations do not show (empty namespaces, blocks)
            for o, n, _, _ in self.ns_rows4:
                self.inv_tok_extra = getattr(self, "inv_tok_extra", {})
                self.inv_tok_extra.setdefault(n, o)
            for o, n, _ in self.open_rows:
                self.inv_tok_extra.setdefault(n, o)
        self.inv_tok = {}
        for o, n in self.tok.items():
            if n in self.inv_tok and self.inv_tok[n] != o and "." in n:
                die(f"two old names {self.inv_tok[n]} and {o} have the same new name {n}: the inverse is not unique")
            self.inv_tok.setdefault(n, o)
        for o, n in self.modules.items():
            self.inv_tok[n] = o
        self.inv_short = {n: o for o, n in self.short.items()}
        self.inv_paths = {n: o for o, n in self.paths.items()}
        if len(self.inv_short) != len(self.short) or len(self.inv_paths) != len(self.paths):
            die("short-name or path map is not one-to-one")
        self.path_re = self._path_re(self.paths)
        self.inv_path_re = self._path_re(self.inv_paths)

    @staticmethod
    def _path_re(m):
        if not m:
            return None
        keys = sorted(m, key=len, reverse=True)
        return re.compile(r"(?<![A-Za-z0-9_.\-])(" + "|".join(re.escape(k) for k in keys) + r")(?![A-Za-z0-9_])")

    def protected(self, rel):
        return any(fnmatch.fnmatch(rel, g) for g in self.protect)


def sub_tokens(text, tok, short, lean=True):
    """Rewrite qualified names (longest prefix in `tok`) and short names (`short`). Outside Lean, a trailing
    quote, `!` or `?` ends a name (Python and shell strings)."""
    def rep(m):
        t = m.group(0)
        if not lean:
            u = t.rstrip("'!?")
            return rep1(u) + t[len(u):]
        return rep1(t)

    def rep1(t):
        parts = t.split(".")
        for i in range(len(parts), 1, -1):
            k = ".".join(parts[:i])
            if k in tok:
                return tok[k] + t[len(k):]
        if parts[0] in short:
            return short[parts[0]] + t[len(parts[0]):]
        return t
    return TOKEN.sub(rep, text)


def sub_paths(text, rx, m):
    if rx is None:
        return text
    return rx.sub(lambda x: m[x.group(1)], text)


def list_files(root, tooldir):
    out = []
    base = os.path.join(root, "fv")
    for dp, dns, fns in os.walk(base):
        dns[:] = sorted(d for d in dns if d not in SKIP_DIRS and os.path.join(dp, d) != tooldir)
        for fn in sorted(fns):
            p = os.path.join(dp, fn)
            if os.path.islink(p):
                continue
            out.append(os.path.relpath(p, root).replace(os.sep, "/"))
    return out


def read_text(path):
    with open(path, "rb") as f:
        data = f.read()
    if b"\0" in data:
        return None
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        return None


def write_text(path, text):
    with open(path, "wb") as f:
        f.write(text.encode("utf-8"))


def top_namespaces(lines):
    """(index, name) of the namespace lines at the top level (no enclosing namespace or section)."""
    depth, out = [], []
    for i, ln in enumerate(lines):
        s = ln.rstrip("\n")
        m = NAMESPACE.match(s)
        if m:
            if not any(k == "ns" for k, _ in depth):
                out.append((i, m.group(2)))
            depth.append(("ns", m.group(2)))
            continue
        if SECTION.match(s):
            depth.append(("sec", None))
            continue
        m = END.match(s)
        if m and depth:
            depth.pop()
    return out


def registered(lines):
    """Namespaces (with prefixes) that a Lean file declares by its namespace lines and qualified top-level names."""
    stack, regs = [], set()

    def add(full):
        parts = full.split(".")
        for i in range(1, len(parts) + 1):
            regs.add(".".join(parts[:i]))
    for ln in lines:
        s = ln.rstrip("\n")
        m = NAMESPACE.match(s)
        if m:
            cur = ".".join(x for k, x in stack if k == "ns")
            full = (cur + "." if cur else "") + m.group(2)
            add(full)
            stack.append(("ns", m.group(2)))
            continue
        if SECTION.match(s):
            stack.append(("sec", ""))
            continue
        m = END.match(s)
        if m and stack:
            stack.pop()
            continue
        m = DECL.match(s)
        if m and "." in m.group(1):
            cur = ".".join(x for k, x in stack if k == "ns")
            full = (cur + "." if cur else "") + m.group(1)
            add(full.rsplit(".", 1)[0])
    return regs


def imports_of(lines):
    out = []
    for ln in lines:
        m = IMPORT.match(ln.rstrip("\n"))
        if m:
            out.append(m.group(2))
    return out


def tool_dir(root):
    """This directory, located under `root` (the tool may run on a copy of the tree)."""
    here = os.path.dirname(os.path.abspath(__file__))
    repo = os.path.abspath(os.path.join(here, "..", "..", "..", ".."))
    return os.path.join(root, os.path.relpath(here, repo))


def forward(maps, root):
    tooldir = tool_dir(root)
    if maps.conflicts:
        for o, a, b in maps.conflicts:
            print(f"note: old name {o} is a module ({a}) and a declaration ({b}); the module rename is used in text")
    for o, n in maps.files:
        if not os.path.exists(os.path.join(root, o)):
            die(f"missing old file {o}")
        if os.path.exists(os.path.join(root, n)):
            die(f"new file exists already: {n}")
    files = list_files(root, tooldir)
    # 1. inverse safety: no new token, short name or path may occur in the old text
    bad = []
    for rel in files:
        if maps.protected(rel):
            continue
        text = read_text(os.path.join(root, rel))
        if text is None:
            continue
        for m in TOKEN.finditer(text):
            t = m.group(0) if rel.endswith(".lean") else m.group(0).rstrip("'!?")
            parts = t.split(".")
            hit = any(".".join(parts[:i]) in maps.inv_tok for i in range(len(parts), 1, -1)) or parts[0] in maps.inv_short
            if hit:
                bad.append(f"{rel}: {t}")
        if maps.inv_path_re is not None:
            for m in maps.inv_path_re.finditer(text):
                bad.append(f"{rel}: path {m.group(1)}")
    if bad:
        print("\n".join(bad[:50]), file=sys.stderr)
        die(f"{len(bad)} occurrences of new names in the old tree: the inverse would not be exact")
    # 2. moves
    for o, n in maps.files:
        os.makedirs(os.path.dirname(os.path.join(root, n)), exist_ok=True)
        os.rename(os.path.join(root, o), os.path.join(root, n))
    for o, _ in maps.files:
        d = os.path.dirname(os.path.join(root, o))
        while d.startswith(os.path.join(root, "fv")) and os.path.isdir(d) and not os.listdir(d):
            os.rmdir(d)
            d = os.path.dirname(d)
    files = list_files(root, tooldir)
    # 3. text pass
    texts, oldlines = {}, {}
    for rel in files:
        if maps.protected(rel):
            continue
        text = read_text(os.path.join(root, rel))
        if text is None:
            continue
        texts[rel] = text
    newlines = {}
    records = []
    lib_of_new = {}
    for o, n in maps.files:
        mn = module_of(n)
        if mn:
            lib_of_new[n] = mn.split(".")[0]
    for rel, text in texts.items():
        lines = text.splitlines(keepends=True)
        is_lean = rel.endswith(".lean")
        oldlines[rel] = list(lines)
        out = []
        for ln in lines:
            body, nl = (ln[:-1], "\n") if ln.endswith("\n") else (ln, "")
            if is_lean:
                m = IMPORT.match(body)
                if m:
                    mod = maps.modules.get(m.group(2), m.group(2))
                    out.append(m.group(1) + mod + m.group(3) + nl)
                    continue
                if OPEN.match(body) or NAMESPACE.match(body) or END.match(body):
                    out.append(ln)
                    continue
            nb = sub_tokens(body, maps.tok, maps.short, is_lean)
            nb = sub_paths(nb, maps.path_re, maps.paths)
            out.append(nb + nl)
        newlines[rel] = out
    # 4. namespace and end lines (top level only)
    for rel, lines in newlines.items():
        if not rel.endswith(".lean"):
            continue
        lib = lib_of_new.get(rel)

        if lib is None:
            continue    # a file that does not move keeps its namespace lines

        def map_ns(name):
            best = None
            for o, targets in maps.ns_targets.items():
                if name == o or name.startswith(o + "."):
                    t = [n for l, n in targets if l == lib]
                    if t and (best is None or len(o) > len(best[0])):
                        best = (o, t[0])
            if best is None:
                return name
            return best[1] + name[len(best[0]):]
        depth = []
        for i, ln in enumerate(lines):
            body, nl = (ln[:-1], "\n") if ln.endswith("\n") else (ln, "")
            m = NAMESPACE.match(body)
            if m:
                if not any(k == "ns" for k, _ in depth):
                    nn = map_ns(m.group(2))
                    if nn != m.group(2):
                        lines[i] = m.group(1) + "namespace " + nn + m.group(3) + nl
                depth.append(("ns", m.group(2)))
                continue
            if SECTION.match(body):
                depth.append(("sec", None))
                continue
            m = END.match(body)
            if m and depth:
                k, name = depth.pop()
                if k == "ns" and not any(x == "ns" for x, _ in depth) and m.group(2):
                    nn = map_ns(m.group(2))
                    if nn != m.group(2):
                        lines[i] = m.group(1) + "end " + nn + m.group(3) + nl
    # 5. registration and import closure in the new tree
    regs, imps = {}, {}
    for rel, lines in newlines.items():
        mod = module_of(rel)
        if mod:
            regs[mod] = registered(lines)
        imps[rel] = imports_of(lines)
    mod_imps = {module_of(r): v for r, v in imps.items() if module_of(r)}
    closure_cache = {}

    def closure(mod):
        if mod in closure_cache:
            return closure_cache[mod]
        closure_cache[mod] = set()
        acc = set()
        for i in mod_imps.get(mod, []):
            acc.add(i)
            acc |= closure(i)
        closure_cache[mod] = acc
        return acc
    all_regs = set()
    for v in regs.values():
        all_regs |= v
    by_ns = {}      # new namespace -> [(short name, old name, new module)]
    for o, n, _, mod in maps.decl_rows:
        ns, _, short = n.rpartition(".")
        by_ns.setdefault(ns, []).append((short, o, mod))
    for rel, lines in newlines.items():
        if not rel.endswith(".lean"):
            continue
        mods = set()
        for i in imps[rel]:
            mods |= {i} | closure(i)
        avail = set()
        for m2 in mods:
            avail |= regs.get(m2, set())
        old = oldlines[rel]
        lib = lib_of_new.get(rel)
        tokens = set(m.group(0).split(".")[0] for m in TOKEN.finditer("".join(lines)))
        tops = top_namespaces(old)
        first_ns = tops[0][0] if tops else None
        old_open = set(t for ln in old for m in [OPEN.match(ln.rstrip("\n"))] if m for t in m.group(2).split())
        old_open |= set(n for _, n in tops)

        def hide(target, src):
            """Names of `target` that the open of the old namespace `src` did not make visible and that the file uses."""
            out = []
            for short, o, mod in by_ns.get(target, []):
                ons = o.rpartition(".")[0]
                if ons == src or ons in old_open or mod not in mods or short not in tokens:
                    continue
                out.append(short)
            return sorted(set(out))

        def open_lines(indent, items, suffix, nl):
            """`items`: list of (namespace, old namespace or None). One line for the plain ones, one per hiding."""
            plain, extra = [], []
            for c, src in items:
                h = hide(c, src) if src is not None else []
                if h:
                    extra.append(indent + "open " + c + " hiding " + " ".join(h) + nl)
                elif c not in plain:
                    plain.append(c)
            if extra and suffix:
                die(f"{rel}: an `open ... in` line needs a hiding clause")
            head = [indent + "open " + " ".join(plain) + suffix + nl] if plain else []
            return head + extra
        slots = [[ln] for ln in lines]
        # 5a. open lines
        opened_before_ns = set()
        for i, ln in enumerate(lines):
            body, nl = (ln[:-1], "\n") if ln.endswith("\n") else (ln, "")
            m = OPEN.match(body)
            if not m:
                continue
            toks = m.group(2).split()
            items, seen = [], set()
            for t in toks:
                if t in maps.ns_targets:
                    cand = ([(t, None)] if t in all_regs else []) + [(n, t) for _, n in maps.ns_targets[t]]
                    cand = [(c, src) for c, src in cand if c in avail]
                else:
                    cand = [(t, None)]
                for c, src in cand:
                    if c not in seen:
                        seen.add(c)
                        items.append((c, src))
            if first_ns is None or i < first_ns:
                opened_before_ns |= seen
            if [c for c, _ in items] != toks or any(src is not None and hide(c, src) for c, src in items):
                slots[i] = open_lines(m.group(1), items, m.group(3) or "", m.group(4) + nl)
        # 5b. inserted open line for a split old namespace
        ins = []
        for _, name in tops:
            for o, targets in maps.ns_targets.items():
                if len(targets) < 2 and o not in all_regs:
                    continue
                if not (name == o or name.startswith(o + ".")):
                    continue
                own = None
                if lib is not None:
                    t = [n for l, n in targets if l == lib]
                    own = t[0] if t else None
                cand = ([o] if o in all_regs else []) + [n for _, n in targets]
                for c in cand:
                    if own is not None and (c == own or own.startswith(c + ".")):
                        continue
                    if own is None and (name == c or name.startswith(c + ".")):
                        continue
                    if c in avail and c not in opened_before_ns and c not in [x for x, _ in ins]:
                        ins.append((c, o if c != o else None))
        inserted = open_lines("", ins, "", "\n") if ins and first_ns is not None else []
        # records: open / namespace / end lines that changed, and inserted lines
        newl = []
        for i, slot in enumerate(slots):
            if i == first_ns:
                for ln in inserted:
                    records.append((rel, len(newl) + 1, "insert", ln.rstrip("\n"), ""))
                    newl.append(ln)
            o_ln = old[i]
            if not slot:
                records.append((rel, len(newl) + 1, "delete", "", o_ln.rstrip("\n")))
                continue
            ln = slot[0]
            b = ln.rstrip("\n")
            if ln != o_ln and (OPEN.match(b) or NAMESPACE.match(b) or END.match(b)):
                if ln.endswith("\n") != o_ln.endswith("\n"):
                    die(f"{rel}: line end changed")
                records.append((rel, len(newl) + 1, "replace", b, o_ln.rstrip("\n")))
            newl.append(ln)
            for ln2 in slot[1:]:
                records.append((rel, len(newl) + 1, "insert", ln2.rstrip("\n"), ""))
                newl.append(ln2)
        newlines[rel] = newl
    # 6. manual edits
    for path, line, before, after in maps.manual:
        if path not in newlines:
            die(f"manual edit: no text file {path}")
        ls = newlines[path]
        if line < 1 or line > len(ls) or ls[line - 1].rstrip("\n") != before:
            die(f"manual edit {path}:{line}: the line is not {before!r}")
        ls[line - 1] = after + ("\n" if ls[line - 1].endswith("\n") else "")
    changed = 0
    for rel, lines in newlines.items():
        new = "".join(lines)
        if new != texts[rel]:
            changed += 1
            write_text(os.path.join(root, rel), new)
    with open(os.path.join(maps.dir, "applied-lines.tsv"), "w", encoding="utf-8") as f:
        f.write("# written by rename.py forward; read by rename.py inverse. path\tline\taction\tnew text\told text\n")
        for r in records:
            f.write("\t".join(str(x) for x in r) + "\n")
    print(f"forward: {len(maps.files)} files moved, {changed} files rewritten, {len(records)} line records")
    return 0


def inverse(maps, root):
    tooldir = tool_dir(root)
    rec = read_tsv(os.path.join(maps.dir, "applied-lines.tsv"), 5)
    files = list_files(root, tooldir)
    texts = {}
    for rel in files:
        if maps.protected(rel):
            continue
        t = read_text(os.path.join(root, rel))
        if t is not None:
            texts[rel] = t
    lines = {rel: t.splitlines(keepends=True) for rel, t in texts.items()}
    for path, line, before, after in reversed(maps.manual):
        ls = lines.get(path)
        if ls is None or ls[line - 1].rstrip("\n") != after:
            die(f"manual edit {path}:{line}: the line is not {after!r}")
        ls[line - 1] = before + ("\n" if ls[line - 1].endswith("\n") else "")
    byfile = {}
    for path, line, action, new, old in ([r[0], int(r[1]), r[2], r[3], r[4]] for r in rec):
        byfile.setdefault(path, []).append((line, action, new, old))
    for path, rs in byfile.items():
        ls = lines.get(path)
        if ls is None:
            die(f"record: no text file {path}")
        # a replaced line and a deleted line can have the same number (the deleted line stood before it):
        # restore the replaced line first, then insert the deleted line before it
        for line, action, new, old in sorted(rs, key=lambda x: (-x[0], x[1] != "replace")):
            if action == "insert":
                if ls[line - 1].rstrip("\n") != new:
                    die(f"record {path}:{line}: inserted line is not {new!r}")
                del ls[line - 1]
            elif action == "replace":
                if ls[line - 1].rstrip("\n") != new:
                    die(f"record {path}:{line}: line is not {new!r}")
                ls[line - 1] = old + ("\n" if ls[line - 1].endswith("\n") else "")
            elif action == "delete":
                ls.insert(line - 1, old + "\n")
    inv_mod = {n: o for o, n in maps.modules.items()}
    changed = 0
    for rel, ls in lines.items():
        is_lean = rel.endswith(".lean")
        out = []
        for ln in ls:
            body, nl = (ln[:-1], "\n") if ln.endswith("\n") else (ln, "")
            if is_lean:
                m = IMPORT.match(body)
                if m:
                    out.append(m.group(1) + inv_mod.get(m.group(2), m.group(2)) + m.group(3) + nl)
                    continue
            nb = sub_tokens(body, maps.inv_tok, maps.inv_short, is_lean)
            nb = sub_paths(nb, maps.inv_path_re, maps.inv_paths)
            out.append(nb + nl)
        new = "".join(out)
        if new != texts[rel]:
            changed += 1
            write_text(os.path.join(root, rel), new)
    for o, n in reversed(maps.files):
        if not os.path.exists(os.path.join(root, n)):
            die(f"missing new file {n}")
        os.makedirs(os.path.dirname(os.path.join(root, o)), exist_ok=True)
        os.rename(os.path.join(root, n), os.path.join(root, o))
    for o, n in maps.files:
        d = os.path.dirname(os.path.join(root, n))
        while d.startswith(os.path.join(root, "fv")) and os.path.isdir(d) and not os.listdir(d):
            os.rmdir(d)
            d = os.path.dirname(d)
    print(f"inverse: {changed} files rewritten, {len(maps.files)} files moved back")
    return 0


# ---------------------------------------------------------------------------------------------------------------
# Reference mode: a map with `type` rows (one step of the move to one directory per Prysm type).
#
# Every rename is keyed on the full old name and its declaring module. In a Lean file the tool tracks the scope of
# each line (namespace blocks, `open` lines, `open ... in`, the namespace that a dotted declaration name opens) and
# resolves each identifier as Lean does. A reference to a moved declaration is then written:
# * with the full new name when the old text had the full old name, or when the line is outside the namespace of
#   the declaring type (a `type` row);
# * else in the shortest form that resolves to exactly that declaration in the new scope.
# An `open` of an old namespace becomes the `open` rows of the file's type; the tool never opens the namespace of
# another type. A line whose text the rule-based inverse (full names, modules, paths) does not restore is recorded in
# applied-lines.tsv; the forward mode checks the inverse in memory before it writes anything.
# ---------------------------------------------------------------------------------------------------------------
REF_CMD_DECL = re.compile(
    r"^((?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|partial|unsafe|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+)([A-Za-z_«][\w'.!?«»]*)")
REF_OPEN = re.compile(r"^(\s*)open\s+(.*?)(\s+in)?(\s*)$")
JSON_KV = re.compile(r'^(\s*)"([A-Za-z_]+)": (".*")(,?)\s*$')
CASE_KEYS_CODE = ("old", "new", "diff")


def lean_segments(line, depth):
    """Split one line into (kind, text) segments: 'code', 'comment', 'string'. `depth` is the block comment depth
    at the line start. Returns (segments, depth at the line end)."""
    segs, i, n, cur, kind = [], 0, len(line), [], "comment" if depth else "code"

    def flush(k):
        if cur:
            segs.append((k, "".join(cur)))
            cur.clear()
    while i < n:
        c = line[i]
        if depth:
            if line.startswith("/-", i):
                depth += 1
                cur.append("/-")
                i += 2
                continue
            if line.startswith("-/", i):
                depth -= 1
                cur.append("-/")
                i += 2
                if not depth:
                    flush("comment")
                continue
            cur.append(c)
            i += 1
            continue
        if line.startswith("/-", i):
            flush("code")
            depth = 1
            cur.append("/-")
            i += 2
            continue
        if line.startswith("--", i):
            flush("code")
            segs.append(("comment", line[i:]))
            return segs, depth
        if c == '"':
            flush("code")
            j = i + 1
            while j < n and line[j] != '"':
                j += 2 if line[j] == "\\" else 1
            segs.append(("string", line[i:j + 1]))
            i = j + 1
            continue
        cur.append(c)
        i += 1
    flush("comment" if depth else "code")
    return segs, depth


class RefScope:
    """The scope of one line: namespace blocks, opens (per block), `open ... in`, the dotted declaration namespace."""

    def __init__(self):
        self.stack = []          # [kind, name, opens]; kind 'ns' or 'sec'
        self.top_opens = []      # opens before any block
        self.pending = []        # `open ... in` items waiting for their command
        self.active_in = []      # `open ... in` items of the current command
        self.state = "none"      # none | waiting | active
        self.declns = ""

    def ns(self):
        return ".".join(x[1] for x in self.stack if x[0] == "ns")

    def prefixes(self):
        full = self.ns()
        if self.declns:
            full = (full + "." if full else "") + self.declns
        p = full.split(".") if full else []
        return [".".join(p[:i]) for i in range(len(p), 0, -1)]

    def opens(self):
        out = list(self.top_opens)
        for x in self.stack:
            out += x[2]
        return out + self.active_in

    def add_open(self, items):
        (self.stack[-1][2] if self.stack else self.top_opens).extend(items)


class RefRename:
    def __init__(self, maps, root):
        self.m, self.root = maps, root
        self.tooldir = tool_dir(root)
        self.warn = []
        self.file_scope = None
        # declarations: old full name -> [(new full name, new module)]
        self.old_rows = {}
        for o, n, _, mod in maps.decl_rows_all:
            self.old_rows.setdefault(o, []).append((n, mod))
        self.new_rows = {n: o for o, n, _, _ in maps.decl_rows_all}
        self.mod_map = dict(maps.modules)
        self.inv_mod = {n: o for o, n in self.mod_map.items()}
        self.old_ns_mine = set()
        for o in self.old_rows:
            p = o.split(".")
            for i in range(1, len(p)):
                self.old_ns_mine.add(".".join(p[:i]))
        self.new_ns_mine = set()
        for n in self.new_rows:
            p = n.split(".")
            for i in range(1, len(p)):
                self.new_ns_mine.add(".".join(p[:i]))
        for o, n, _, _ in maps.ns_rows4:
            self.old_ns_mine.add(o)
            self.new_ns_mine.add(n)
        self.declared = maps.declared
        self.free_opens = {n for _, n, sc in maps.open_rows if sc in ("-", "*")}
        # non-Lean text: the last name component of a moved declaration whose relative name changes, if it is unique
        cnt = {}
        for o, n, _, _ in maps.decl_rows_all:
            cnt.setdefault(o.split(".")[-1], set()).add(n)
        other_last = {x.split(".")[-1] for x in self.declared}
        self.text_short = {}
        for o, n, _, _ in maps.decl_rows_all:
            so = o.split(".")[-1]
            if len(cnt[so]) == 1 and so not in other_last and not n.endswith("." + so):
                self.text_short[so] = n

    # -- name universe ------------------------------------------------------------------------------------------
    def mine_old(self, name):
        """(row target list, "") when `name` is a moved declaration (names.tsv lists every declaration of the moved
        modules, the generated ones included, so that a name under a moved structure does not count as declared)."""
        if name in self.old_rows:
            return self.old_rows[name], ""
        return None

    def mine_new(self, name):
        return name if name in self.new_rows else None

    def exists_old(self, name):
        if self.mine_old(name):
            return "mine"
        if name in self.declared:
            return "other"
        return None

    def exists_new(self, name):
        k = self.mine_new(name)
        if k:
            return "mine"
        if name in self.declared and not self.mine_old(name):
            return "other"
        return None

    def resolve(self, tok, sc, exists):
        """Lean name resolution of `tok` in scope `sc`: list of (full name), or [] (unknown or local)."""
        if tok.startswith("_root_."):
            t = tok[7:]
            return [t] if exists(t) else []
        parts = tok.split(".")
        hid = {}
        for o in sc.opens():
            hid[o[0]] = o[1]
        for i in range(len(parts), 0, -1):
            ident = ".".join(parts[:i])
            # the innermost namespace that has the name wins (a nested namespace shadows its parent)
            found = next(([p + "." + ident] for p in sc.prefixes() if exists(p + "." + ident)), [])
            if found:
                return [(f, tok[len(ident):]) for f in found]
            res = [ident] if exists(ident) else []
            for o, h in sc.opens():
                if parts[0] in h:
                    continue
                if exists(o + "." + ident):
                    res.append(o + "." + ident)
            if res:
                return [(f, tok[len(ident):]) for f in dict.fromkeys(res)]
        return []

    def resolve_ns(self, tok, sc, isns):
        cands = [p + "." + tok for p in sc.prefixes()] + [tok]
        return [c for c in cands if isns(c)]

    def type_of(self, name):
        for t in self.m.types:
            if name == t or name.startswith(t + "."):
                return t
        return None

    def target(self, old, mod_new):
        """The new name of the moved declaration `old` seen from module `mod_new` (the row of the declaring module in
        its import closure when two modules declare the same old name)."""
        rows = self.old_rows[old]
        if len(rows) == 1:
            return rows[0][0]
        clo = self.closure_new(mod_new) | {mod_new}
        hit = [n for n, m in rows if m in clo]
        if len(hit) != 1:
            self.fail(f"{mod_new}: old name {old} is declared by several modules {[m for _, m in rows]}")
            return rows[0][0]
        return hit[0]

    def emit(self, full, sc_new, written_full, ctx):
        """Text of a reference to the new name `full` in the new scope."""
        if written_full:
            return full
        t = self.type_of(full)
        cur = sc_new.ns()
        drops = []
        home = t if t else full.rsplit(".", 1)[0]
        if cur == home or cur.startswith(home + "."):
            p = cur.split(".")
            drops += [".".join(p[:i]) for i in range(len(p), 0, -1) if ".".join(p[:i]) == home
                      or ".".join(p[:i]).startswith(home + ".")]
            drops += [o for o, _ in sc_new.opens()]
        elif t is None:
            drops += [o for o, _ in sc_new.opens()]
        else:
            # outside the type: only an `open` that a row grants to files outside every type (`-`) or to every
            # file (`*`) may shorten (a generator that writes bare constant names under such an open)
            drops += [o for o, _ in sc_new.opens() if o in self.free_opens]
        cands = []
        for d in drops:
            if full.startswith(d + "."):
                cands.append(full[len(d) + 1:])
        cands.sort(key=lambda s: (s.count("."), len(s)))
        for c in cands:
            r = self.resolve(c, sc_new, self.exists_new)
            if len(r) == 1 and r[0][0] == full and r[0][1] == "":
                return c
        r = self.resolve(full, sc_new, self.exists_new)
        if len(r) == 1 and r[0][0] == full:
            return full
        self.warn.append(f"{ctx}: {full} needs _root_")
        return "_root_." + full

    def fail(self, msg):
        self.errors.append(msg)

    # -- module graph of the new tree -----------------------------------------------------------------------------
    def closure_new(self, mod):
        if mod in self.clo_cache:
            return self.clo_cache[mod]
        self.clo_cache[mod] = set()
        acc = set()
        for i in self.imports_new.get(mod, []):
            acc.add(i)
            acc |= self.closure_new(i)
        self.clo_cache[mod] = acc
        return acc

    def ns_row(self, old_ns, mod_new, block):
        """New namespace of the old namespace `old_ns` in a block of module `mod_new` (block: ordinal of the top-level
        namespace block). A scope `MODULE#N` names one block; else the longest module prefix wins."""
        best = None
        for o, n, scope, _ in self.m.ns_rows4:
            if not (old_ns == o or old_ns.startswith(o + ".")):
                continue
            if "#" in scope:
                sm, sb = scope.split("#")
                if sm != mod_new or int(sb) != block:
                    continue
                rank = (2, len(o))
            elif mod_new == scope or mod_new.startswith(scope + "."):
                rank = (1, len(scope), len(o))
            else:
                continue
            if best is None or rank > best[0]:
                best = (rank, o, n)
        if best is None:
            return None
        return best[2] + old_ns[len(best[1]):]

    # -- one Lean file ----------------------------------------------------------------------------------------------
    def lean_file(self, rel_old, rel_new, lines):
        self.file_scope = None
        self.snap = None
        self.lean_file1(rel_old, rel_new, lines)
        self.file_scope = self.snap
        save, self.warn = self.warn, []
        out = self.lean_file1(rel_old, rel_new, lines)
        self.warn = save + self.warn
        return out

    def lean_file1(self, rel_old, rel_new, lines):
        mod_old, mod_new = module_of(rel_old), module_of(rel_new)
        moved = mod_old in self.mod_map
        self.file_type = self.type_of(mod_new) if mod_new else None
        so, sn = RefScope(), RefScope()
        depth = 0
        out = []
        block = 0
        here = mod_new or rel_new
        for idx, ln in enumerate(lines):
            body, nl = (ln[:-1], "\n") if ln.endswith("\n") else (ln, "")
            ctx = f"{rel_new}:{idx + 1}"
            start_depth = depth
            segs, depth = lean_segments(body, depth)
            stripped = body.strip()
            col0 = bool(body) and not body[0].isspace() and not start_depth
            is_cmd = col0 and not body.startswith("--") and not body.startswith("/-") and not body.startswith("|")
            m_imp = IMPORT.match(body)
            if m_imp:
                out.append(m_imp.group(1) + self.mod_map.get(m_imp.group(2), m_imp.group(2)) + m_imp.group(3) + nl)
                continue
            if is_cmd:
                for s in (so, sn):
                    if s.state == "active":
                        s.active_in, s.state = [], "none"
                    s.declns = ""
                if so.state == "waiting" and not body.startswith("open ") and not body.startswith("set_option ") \
                        and not body.startswith("@["):
                    for s in (so, sn):
                        s.active_in, s.pending, s.state = s.pending, [], "active"
            m_ns = NAMESPACE.match(body) if not start_depth else None
            m_end = END.match(body) if not start_depth else None
            m_sec = SECTION.match(body) if not start_depth else None
            if m_ns:
                oldfull = (so.ns() + "." if so.ns() else "") + m_ns.group(2)
                if not so.stack:
                    block += 1
                so.stack.append(["ns", m_ns.group(2), []])
                newname = m_ns.group(2)
                if moved:
                    nf = self.ns_row(oldfull, mod_new, block)
                    if nf is not None and nf != oldfull:
                        par = sn.ns()
                        if par and not nf.startswith(par + "."):
                            self.fail(f"{ctx}: new namespace {nf} is not inside {par}")
                        newname = nf[len(par) + 1:] if par else nf
                sn.stack.append(["ns", newname, []])
                if self.snap is None and len(so.stack) == 1:
                    self.snap = (copy_scope(so), copy_scope(sn))
                out.append(m_ns.group(1) + "namespace " + newname + m_ns.group(3) + nl
                           if newname != m_ns.group(2) else ln)
                continue
            if m_sec:
                so.stack.append(["sec", "", []])
                sn.stack.append(["sec", "", []])
                out.append(self.text_line(body, segs, so, sn, ctx, here) + nl)
                continue
            if m_end and so.stack:
                ko = so.stack.pop()
                kn = sn.stack.pop()
                if ko[0] == "ns" and m_end.group(2):
                    parts = m_end.group(2)
                    newname = kn[1] if parts == ko[1] else parts
                    out.append(m_end.group(1) + "end " + newname + m_end.group(3) + nl if newname != parts else ln)
                else:
                    out.append(ln)
                continue
            m_op = REF_OPEN.match(body) if not start_depth else None
            if m_op and not m_op.group(2).startswith("--"):
                new = self.open_line(m_op, so, sn, ctx, mod_new)
                out.append(None if new is None else new + nl)
                continue
            if is_cmd:
                md = REF_CMD_DECL.match(body)
                if md:
                    nm = md.group(2)
                    if nm.startswith("_root_."):
                        oldfull = nm[7:]
                    else:
                        oldfull = (so.ns() + "." if so.ns() else "") + nm
                    if "." in nm and not nm.startswith("_root_."):
                        so.declns = nm.rsplit(".", 1)[0]
                    newtxt = nm
                    if oldfull in self.old_rows and moved:
                        nf = self.target(oldfull, mod_new)
                        cur = sn.ns()
                        if cur and nf.startswith(cur + "."):
                            newtxt = nf[len(cur) + 1:]
                        elif not cur:
                            newtxt = nf
                        else:
                            newtxt = "_root_." + nf
                    if "." in newtxt and not newtxt.startswith("_root_."):
                        sn.declns = newtxt.rsplit(".", 1)[0]
                    rest = body[md.end(2):]
                    segs2, _ = lean_segments(rest, 0)
                    out.append(md.group(1) + newtxt + self.text_line(rest, segs2, so, sn, ctx, here) + nl)
                    continue
            out.append(self.text_line(body, segs, so, sn, ctx, here) + nl)
        return out

    def open_line(self, m, so, sn, ctx, mod_new):
        """New text of an `open` line (None: the line is deleted). Also updates both scopes."""
        items_txt = m.group(2)
        is_in = bool(m.group(3))
        words = items_txt.split()
        if "hiding" in words or "renaming" in words or "(" in items_txt or "--" in items_txt:
            if "hiding" in words:
                i = words.index("hiding")
                o = self.resolve_ns(words[0], so, self.isns_old)
                o2 = o[0] if o else words[0]
                hid = set(words[i + 1:])
                nsn = self.resolve_ns(words[0], sn, self.isns_new)
                item_o, item_n = [(o2, hid)], [(nsn[0] if nsn else words[0], hid)]
            else:
                item_o = item_n = []
            for s, it in ((so, item_o), (sn, item_n)):
                if is_in:
                    s.pending, s.state = it, "waiting"
                else:
                    s.add_open(it)
            return m.group(0)
        ftype = self.type_of(sn.ns()) or self.file_type or "-"
        new_items, o_items, n_items = [], [], []
        for w in words:
            old = self.resolve_ns(w, so, self.isns_old)
            o_items += [(x, set()) for x in old] or [(w, set())]
            if not old or not any(x in self.old_ns_mine for x in old):
                new_items.append(w)
                n_items += [(x, set()) for x in self.resolve_ns(w, sn, self.isns_new)] or [(w, set())]
                continue
            written_full = w in old
            for x in old:
                tg = [n for o, n, s in self.m.open_rows if o == x and (s == ftype or s == "*")]
                if x in self.avail and x not in tg:
                    tg = [x] + tg
                for t in tg:
                    if t not in self.avail:
                        continue
                    txt = t
                    if not written_full:
                        cur = sn.ns().split(".") if sn.ns() else []
                        for i in range(len(cur), 0, -1):
                            p = ".".join(cur[:i])
                            if t.startswith(p + ".") and self.resolve_ns(t[len(p) + 1:], sn, self.isns_new) == [t]:
                                txt = t[len(p) + 1:]
                                break
                    if txt not in new_items:
                        new_items.append(txt)
                        n_items.append((t, set()))
        for s, it in ((so, o_items), (sn, n_items)):
            if is_in:
                s.pending, s.state = it, "waiting"
            else:
                s.add_open(it)
        if not new_items:
            return None
        if new_items == words:
            return m.group(0)
        return m.group(1) + "open " + " ".join(new_items) + (m.group(3) or "") + m.group(4)

    def isns_old(self, name):
        return name in self.old_ns_all

    def isns_new(self, name):
        return name in self.new_ns_all

    def text_line(self, body, segs, so, sn, ctx, here):
        out = []
        for kind, text in segs:
            if kind == "string":
                out.append(text)
                continue
            # paths first: a file name can also be a declaration name (`E2e/CpMarshal.lean`)
            text = sub_paths(text, self.m.path_re, self.m.paths)
            out.append(TOKEN.sub(lambda mt: self.ref_token(mt.group(0), so, sn, ctx, kind == "code", here), text))
        return "".join(out)

    def ref_token(self, tok, so, sn, ctx, code, here):
        res = self.resolve(tok, so, self.exists_old)
        if not res and not code and self.file_scope is not None:
            # a comment above the `open` lines (a file header): resolve in the scope of the first namespace block
            so, sn = self.file_scope
            res = self.resolve(tok, so, self.exists_old)
        mine = [(f, s) for f, s in res if self.mine_old(f)]
        if res and len(mine) == len(res) and len({self.mine_old(f)[0][0][0] for f, _ in mine}) == 1:
            f, suf = mine[0]
            rows, rest = self.mine_old(f)
            base = f[:len(f) - len(rest)] if rest else f
            mod = here if isinstance(here, str) and "/" not in here else None
            nf = self.target(base, mod) if mod else rows[0][0]
            written_full = tok == f + suf or tok.startswith("_root_.")
            if not code and "." not in tok and nf.rsplit(".", 1)[-1] == tok:
                return tok      # a short name in a comment whose last component does not change (often a word)
            return self.emit(nf + rest, sn, written_full, ctx) + suf
        if res and mine:
            self.warn.append(f"{ctx}: {tok} resolves to {res}; left unchanged")
            return tok
        if not res:
            # a module name or a namespace of the map that is not a declaration (comments, `#check`, ...)
            if tok in self.mod_map:
                return self.mod_map[tok]
            for o, n, _, w in self.m.ns_rows4:
                if w == "whole" and (tok == o or tok.startswith(o + ".")) and not self.mine_old(tok):
                    return n + tok[len(o):]
        if code and not mine:
            r2 = self.resolve(tok, sn, self.exists_new)
            if any(self.mine_new(f) for f, _ in r2):
                self.warn.append(f"{ctx}: unchanged token {tok} now resolves to {r2} (capture?)")
        return tok

    # -- JSON case files (negative cases and their result records) ------------------------------------------------
    def json_file(self, rel, text, lines, lean_scopes):
        self.file_scope = None
        try:
            data = json.loads(text)
        except ValueError:
            return None
        cases = data if isinstance(data, list) else data.get("cases") if isinstance(data, dict) else None
        if not isinstance(cases, list) or not cases or not all(isinstance(c, dict) and "module" in c and "theorem" in c
                                                                for c in cases):
            return None
        spans = json_object_spans(text)
        out = list(lines)
        lstart = [0]
        for ln in lines:
            lstart.append(lstart[-1] + len(ln))
        tops = [s for s in spans if s[2] == (1 if isinstance(data, list) else 2) and '"theorem": ' in text[s[0]:s[1]]]
        if len(tops) != len(cases):
            return None
        for (a, b, _), c in zip(tops, cases):
            info = lean_scopes.get("fv/kraken/lean/" + c["module"])
            if info is None:
                continue
            scope = info.get(c["theorem"])
            if scope is None:
                continue
            so, sn, mod_new, oldfull = scope
            la = next(i for i in range(len(lines)) if lstart[i + 1] > a)
            lb = next(i for i in range(len(lines)) if lstart[i + 1] > b)
            for i in range(la, lb + 1):
                mk = JSON_KV.match(lines[i].rstrip("\n"))
                if not mk:
                    continue
                key, val = mk.group(2), json.loads(mk.group(3))
                ascii_ = all(ord(ch) < 128 for ch in lines[i])
                if key == "theorem":
                    nv = self.target(oldfull, mod_new) if oldfull in self.old_rows else val
                elif key == "code_def":
                    nv = self.ref_token(val, so, sn, f"{rel}:{i + 1}", True, mod_new)
                elif key == "code_ns":
                    r = self.resolve_ns(val, so, self.isns_old)
                    nv = val
                    if r and r[0] in self.old_ns_mine:
                        tg = [n for o, n, s in self.m.open_rows if o == r[0]
                              and (s == (self.type_of(sn.ns()) or "-") or s == "*")]
                        nv = tg[0] if tg else val
                elif key in CASE_KEYS_CODE:
                    segs, _ = lean_segments(val, 0)
                    nv = self.text_line(val, segs, so, sn, f"{rel}:{i + 1}", mod_new) if "\n" not in val else \
                        "\n".join(self.text_line(x, lean_segments(x, 0)[0], so, sn, f"{rel}:{i + 1}", mod_new)
                                  for x in val.split("\n"))
                else:
                    continue
                if nv != val:
                    nl = "\n" if lines[i].endswith("\n") else ""
                    out[i] = mk.group(1) + '"' + key + '": ' + json.dumps(nv, ensure_ascii=ascii_) + mk.group(4) + nl
        return out


def copy_scope(sc):
    c = RefScope()
    c.stack = [[k, n, list(o)] for k, n, o in sc.stack]
    c.top_opens = list(sc.top_opens)
    return c


def json_object_spans(text):
    """(start offset, end offset, depth) of every JSON object in `text` (depth 1 = element of the top value)."""
    spans, stack, i, n, depth = [], [], 0, len(text), 0
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
        elif c in "{[":
            stack.append((c, i, depth))
            depth += 1
        elif c in "}]":
            k, s, d = stack.pop()
            depth -= 1
            if k == "{":
                spans.append((s, i, d))
        i += 1
    return spans


def forward_ref(maps, root):
    R = RefRename(maps, root)
    R.errors = []
    tooldir = R.tooldir
    for o, n in maps.files:
        if not os.path.exists(os.path.join(root, o)):
            die(f"missing old file {o}")
        if os.path.exists(os.path.join(root, n)):
            die(f"new file exists already: {n}")
    files = list_files(root, tooldir)
    texts = {}
    for rel in files:
        if maps.protected(rel):
            continue
        t = read_text(os.path.join(root, rel))
        if t is not None:
            texts[rel] = t
    # 1. inverse safety: no new full name, module or path occurs in the old text
    newkeys = set(maps.inv_tok) | set(getattr(maps, "inv_tok_extra", {}))
    bad = []
    for rel, text in texts.items():
        for mt in TOKEN.finditer(text):
            t = mt.group(0) if rel.endswith(".lean") else mt.group(0).rstrip("'!?")
            parts = t.split(".")
            if any(".".join(parts[:i]) in newkeys for i in range(len(parts), 1, -1)):
                bad.append(f"{rel}: {t}")
        if maps.inv_path_re is not None:
            for mt in maps.inv_path_re.finditer(text):
                bad.append(f"{rel}: path {mt.group(1)}")
    if bad:
        print("\n".join(bad[:50]), file=sys.stderr)
        die(f"{len(bad)} occurrences of new names in the old tree: the inverse would not be exact")
    newpath = dict(maps.files)
    # 2. module graph and namespaces of the new tree (for the availability of an `open`)
    R.imports_new, R.clo_cache, regs = {}, {}, {}
    old_regs_all = set()
    for rel, text in texts.items():
        mo = module_of(rel)
        if not mo:
            continue
        ls = text.splitlines(keepends=True)
        mn = maps.modules.get(mo, mo)
        R.imports_new[mn] = [maps.modules.get(i, i) for i in imports_of(ls)]
        rg = registered(ls)
        old_regs_all |= rg
        if mo in maps.modules:
            rg = set()
            for o, rows in R.old_rows.items():
                for n, m2 in rows:
                    if m2 == mn:
                        p = n.split(".")
                        rg |= {".".join(p[:i]) for i in range(1, len(p))}
            for o, n, scope, _ in maps.ns_rows4:
                sm = scope.split("#")[0]
                if mn == sm or mn.startswith(sm + "."):
                    p = n.split(".")
                    rg |= {".".join(p[:i]) for i in range(1, len(p) + 1)}
        regs[mn] = rg
    R.old_ns_all = old_regs_all | R.old_ns_mine | {x for x in R.declared}
    R.new_ns_all = set()
    for v in regs.values():
        R.new_ns_all |= v
    R.new_ns_all |= R.new_ns_mine | {x for x in R.declared if not R.mine_old(x)}
    # 3. Lean files
    newtexts, aligned, lean_scopes = {}, {}, {}
    for rel, text in texts.items():
        if not rel.endswith(".lean"):
            continue
        reln = newpath.get(rel, rel)
        mn = module_of(reln)
        clo = set()
        if mn:
            clo = R.closure_new(mn) | {mn}
        else:
            for i in imports_of(text.splitlines(keepends=True)):
                i2 = maps.modules.get(i, i)
                clo |= R.closure_new(i2) | {i2}
        R.avail = set()
        for m2 in clo:
            R.avail |= regs.get(m2, set())
        lines = text.splitlines(keepends=True)
        out = R.lean_file(rel, reln, lines)
        aligned[reln] = (lines, out)
        lean_scopes[rel] = theorem_scopes(R, rel, reln, lines)
    # 4. other text files
    for rel, text in texts.items():
        if rel.endswith(".lean"):
            continue
        reln = newpath.get(rel, rel)
        lines = text.splitlines(keepends=True)
        out = R.json_file(rel, text, lines, lean_scopes) if rel.endswith(".json") else None
        if out is None:
            out = list(lines)
        res = []
        for ln, cur in zip(lines, out):
            if cur != ln:
                res.append(cur)
                continue
            body, nl = (ln[:-1], "\n") if ln.endswith("\n") else (ln, "")
            nb = sub_paths(body, maps.path_re, maps.paths)
            nb = sub_tokens(nb, maps.tok, R.text_short, False)
            res.append(nb + nl)
        aligned[reln] = (lines, res)
    if R.errors:
        print("\n".join(R.errors[:80]), file=sys.stderr)
        die(f"{len(R.errors)} errors")
    # 5. records: lines that the rule-based inverse does not restore
    records, final = [], {}
    for reln, (old, new) in aligned.items():
        is_lean = reln.endswith(".lean")
        fl = []
        for o, n in zip(old, new):
            if n is None:
                records.append((reln, len(fl) + 1, "delete", "", o.rstrip("\n")))
                continue
            if n.endswith("\n") != o.endswith("\n"):
                die(f"{reln}: line end changed")
            if rule_inverse_line(maps, n, is_lean) != o:
                records.append((reln, len(fl) + 1, "replace", n.rstrip("\n"), o.rstrip("\n")))
            fl.append(n)
        final[reln] = fl
    # 6. manual edits
    for path, line, before, after in maps.manual:
        ls = final.get(path)
        if ls is None:
            die(f"manual edit: no text file {path}")
        if line < 1 or line > len(ls) or ls[line - 1].rstrip("\n") != before:
            die(f"manual edit {path}:{line}: the line is not {before!r} but {ls[line - 1].rstrip(chr(10))!r}")
        ls[line - 1] = after + ("\n" if ls[line - 1].endswith("\n") else "")
    # 7. the inverse in memory must give the old text back
    byf = {}
    for r in records:
        byf.setdefault(r[0], []).append(r)
    inv_manual = {}
    for path, line, before, after in maps.manual:
        inv_manual.setdefault(path, []).append((line, before))
    for reln, fl in final.items():
        ls = list(fl)
        for line, before in inv_manual.get(reln, []):
            ls[line - 1] = before + ("\n" if ls[line - 1].endswith("\n") else "")
        for _, line, action, new, old in sorted(byf.get(reln, []), key=lambda x: (-x[1], x[2] != "replace")):
            if action == "replace":
                ls[line - 1] = old + ("\n" if ls[line - 1].endswith("\n") else "")
            elif action == "delete":
                ls.insert(line - 1, old + "\n")
        back = "".join(rule_inverse_line(maps, x, reln.endswith(".lean")) for x in ls)
        orig = [o for o, n in maps.files if n == reln]
        if back != texts[orig[0] if orig else reln]:
            die(f"internal: the inverse of {reln} is not the old text")
    # 8. write
    for o, n in maps.files:
        os.makedirs(os.path.dirname(os.path.join(root, n)), exist_ok=True)
        os.rename(os.path.join(root, o), os.path.join(root, n))
    for o, _ in maps.files:
        d = os.path.dirname(os.path.join(root, o))
        while d.startswith(os.path.join(root, "fv")) and os.path.isdir(d) and not os.listdir(d):
            os.rmdir(d)
            d = os.path.dirname(d)
    changed = 0
    for reln, fl in final.items():
        orig = [o for o, n in maps.files if n == reln]
        if "".join(fl) != texts[orig[0] if orig else reln]:
            changed += 1
            write_text(os.path.join(root, reln), "".join(fl))
    with open(os.path.join(maps.dir, "applied-lines.tsv"), "w", encoding="utf-8") as f:
        f.write("# written by rename.py forward; read by rename.py inverse. path\tline\taction\tnew text\told text\n")
        for r in records:
            f.write("\t".join(str(x) for x in r) + "\n")
    for w in R.warn:
        print("warning: " + w, file=sys.stderr)
    print(f"forward: {len(maps.files)} files moved, {changed} files rewritten, {len(records)} line records, "
          f"{len(R.warn)} warnings")
    return 0


def rule_inverse_line(maps, ln, is_lean):
    body, nl = (ln[:-1], "\n") if ln.endswith("\n") else (ln, "")
    if is_lean:
        m = IMPORT.match(body)
        if m:
            inv_mod = {n: o for o, n in maps.modules.items()}
            return m.group(1) + inv_mod.get(m.group(2), m.group(2)) + m.group(3) + nl
    nb = sub_tokens(body, maps.inv_tok, maps.inv_short, is_lean)
    return sub_paths(nb, maps.inv_path_re, maps.inv_paths) + nl


def theorem_scopes(R, rel, reln, lines):
    """For a Lean file: written theorem name -> (old scope, new scope, new module, old full name) at its line, for
    the JSON case files (their `theorem` field is the name as written on the declaration line)."""
    so = RefScope()
    sn = RefScope()
    out = {}
    depth = 0
    mn = module_of(reln)
    for ln in lines:
        body = ln.rstrip("\n")
        sd = depth
        _, depth = lean_segments(body, depth)
        if sd:
            continue
        m = NAMESPACE.match(body)
        if m:
            so.stack.append(["ns", m.group(2), []])
            continue
        if SECTION.match(body):
            so.stack.append(["sec", "", []])
            continue
        if END.match(body) and so.stack:
            so.stack.pop()
            continue
        mo = REF_OPEN.match(body)
        if mo and not mo.group(3):
            so.add_open([(x, set()) for w in mo.group(2).split() for x in R.resolve_ns(w, so, R.isns_old)])
            continue
        md = REF_CMD_DECL.match(body)
        if md:
            nm = md.group(2)
            full = nm[7:] if nm.startswith("_root_.") else (so.ns() + "." if so.ns() else "") + nm
            sc = RefScope()
            sc.stack = [list(x) for x in so.stack]
            sc.top_opens = list(so.top_opens)
            if "." in nm and not nm.startswith("_root_."):
                sc.declns = nm.rsplit(".", 1)[0]
            out.setdefault(nm, (sc, new_scope_for(R, full, mn, sc), mn, full))
    return out


def new_scope_for(R, full, mn, so):
    """The new scope at a declaration line: the new namespace of the declaration and the mapped opens."""
    sn = RefScope()
    nf = R.target(full, mn) if full in R.old_rows else full
    ns = nf.rsplit(".", 1)[0] if "." in nf else ""
    sn.stack = [["ns", ns, []]] if ns else []
    t = R.type_of(ns) or (R.type_of(mn) if mn else None) or "-"
    ops = []
    for o, _ in so.opens():
        tg = [n for a, n, s in R.m.open_rows if a == o and (s == t or s == "*")]
        ops += [(x, set()) for x in tg] if o in R.old_ns_mine else [(o, set())]
    sn.top_opens = ops
    return sn



SELFTEST_TREE = {
    "fv/kraken/lean/A/X.lean": "namespace Old\ntheorem foo : True := trivial\nend Old\n",
    "fv/kraken/lean/B/Y.lean": "namespace Old\ntheorem foo : True := trivial\nend Old\n",
    "fv/kraken/lean/C/UseA.lean": "import A.X\nopen Old\nexample : True := foo  -- `foo`\n",
    "fv/kraken/lean/D/UseB.lean": "import B.Y\nexample : True := Old.foo\n",
    "fv/kraken/lean/E/Two.lean": ("namespace Old2\ntheorem a : True := trivial\ntheorem c : True := trivial\nend Old2\n\n"
                                  "namespace Old2\ntheorem b : True := a\nend Old2\n"),
    "fv/kraken/doc.md": "`Old2.b` and `E/Two.lean`\n",
}
SELFTEST_MAP = {
    "files.tsv": "fv/kraken/lean/A/X.lean\tfv/kraken/lean/Prysm/TA/X.lean\tx\n"
                 "fv/kraken/lean/B/Y.lean\tfv/kraken/lean/Prysm/TB/Y.lean\ty\n"
                 "fv/kraken/lean/E/Two.lean\tfv/kraken/lean/Prysm/TA/Two.lean\ttwo blocks\n",
    "names.tsv": "type\tPrysm.TA\t-\t-\t-\ntype\tPrysm.TB\t-\t-\t-\n"
                 "namespace\tOld\tPrysm.TA\tPrysm.TA.X\tpart\nnamespace\tOld\tPrysm.TB\tPrysm.TB.Y\tpart\n"
                 "namespace\tOld2\tPrysm.TA\tPrysm.TA.Two#1\tpart\nnamespace\tOld2\tPrysm.TB\tPrysm.TA.Two#2\tpart\n"
                 "declaration\tOld.foo\tPrysm.TA.Decode.accept\tPrysm\tPrysm.TA.X\n"
                 "declaration\tOld.foo\tPrysm.TB.Decode.accept\tPrysm\tPrysm.TB.Y\n"
                 "declaration\tOld2.a\tPrysm.TA.Decode.reject\tPrysm\tPrysm.TA.Two\n"
                 "declaration\tOld2.c\tPrysm.TB.Code.c\tPrysm\tPrysm.TA.Two\n"
                 "declaration\tOld2.b\tPrysm.TB.Decode.accept_two\tPrysm\tPrysm.TA.Two\n",
}
SELFTEST_WANT = {
    "fv/kraken/lean/Prysm/TA/X.lean": "namespace Prysm.TA\ntheorem Decode.accept : True := trivial\nend Prysm.TA\n",
    "fv/kraken/lean/Prysm/TB/Y.lean": "namespace Prysm.TB\ntheorem Decode.accept : True := trivial\nend Prysm.TB\n",
    "fv/kraken/lean/C/UseA.lean": "import Prysm.TA.X\nexample : True := Prysm.TA.Decode.accept  -- `Prysm.TA.Decode.accept`\n",
    "fv/kraken/lean/D/UseB.lean": "import Prysm.TB.Y\nexample : True := Prysm.TB.Decode.accept\n",
    "fv/kraken/lean/Prysm/TA/Two.lean": ("namespace Prysm.TA\ntheorem Decode.reject : True := trivial\n"
                                         "theorem _root_.Prysm.TB.Code.c : True := trivial\nend Prysm.TA\n\n"
                                         "namespace Prysm.TB\ntheorem Decode.accept_two : True := Prysm.TA.Decode.reject\n"
                                         "end Prysm.TB\n"),
    "fv/kraken/doc.md": "`Prysm.TB.Decode.accept_two` and `Prysm/TA/Two.lean`\n",
}


def selftest():
    """Reference mode on a small tree: two modules that declare the same old name, a module with two namespace
    blocks of two types, a root-qualified declaring line, the removal of an `open`, and the exact inverse."""
    import tempfile
    bad = []
    with tempfile.TemporaryDirectory() as t:
        root, md = os.path.join(t, "repo"), os.path.join(t, "map")
        os.makedirs(md)
        for rel, txt in SELFTEST_TREE.items():
            os.makedirs(os.path.dirname(os.path.join(root, rel)), exist_ok=True)
            write_text(os.path.join(root, rel), txt)
        for n, txt in SELFTEST_MAP.items():
            write_text(os.path.join(md, n), txt)
        forward_ref(Maps(md), root)
        for rel, want in SELFTEST_WANT.items():
            got = read_text(os.path.join(root, rel))
            if got != want:
                bad.append(f"forward {rel}: {got!r} != {want!r}")
        inverse(Maps(md), root)
        for rel, txt in SELFTEST_TREE.items():
            got = read_text(os.path.join(root, rel)) if os.path.exists(os.path.join(root, rel)) else None
            if got != txt:
                bad.append(f"inverse {rel}: {got!r}")
    print("selftest", "PASS" if not bad else "FAIL\n" + "\n".join(bad))
    return 1 if bad else 0


def main(argv):
    if argv[1:] == ["--selftest"]:
        return selftest()
    if len(argv) < 3 or argv[1] not in ("forward", "inverse"):
        die(__doc__.strip().splitlines()[2].strip() + "  (see the docstring)", 2)
    mode, mapdir = argv[1], os.path.abspath(argv[2])
    root = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", ".."))
    if "--root" in argv:
        root = os.path.abspath(argv[argv.index("--root") + 1])
    maps = Maps(mapdir)
    if mode == "forward":
        return forward_ref(maps, root) if maps.ref else forward(maps, root)
    return inverse(maps, root)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
