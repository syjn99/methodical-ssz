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
        for line, action, new, old in sorted(rs, key=lambda x: -x[0]):
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


def main(argv):
    if len(argv) < 3 or argv[1] not in ("forward", "inverse"):
        die(__doc__.strip().splitlines()[2].strip() + "  (see the docstring)", 2)
    mode, mapdir = argv[1], os.path.abspath(argv[2])
    root = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", ".."))
    if "--root" in argv:
        root = os.path.abspath(argv[argv.index("--root") + 1])
    maps = Maps(mapdir)
    return forward(maps, root) if mode == "forward" else inverse(maps, root)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
