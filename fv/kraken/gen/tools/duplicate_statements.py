#!/usr/bin/env python3
"""Groups of theorems with the same statement, with a class and a reason for each group.

usage (from the repository root, or give --root):
  python3 -I -B fv/kraken/gen/tools/duplicate_statements.py <gate dump.tsv> [--root fv/kraken]
          --regen <regen result.txt> [--out <groups.tsv>]
  python3 -I -B fv/kraken/gen/tools/duplicate_statements.py --selftest

  <gate dump.tsv>  the dump of the axioms gate: `python3 -I -B fv/kraken/gen/e2e/axioms_gate.py run <json> <dump.tsv>`.
                   Columns: name, kind, statement (type) hash, value hash, axioms.
  --root           the directory fv/kraken of the tree that gave the dump (default: fv/kraken).
  --regen          the result of `gen/restructure/tools/regen.py` for the same tree (required). Its third column
                   names the generated files (rows EQ, DIF and NOT). A header comment is not used: hand files also
                   name generators in their comments.
  --out            write the table here (default: standard output). The summary goes to standard error.

A group is a set of two or more theorems that are not internal (no name component starts with `_`) and that have the
same statement hash. The table has one row per member: group id, name, module, class, reason.
The tool gives each group exactly one class. It applies the rules in this order:

  1. lean-derived       a member is an equation or structure lemma that Lean makes (`eq_1`, `eq_def`, `inj`, `injEq`,
                        `sizeOf_spec`, ...). Lean makes it again from its definition, so it is not text to remove.
  2. generated          every member is in a generated file. A generated file must equal a fresh generator run.
                        Usually one generator writes the same statement in two modes (for example root field segment
                        and step), or for two types with the same layout.
  3. generated-and-hand a member is in a generated file, and each other member is the hand statement that a generator
                        identity names (`--same-as`), or a second derivation (rule 4). The generated theorem stays (rule 2).
  4. checked-derivation each hand member is a second derivation that a check compares: a kind identity (`_kind`), an
                        identity (`_same`, `_type`, a statement written as `type_of% @A`, or a name in an identity `@A = @B := rfl` or `type_of% @A` of a
                        module that sees it), an instance of a general lemma (`_inst`, or a theorem in a module
                        whose name ends with `Instances`: Lean checks that the general lemma covers it), an example or a theorem
                        in a file that kindcheck.py reads (`Generated*.lean`, `Decode*Example*.lean`), or a name that a
                        negative case or a generator identity (`--same-as`) names, or an end result: no module uses
                        it and a hand list of `gen/axioms-lists/` prints its axioms (the same statement proved by
                        another route, for example from generated segments; not when its text names a twin, as an
                        alias does). For a theorem with uses, a hand list is
                        not a reason: it only prints axioms (a deletion names the kept twin in the list).
  5. not-visible        no hand member that rule 4 leaves free has a twin that is visible at its declaration and at
                        every use: a use is in a module that does not import (directly or through other modules) the
                        module of the twin. Removing the member would need a new import.
  6. other-binders      a free hand member has a twin that is visible everywhere, but the binders before the colon
                        differ in kind (explicit `(`, implicit `{`, instance `[`). The statement hash does not see the
                        binder kind; each use would need other arguments, so the member is not a plain duplicate.
  7. delete-candidate   a free hand member has a twin that is visible at its declaration and at every use, and no
                        check names it. The member can be removed and its uses can name the twin.
  8. unclassified       a member has no module in the tree (the tool did not find its declaration).

exit 0: no group is in class delete-candidate or unclassified. 1: there is such a group. 2: usage or input error.

Limits: the tool reads text. It finds a declaration by its keyword and the `namespace` / `section` / `end` lines.
A name that a macro or an `elab` declares is not found (class unclassified). It finds a use by a token that is equal to
the full name or to a dotted end part of it (`Decode.head` for `Prysm.Eth1Data.Decode.head`), in a module that imports
the module of the name. A short end part that many types share counts as a use of each of them; this can only make a
group not-visible that a closer look would make a delete-candidate. It does not see a use through `open ... renaming`,
`export` or a notation. The statement hash is from Lean: equal hashes mean equal statements after elaboration.
Python 3 standard library only.
"""
import collections
import json
import os
import re
import sys
import tempfile

DERIVED = re.compile(r'^(eq_\d+|eq_def|inj|injEq|sizeOf_spec|ext|ext_iff|eta|mk\.injEq|noConfusion|recOn|casesOn|elim)$')
SECOND = re.compile(r'(_kind|_same|_type|_inst)$')
KINDCHECK_FILE = re.compile(r'(^|/)(Generated[^/]*|Decode[^/]*Example[^/]*)\.lean$')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|public|meta)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([^\s:({\[⦃]+)')
IDENTITY = re.compile(r"@\(?([A-Za-z_«][\w.'«»]*)\)?\s*=\s*@\(?([A-Za-z_«][\w.'«»]*)\)?\s*:=\s*(?:by\s+)?rfl")
TYPE_OF = re.compile(r"type_of%\s*\(?\s*@?([A-Za-z_«][\w.'«»]*)")
NAME_LITERAL = re.compile(r"(?<![\w`])`([A-Za-z_«][\w.'«»]*)")
TOKEN = re.compile(r"[A-Za-z_«][\w.'!?«»]*")
CLASSES = ['lean-derived', 'generated', 'generated-and-hand', 'checked-derivation', 'not-visible', 'other-binders',
           'delete-candidate', 'unclassified']


def internal(name):
    return any(c.strip('«»').startswith('_') for c in name.split('.'))


def read_groups(dump):
    by_hash = collections.defaultdict(list)
    for line in open(dump, encoding='utf-8'):
        if line.startswith('#') or not line.strip():
            continue
        row = line.rstrip('\n').split('\t')
        if len(row) < 3:
            sys.exit(f'error: {dump}: a row has fewer than 3 columns: {line[:80]}')
        if row[1] == 'theorem' and not internal(row[0]):
            by_hash[row[2]].append(row[0])
    groups = [sorted(v) for v in by_hash.values() if len(v) > 1]
    return sorted(groups)


def strip_code(text):
    """Remove comments and string literals; keep line breaks so that line numbers stay."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        c = text[i]
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                if c == '\n':
                    out.append(c)
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append('""')
            i = j + 1
        else:
            out.append(c)
            i += 1
    return ''.join(out)


class Tree:
    def __init__(self, root, generated):
        self.root = root
        self.lean = os.path.join(root, 'lean')
        self.files = {}    # module -> relative path from root
        self.imports = {}  # module -> list of modules
        self.tokens = {}   # module -> Counter of tokens
        self.decl = {}     # full name -> (module, line)
        self.code = {}     # module -> lines without comments and strings
        self.literals = {}  # name in a name literal `` `A.b `` -> module (a check program, for example an `elab`)
        self.identities = {}  # module -> names in an identity `@A = @B := rfl` or `type_of% @A`
        self.generated = set()
        for dp, dn, fs in os.walk(self.lean):
            dn[:] = sorted(d for d in dn if d != '.lake')
            for f in sorted(fs):
                if f.endswith('.lean') and f not in ('lakefile.lean',):
                    p = os.path.join(dp, f)
                    rel = os.path.relpath(p, self.lean)
                    self.read(rel[:-5].replace(os.sep, '.'), p)
        for path in generated:
            if path.startswith('lean/') and path.endswith('.lean'):
                self.generated.add(path[len('lean/'):-5].replace('/', '.'))
        self.closure_cache = {}

    def read(self, module, path):
        raw = open(path, encoding='utf-8').read()
        self.files[module] = os.path.relpath(path, self.root)
        code = strip_code(raw)
        imps = []
        stack = []  # ('ns', components) or ('sec', name) or ('mutual', '')
        for no, line in enumerate(code.split('\n'), 1):
            s = line.strip()
            m = re.match(r'^(?:public\s+|meta\s+)*import\s+(.*)$', s)
            if m and not line.startswith(' '):
                imps += m.group(1).split()
                continue
            if line.startswith((' ', '\t')):
                continue
            m = re.match(r'^namespace\s+(\S+)', s)
            if m:
                stack.append(('ns', m.group(1).split('.')))
                continue
            m = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?', s)
            if m:
                stack.append(('sec', m.group(1) or ''))
                continue
            if s == 'mutual':
                stack.append(('mutual', ''))
                continue
            m = re.match(r'^end(?:\s+(\S+))?\s*$', s)
            if m:
                name = m.group(1)
                if stack:
                    if name is None:
                        stack.pop()
                    else:
                        while stack:
                            k = stack.pop()
                            if k[0] == 'ns' and '.'.join(k[1]) == name or k[0] == 'sec' and k[1] == name:
                                break
                continue
            m = DECL.match(s)
            if m:
                name = m.group(2).replace('«', '').replace('»', '')
                if name.startswith('_root_.'):
                    full = name[len('_root_.'):]
                else:
                    ns = [c for k in stack if k[0] == 'ns' for c in k[1]]
                    full = '.'.join(ns + [name])
                self.decl.setdefault(full, (module, no))
        self.imports[module] = imps
        ids = set()
        for m in IDENTITY.finditer(code):
            ids.update(x.replace('«', '').replace('»', '') for x in m.groups() if x)
        for m in TYPE_OF.finditer(code):
            ids.add(m.group(1).replace('«', '').replace('»', ''))
        self.identities[module] = ids
        self.tokens[module] = collections.Counter(t.replace('«', '').replace('»', '') for t in TOKEN.findall(code))
        self.code[module] = code.split('\n')
        for m in NAME_LITERAL.finditer(code):
            self.literals.setdefault(m.group(1).replace('«', '').replace('»', ''), module)

    def closure(self, module):
        if module not in self.closure_cache:
            seen, todo = set(), [module]
            while todo:
                m = todo.pop()
                for i in self.imports.get(m, ()):
                    if i not in seen:
                        seen.add(i)
                        todo.append(i)
            self.closure_cache[module] = seen
        return self.closure_cache[module]

    def locate(self, name):
        """(module, line, derived) of a name; derived is True for a lemma that Lean makes from a declaration."""
        if name in self.decl:
            return self.decl[name] + (False,)
        parts = name.split('.')
        for k in range(len(parts) - 1, 0, -1):
            parent = '.'.join(parts[:k])
            if parent in self.decl and DERIVED.match('.'.join(parts[k:])):
                return self.decl[parent] + (True,)
        if len(parts) > 1 and DERIVED.match(parts[-1]):
            return ('-', 0, True)  # the lemma of a declaration that a command (macro, elab) makes
        return None

    def users(self, name, module):
        """Modules other than the declaring module that hold a token equal to the name or a dotted end part of it,
        and that import the declaring module."""
        parts = name.split('.')
        ends = {'.'.join(parts[k:]) for k in range(len(parts))}
        out = []
        for m, toks in self.tokens.items():
            if m == module or module not in self.closure(m):
                continue
            if any(e in toks for e in ends):
                out.append(m)
        return out

    def in_identity(self, name, module):
        """A module that compares the name with another one by an identity: the full name in a module that imports
        the declaring module, or a dotted end part in the declaring module or in a module of the same type directory."""
        parts = name.split('.')
        ends = {'.'.join(parts[k:]) for k in range(len(parts))}
        scope = parts[:2]
        for m, ids in self.identities.items():
            if name in ids and (m == module or module in self.closure(m)):
                return m
            if ids & ends and (m == module or m.split('.')[:2] == scope and module in self.closure(m)):
                return m
        return None

    def binders(self, name):
        """The kinds of the binders before the colon of the declaration, for example '({{('."""
        module, line, _ = self.locate(name)
        text = ' '.join(self.code[module][line - 1:line + 40])
        m = DECL.match(text.strip())
        if not m:
            return None
        rest, depth, kinds = text.strip()[m.end():], 0, []
        for c in rest:
            if c in '({[⦃':
                if depth == 0:
                    kinds.append(c)
                depth += 1
            elif c in ')}]⦄':
                depth -= 1
            elif c == ':' and depth == 0:
                break
        return ''.join(kinds)

    def header(self, name):
        """The declaration text of the name up to the first `:=`."""
        module, line, _ = self.locate(name)
        return ' '.join(self.code[module][line - 1:line + 40]).split(':=')[0]

    def body_tokens(self, name):
        """The tokens of the declaration text of the name, up to the next line that is not indented."""
        module, line, _ = self.locate(name)
        lines = self.code[module]
        out = [lines[line - 1]]
        for s in lines[line:]:
            if s and not s[0].isspace():
                break
            out.append(s)
        return {x.replace('«', '').replace('»', '') for x in TOKEN.findall('\n'.join(out))}

    def uses_in_module(self, name, module):
        """Number of tokens in the declaring module that name it, without the declaration itself."""
        parts = name.split('.')
        ends = {'.'.join(parts[k:]) for k in range(len(parts))}
        return sum(self.tokens[module][e] for e in ends) - 1


def checked_names(root):
    """Names that a check names: negative cases, generator identities (`--same-as`), and the hand lists of
    `gen/axioms-lists/` (a hand list prints the axioms of a name; it does not compare two statements, so it is not a
    reason to keep a duplicate: a deletion names the kept twin in the list)."""
    names = {}
    for dp, dn, fs in os.walk(root):
        dn[:] = sorted(d for d in dn if d not in ('.lake', '.git'))
        for f in sorted(fs):
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, root)
            if 'negcases' in f and f.endswith('.json'):
                d = json.load(open(p, encoding='utf-8'))
                cases = d if isinstance(d, list) else d.get('cases', [])
                for c in cases:
                    if isinstance(c, dict) and c.get('theorem'):
                        names.setdefault(('case', c['theorem'], c.get('module', '')), rel)
            elif rel.startswith('gen' + os.sep + 'axioms-lists' + os.sep) and f.endswith('.lean'):
                for m in re.finditer(r'#print\s+axioms\s+(\S+)', open(p, encoding='utf-8').read()):
                    names.setdefault(('list', m.group(1), ''), rel)
            elif f.endswith(('.sh', '.lean')) and not rel.startswith('gen' + os.sep + 'restructure'):
                text = open(p, encoding='utf-8', errors='replace').read()
                if '--same-as' in text:
                    for m in re.finditer(r'--same-as(?:-prop)?[ =]+([A-Za-z_][\w.\']*)', text):
                        names.setdefault(('same-as', m.group(1), ''), rel)
    return names


def resolve_checked(tree, checked):
    """Map each checked entry to a declared full name (a negative case can give a name relative to its module)."""
    out = {}
    for (src, name, module), rel in checked.items():
        if name in tree.decl or tree.locate(name):
            out.setdefault(name, f'{src} in {rel}')
            continue
        mod = module[:-5].replace('/', '.') if module.endswith('.lean') else ''
        hits = [n for n, (m, _) in tree.decl.items() if (n == name or n.endswith('.' + name)) and (not mod or m == mod)]
        if len(hits) == 1:
            out.setdefault(hits[0], f'{src} in {rel}')
    return out


def classify(tree, groups, checked):
    rows, summary = [], collections.defaultdict(lambda: [0, 0])
    for gid, members in enumerate(groups, 1):
        info = {n: tree.locate(n) for n in members}
        reason = ''
        free = []
        if any(v is None for v in info.values()):
            cls = 'unclassified'
            reason = 'no declaration found for ' + ', '.join(n for n, v in info.items() if v is None)
        elif any(v[2] for v in info.values()):
            cls = 'lean-derived'
            reason = 'Lean makes ' + ', '.join(n for n, v in info.items() if v[2]) + ' from its declaration' + \
                ('' if all(v[0] != '-' for v in info.values()) else ' (a command declares it, no text in the tree)')
        else:
            gen = [n for n in members if info[n][0] in tree.generated]
            hand = [n for n in members if n not in gen]

            def why(n):
                mod = info[n][0]
                parts = n.split('.')
                last = parts[-1]
                if SECOND.search(last):
                    return 'second derivation (' + SECOND.search(last).group(1) + ')'
                if last.startswith('example'):
                    return 'example'
                if mod.endswith('Instances'):
                    return 'instance of a general lemma (module ' + mod + ')'
                if KINDCHECK_FILE.search(tree.files[mod]):
                    return 'in a file that kindcheck.py reads'
                if 'type_of%' in tree.header(n):
                    return 'second derivation: its statement is written as `type_of%` of another theorem'
                if n in checked and not checked[n].startswith('list '):
                    return checked[n]
                if n in tree.literals:
                    return 'a check program names it (name literal in ' + tree.files[tree.literals[n]] + ')'
                idm = tree.in_identity(n, mod)
                if idm:
                    return 'identity check in ' + tree.files[idm]
                if last.startswith('runs') and 'Witness' in parts:
                    return 'witness of a work unit (shows that the premises can hold)'
                body = tree.body_tokens(n)
                alias = any(b != n and {'.'.join(b.split('.')[k:]) for k in range(len(b.split('.')))} & body
                            for b in members)
                if n in checked and not alias and not tree.users(n, mod) and tree.uses_in_module(n, mod) <= 0:
                    return 'end result of its own proof route (no use; the ' + checked[n] + ' prints its axioms)'
                return ''
            reasons = {n: why(n) for n in hand}
            free = [n for n in hand if not reasons[n]]
            if not hand:
                cls = 'generated'
                reason = 'every member is generator output: ' + ', '.join(sorted({tree.files[info[n][0]] for n in gen}))
            elif not free:
                cls = 'generated-and-hand' if gen else 'checked-derivation'
                reason = '; '.join(f'{n}: {reasons[n]}' for n in hand)
                if gen:
                    reason = 'generated: ' + ', '.join(gen) + '; hand: ' + reason
            else:
                movable, other = [], []
                for a in free:
                    ma = info[a][0]
                    users = tree.users(a, ma)
                    for b in members:
                        if b == a:
                            continue
                        mb = info[b][0]
                        ok = (mb == ma and info[b][1] < info[a][1]) or mb in tree.closure(ma)
                        if ok and all(mb == u or mb in tree.closure(u) for u in users):
                            if tree.binders(a) != tree.binders(b):
                                other.append((a, b))
                                continue
                            movable.append((a, b, users))
                            break
                if movable:
                    cls = 'delete-candidate'
                    reason = '; '.join(f'{a} can name {b} ({len(u)} user modules'
                                       + (f'; the {checked[a]} names it: name {b} there' if a in checked else '') + ')'
                                       for a, b, u in movable)
                elif other:
                    cls = 'other-binders'
                    reason = '; '.join(f'{a} and {b}: the same statement with other explicit or implicit binders '
                                       f'({tree.binders(a)} / {tree.binders(b)}); each use would change' for a, b in other)
                else:
                    cls = 'not-visible'
                    parts = []
                    for a in free:
                        ma = info[a][0]
                        hidden = [u for u in [ma] + tree.users(a, ma)
                                  if not any(b != a and (info[b][0] == u or info[b][0] in tree.closure(u)) for b in members)]
                        parts.append(f'{a}: no twin visible in ' + ', '.join(hidden[:3]) + (' ...' if len(hidden) > 3 else ''))
                    reason = '; '.join(parts)
        summary[cls][0] += 1
        summary[cls][1] += len(members)
        for n in members:
            mod = info[n][0] if info[n] else '-'
            rows.append((f'G{gid}', n, mod, cls, reason))
    return rows, summary


def run(dump, root, regen, out):
    generated = [l.split('\t')[2] for l in open(regen, encoding='utf-8')
                 if l.count('\t') >= 2 and l.split('\t')[0] in ('EQ', 'DIF', 'NOT')]
    if not generated:
        sys.exit(f'error: {regen} names no generated file')
    tree = Tree(root, generated)
    groups = read_groups(dump)
    checked = resolve_checked(tree, checked_names(root))
    rows, summary = classify(tree, groups, checked)
    text = '# group\tname\tmodule\tclass\treason\n' + ''.join('\t'.join(r) + '\n' for r in rows)
    if out:
        open(out, 'w', encoding='utf-8').write(text)
    else:
        sys.stdout.write(text)
    sys.stderr.write('class\tgroups\tnames\n')
    for c in CLASSES:
        g, n = summary.get(c, [0, 0])
        sys.stderr.write(f'{c}\t{g}\t{n}\n')
    sys.stderr.write(f'total\t{len(groups)}\t{sum(len(g) for g in groups)}\n')
    bad = summary.get('delete-candidate', [0])[0] + summary.get('unclassified', [0])[0]
    return 1 if bad else 0


# ---------------------------------------------------------------- self-test
FIXTURE = {
    'lean/Base/Def.lean': 'namespace Base\ndef f (n : Nat) : Nat := n + 1\nend Base\n',
    'lean/Base/Lemmas.lean': 'import Base.Def\nnamespace Base\ntheorem f_eq (n : Nat) : f n = n + 1 := rfl\n'
                             'theorem add_zero_hand (n : Nat) : n + 0 = n := rfl\nend Base\n',
    'lean/Base/Other.lean': 'namespace Other\ntheorem add_zero_other (n : Nat) : n + 0 = n := rfl\nend Other\n',
    'lean/Base/Uses.lean': 'import Base.Lemmas\nexample : Base.add_zero_hand 1 = Base.add_zero_hand 1 := rfl\n',
    'lean/T/GeneratedDecodeAccept.lean': '/- written by scalgen.py decoder -/\nnamespace T\ntheorem generated_a : True := trivial\n'
                                         'theorem generated_step_a : True := trivial\n'
                                         'theorem generated_b : 1 = 1 := rfl\n'
                                         'theorem generated_b_kind : 2 = 2 := rfl\nend T\n',
    'lean/T/Accept.lean': 'namespace T\ntheorem accept : 1 = 1 := rfl\ntheorem seg : 2 = 2 := rfl\n'
                          'theorem seg_inst : 3 = 3 := rfl\nend T\n',
    'lean/T/Seg.lean': 'namespace T\ntheorem seg2_inst : 3 = 3 := rfl\nend T\n',
    'lean/T/Plain.lean': 'namespace T\ntheorem lemma_one : 4 = 4 := rfl\nend T\n',
    'lean/T/PlainTwin.lean': 'import T.Plain\nnamespace T\ntheorem lemma_two : 4 = 4 := rfl\nend T\n'
                             'theorem use_two : 4 = 4 := T.lemma_two\n',
    'gen/scal/gen.sh': 'python3 scalgen.py uint64 --same-as T.accept\n',
    'gen/axioms-lists/hand.lean': '#print axioms T.seg\n',
}
DUMP = [('Base.f.eq_1', 'h1'), ('Base.f_eq', 'h1'),              # lean-derived
        ('T.generated_a', 'h2'), ('T.generated_step_a', 'h2'),  # generated
        ('T.generated_b', 'h3'), ('T.accept', 'h3'),            # generated-and-hand (identity names T.accept)
        ('T.generated_b_kind', 'h4'), ('T.seg', 'h4'),          # generated-and-hand (hand list names T.seg)
        ('T.seg_inst', 'h5'), ('T.seg2_inst', 'h5'),            # checked-derivation (two instances)
        ('Base.add_zero_hand', 'h6'), ('Other.add_zero_other', 'h6'),  # not-visible (no module sees both)
        ('T.lemma_one', 'h7'), ('T.lemma_two', 'h7'),           # delete-candidate
        ('T._private_x', 'h8'), ('T._private_y', 'h8')]         # internal: no group


def selftest():
    fails = 0

    def case(label, files, dump, want_classes, want_exit):
        nonlocal fails
        with tempfile.TemporaryDirectory() as d:
            for rel, text in files.items():
                p = os.path.join(d, rel)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                open(p, 'w').write(text)
            dp = os.path.join(d, 'dump.tsv')
            open(dp, 'w').write(''.join(f'{n}\ttheorem\t{h}\t-\t-\n' for n, h in dump))
            tree = Tree(d, ['lean/T/GeneratedDecodeAccept.lean'])
            groups = read_groups(dp)
            rows, summary = classify(tree, groups, resolve_checked(tree, checked_names(d)))
            got = {r[1]: r[3] for r in rows}
            ok = all(got.get(n) == c for n, c in want_classes.items()) and len(got) == len(want_classes)
            bad = summary.get('delete-candidate', [0])[0] + summary.get('unclassified', [0])[0]
            ok = ok and (1 if bad else 0) == want_exit
            print(('ok   ' if ok else 'FAIL ') + label)
            if not ok:
                fails += 1
                for r in rows:
                    print('     ', '\t'.join(r))
    want = {'Base.f.eq_1': 'lean-derived', 'Base.f_eq': 'lean-derived',
            'T.generated_a': 'generated', 'T.generated_step_a': 'generated',
            'T.generated_b': 'generated-and-hand', 'T.accept': 'generated-and-hand',
            'T.generated_b_kind': 'generated-and-hand', 'T.seg': 'generated-and-hand',
            'T.seg_inst': 'checked-derivation', 'T.seg2_inst': 'checked-derivation',
            'Base.add_zero_hand': 'not-visible', 'Other.add_zero_other': 'not-visible',
            'T.lemma_one': 'delete-candidate', 'T.lemma_two': 'delete-candidate'}
    # 1. every class except unclassified; the planted pair lemma_one / lemma_two gives exit 1
    case('every class; planted duplicate pair in hand modules gives exit 1', FIXTURE, DUMP, want, 1)
    # 2. without the planted pair: exit 0
    dump2 = [r for r in DUMP if r[1] != 'h7']
    want2 = {k: v for k, v in want.items() if v != 'delete-candidate'}
    case('without the planted pair: exit 0', FIXTURE, dump2, want2, 0)
    # 3. the planted twin is not visible at a use: not-visible, exit 0
    files3 = dict(FIXTURE)
    files3['lean/T/Plain.lean'] = 'namespace T\ntheorem lemma_one : 4 = 4 := rfl\nend T\n'
    files3['lean/T/PlainTwin.lean'] = 'namespace T\ntheorem lemma_two : 4 = 4 := rfl\nend T\n'
    files3['lean/T/UsesOne.lean'] = 'import T.Plain\ntheorem use_one : 4 = 4 := T.lemma_one\n'
    files3['lean/T/UsesTwo.lean'] = 'import T.PlainTwin\ntheorem use_two : 4 = 4 := T.lemma_two\n'
    want3 = dict(want2, **{'T.lemma_one': 'not-visible', 'T.lemma_two': 'not-visible'})
    case('twins that no user sees together: not-visible, exit 0', files3, DUMP, want3, 0)
    # 4. a name whose declaration the tool cannot find: unclassified, exit 1
    case('a member without declaration: unclassified, exit 1', FIXTURE, dump2 + [('T.made_by_macro', 'h9'), ('T.lemma_one', 'h9')],
         dict(want2, **{'T.made_by_macro': 'unclassified', 'T.lemma_one': 'unclassified'}), 1)
    # 5. a negative case names the free member: checked-derivation, exit 0
    files5 = dict(FIXTURE)
    files5['gen/scal/negcases-x.json'] = json.dumps([{'module': 'T/Plain.lean', 'theorem': 'T.lemma_one', 'kind': 'control', 'id': 'x'},
                                                     {'module': 'T/PlainTwin.lean', 'theorem': 'lemma_two', 'kind': 'control', 'id': 'y'}])
    case('negative cases name both members: checked-derivation, exit 0', files5, DUMP,
         dict(want, **{'T.lemma_one': 'checked-derivation', 'T.lemma_two': 'checked-derivation'}), 0)
    # 6. the planted twin takes its argument as implicit: other-binders, exit 0
    files6 = dict(FIXTURE)
    files6['lean/T/PlainTwin.lean'] = 'import T.Plain\nnamespace T\ntheorem lemma_two {n : Nat} : n = n := rfl\nend T\n'
    files6['lean/T/Plain.lean'] = 'namespace T\ntheorem lemma_one (n : Nat) : n = n := rfl\nend T\n'
    case('the planted pair with other binder kinds: other-binders, exit 0', files6, DUMP,
         dict(want, **{'T.lemma_one': 'other-binders', 'T.lemma_two': 'other-binders'}), 0)
    # 7. the free member is an alias of its twin and no module uses it, but a hand list prints it: still a candidate
    files7 = dict(FIXTURE)
    files7['lean/T/PlainTwin.lean'] = 'import T.Plain\nnamespace T\ntheorem lemma_two : 4 = 4 := lemma_one\nend T\n'
    files7['gen/axioms-lists/hand.lean'] = '#print axioms T.seg\n#print axioms T.lemma_two\n'
    case('an unused alias that a hand list prints: delete-candidate, exit 1', files7, DUMP, want, 1)
    print('selftest:', 'PASS' if not fails else f'{fails} FAILED')
    return 1 if fails else 0


def main(argv):
    if argv == ['--selftest']:
        return selftest()
    args, opts = [], {'--root': 'fv/kraken', '--regen': None, '--out': None}
    i = 0
    while i < len(argv):
        if argv[i] in opts and i + 1 < len(argv):
            opts[argv[i]] = argv[i + 1]
            i += 2
        elif argv[i].startswith('-'):
            sys.stderr.write(__doc__)
            return 2
        else:
            args.append(argv[i])
            i += 1
    if len(args) != 1 or not opts['--regen'] or not os.path.isdir(os.path.join(opts['--root'], 'lean')):
        sys.stderr.write(__doc__)
        return 2
    return run(args[0], opts['--root'], opts['--regen'], opts['--out'])


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
