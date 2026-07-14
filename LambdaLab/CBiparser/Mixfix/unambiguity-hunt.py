"""Counterexample hunt: do headsDistinct + varDisjoint + interiorTerminates imply Unambiguous?

Mirrors LambdaLab/CBiparser/Mixfix/{Basic,Tree}.lean exactly, single entry (Ent = Unit):

  Notation.toParts  [t1..tk]        = name t1, hole loosest, name t2, ..., hole loosest, name tk
  Operator.toParts  closed n        = nparts
                    prefx  n        = nparts ++ [hole (tighter o)]
                    infx   n        = [hole (tighter o)]   ++ nparts ++ [hole (tighter o)]
                    infxl  n        = [hole (tighterEq o)] ++ nparts ++ [hole (tighter o)]
                    infxr  n        = [hole (tighter o)]   ++ nparts ++ [hole (tighterEq o)]
                    postfx n        = [hole (tighter o)]   ++ nparts
                    juxt            = [hole (tighterEq o), hole (tighter o)]
  Level.condition   tighter a   b   = Tighter   (strict, transitive closure)
                    tighterEq a b   = TighterEq (refl-transitive closure)
                    loosest     b   = exists a in loosest, TighterEq a b
  Expr = op o (cond l o) parts | var t (isVar t)      -- var inhabits EVERY level
"""
import itertools, sys
from functools import lru_cache

NAMES = ["A", "B", "C"]      # candidate operator name tokens
VARS  = ["x"]                # a single variable token (more would just rename)
FIX   = ["closed", "prefx", "infx", "infxl", "infxr", "postfx"]
MAXLEN = 7                   # max flatten length searched


def closure(tighter, nops, strict):
    """reach[a] = {b : Tighter/TighterEq a b}"""
    reach = []
    for a in range(nops):
        seen, frontier = set(), list(tighter[a])
        while frontier:
            b = frontier.pop()
            if b not in seen:
                seen.add(b)
                frontier.extend(tighter[b])
        if not strict:
            seen = seen | {a}
        reach.append(seen)
    return reach


def op_parts(o, fix, notn, nops):
    """parts of operator o; hole = ('h', level), name = ('n', token)"""
    np = []
    for i, t in enumerate(notn):
        np.append(("n", t))
        if i + 1 < len(notn):
            np.append(("h", ("loosest",)))
    T, TE = ("tighter", o), ("tighterEq", o)
    if fix == "closed":  return np
    if fix == "prefx":   return np + [("h", T)]
    if fix == "infx":    return [("h", T)] + np + [("h", T)]
    if fix == "infxl":   return [("h", TE)] + np + [("h", T)]
    if fix == "infxr":   return [("h", T)] + np + [("h", TE)]
    if fix == "postfx":  return [("h", T)] + np
    if fix == "juxt":    return [("h", TE), ("h", T)]
    raise AssertionError


class Grammar:
    def __init__(self, ops, tighter, loosest, isvar):
        self.ops = ops                      # list of (fix, notation-token-list)
        self.n = len(ops)
        self.tighter = tighter
        self.loosest = loosest
        self.isvar = isvar
        self.strict = closure(tighter, self.n, True)
        self.refl = closure(tighter, self.n, False)
        self.parts = [op_parts(o, f, nt, self.n) for o, (f, nt) in enumerate(ops)]

    def nametoks(self, o):
        return self.ops[o][1]

    def headtok(self, o):
        nt = self.nametoks(o)
        return nt[0] if nt else None

    def cond(self, level, b):
        k = level[0]
        if k == "tighter":   return b in self.strict[level[1]]
        if k == "tighterEq": return b in self.refl[level[1]]
        if k == "loosest":   return any(b in self.refl[a] for a in self.loosest)
        raise AssertionError

    def levels(self):
        ls = [("loosest",)]
        for o in range(self.n):
            ls.append(("tighter", o))
            ls.append(("tighterEq", o))
        return ls

    # --- the three lexical conditions, exactly as forced in Entry ---
    def heads_distinct(self):
        seen = {}
        for o in range(self.n):
            h = self.headtok(o)
            if h is None:
                continue
            if h in seen:
                return False
            seen[h] = o
        return True

    def var_disjoint(self):
        return all(t not in self.isvar for o in range(self.n) for t in self.nametoks(o))

    def interior_terminates(self):
        heads = {self.headtok(o) for o in range(self.n)} - {None}
        for o in range(self.n):
            for t in self.nametoks(o)[1:]:          # tail = non-leading name tokens
                if t in heads:
                    return False
        return True

    def wellformed(self):
        return self.heads_distinct() and self.var_disjoint() and self.interior_terminates()


def ambiguous(g, maxlen=MAXLEN):
    """Enumerate all trees with flatten length <= maxlen at every level; find a collision."""
    # gen[level][n] = dict flatten -> set of trees (trees are hashable nested tuples)
    gen = {l: {} for l in g.levels()}

    def trees(level, n):
        d = gen[level].setdefault(n, None)
        if d is not None:
            return d
        d = {}
        gen[level][n] = d
        if n <= 0:
            return d
        if n == 1:
            for t in g.isvar:
                d.setdefault((t,), set()).add(("var", t))
        for o in range(g.n):
            if not g.cond(level, o):
                continue
            parts = g.parts[o]
            holes = [p for p in parts if p[0] == "h"]
            k = sum(1 for p in parts if p[0] == "n")
            rem = n - k
            if rem < len(holes) or (not holes and rem != 0):
                continue
            # compositions of `rem` into len(holes) positive parts
            comps = ([()] if not holes else
                     _compositions(rem, len(holes)))
            for comp in comps:
                subsets = []
                ok = True
                for (hp, sz) in zip(holes, comp):
                    sub = trees(hp[1], sz)
                    if not sub:
                        ok = False
                        break
                    subsets.append([(fl, tr) for fl, trs in sub.items() for tr in trs])
                if not ok:
                    continue
                for choice in itertools.product(*subsets):
                    fl, ci = [], 0
                    kids = []
                    for p in parts:
                        if p[0] == "n":
                            fl.append(p[1])
                        else:
                            fl.extend(choice[ci][0]); kids.append(choice[ci][1]); ci += 1
                    d.setdefault(tuple(fl), set()).add(("op", o, tuple(kids)))
        return d

    for level in g.levels():
        for n in range(1, maxlen + 1):
            for fl, trs in trees(level, n).items():
                if len(trs) > 1:
                    return (level, fl, sorted(trs, key=str)[:2])
    return None


@lru_cache(maxsize=None)
def _compositions(total, parts):
    if parts == 0:
        return [()] if total == 0 else []
    out = []
    for first in range(1, total - parts + 2):
        for rest in _compositions(total - first, parts - 1):
            out.append((first,) + rest)
    return out


def dags(n):
    """all DAGs on n nodes as tighter : op -> list op (edges only i -> j with rank i < rank j
       -- WLOG by relabelling, since tighter must be well-founded)"""
    edges = [(i, j) for i in range(n) for j in range(n) if i != j]
    # restrict to i<j to guarantee acyclicity; every DAG is isomorphic to one such
    edges = [(i, j) for (i, j) in edges if i < j]
    for mask in range(1 << len(edges)):
        t = [[] for _ in range(n)]
        for b, (i, j) in enumerate(edges):
            if mask >> b & 1:
                t[i].append(j)
        yield t


def search(nops, notn_lens, use_juxt, require_interior=True, maxlen=MAXLEN):
    found = []
    notns = []
    for L in notn_lens:
        notns.extend(itertools.product(NAMES, repeat=L))
    opspace = [(f, list(nt)) for f in FIX for nt in notns]
    total = 0
    for ops in itertools.combinations_with_replacement(opspace, nops):
        ops = list(ops)
        if use_juxt:
            ops = ops + [("juxt", [])]
        n = len(ops)
        for t in dags(n):
            for lmask in range(1, 1 << n):
                loosest = [i for i in range(n) if lmask >> i & 1]
                g = Grammar(ops, t, loosest, set(VARS))
                if not (g.heads_distinct() and g.var_disjoint()):
                    continue
                if require_interior and not g.interior_terminates():
                    continue
                total += 1
                r = ambiguous(g, maxlen)
                if r:
                    found.append((ops, t, loosest, r))
                    if len(found) >= 3:
                        return found, total
    return found, total


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "with"
    req = (mode == "with")
    for nops, lens, juxt in [(2, [1, 2], False), (2, [1, 2], True), (3, [1, 2], False)]:
        found, total = search(nops, lens, juxt, require_interior=req)
        tag = "WITH interiorTerminates" if req else "WITHOUT interiorTerminates"
        print(f"[{tag}] nops={nops} juxt={juxt}: {total} wellformed grammars, "
              f"{len(found)} ambiguous")
        for ops, t, loosest, (level, fl, trs) in found[:2]:
            print(f"    ops={ops} tighter={t} loosest={loosest}")
            print(f"    level={level} flatten={' '.join(fl)}")
            for tr in trs:
                print(f"      {tr}")
        sys.stdout.flush()


def random_search(iters=200000, seed=0, maxlen=8, require_interior=True):
    import random
    rnd = random.Random(seed)
    found, tested = [], 0
    for _ in range(iters):
        nops = rnd.randint(1, 4)
        ops = []
        for _ in range(nops):
            f = rnd.choice(FIX)
            L = rnd.randint(1, 3)
            ops.append((f, [rnd.choice(NAMES) for _ in range(L)]))
        if rnd.random() < 0.4:
            ops.append(("juxt", []))
        n = len(ops)
        perm = list(range(n))              # tighter must be well-founded: only i -> j, i<j
        t = [[j for j in range(i + 1, n) if rnd.random() < 0.45] for i in range(n)]
        loosest = [i for i in range(n) if rnd.random() < 0.5] or [rnd.randrange(n)]
        g = Grammar(ops, t, loosest, set(VARS))
        if not (g.heads_distinct() and g.var_disjoint()):
            continue
        if require_interior and not g.interior_terminates():
            continue
        tested += 1
        r = ambiguous(g, maxlen)
        if r:
            found.append((ops, t, loosest, r))
            if len(found) >= 3:
                break
    return found, tested
