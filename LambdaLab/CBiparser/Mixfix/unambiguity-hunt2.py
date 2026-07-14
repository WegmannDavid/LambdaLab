"""Two-entry hunt: is `interiorTerminates` (constraining the seam token only w.r.t. the HOLE's
entry) enough, or must the seam token also head no operator of the HOST entry?

Same Tree.lean semantics as hunt.py, but a grammar has 2 entries and a notation's interior hole
carries an entry index.
"""
import itertools, random, sys
from hunt import closure, _compositions

NAMES = ["A", "B", "C"]
VARS  = ["x"]
FIX   = ["closed", "prefx", "infx", "infxl", "infxr", "postfx"]


class Ent:
    def __init__(self, ops, tighter, loosest, isvar):
        self.ops, self.tighter, self.loosest, self.isvar = ops, tighter, loosest, isvar
        self.n = len(ops)
        self.strict = closure(tighter, self.n, True)
        self.refl = closure(tighter, self.n, False)

    def nametoks(self, o):  # ops entries are (fix, [(tok, holeEnt|None)...]) -> token list
        return [t for (t, _) in self.ops[o][1]]

    def headtok(self, o):
        nt = self.nametoks(o)
        return nt[0] if nt else None

    def seams(self, o):
        """(holeEntry, followingToken) for each interior hole, per Notation.holeFollowers"""
        notn = self.ops[o][1]
        return [(notn[i][1], notn[i + 1][0]) for i in range(len(notn) - 1)]


class G2:
    def __init__(self, entries):
        self.E = entries

    def parts(self, ei, o):
        E = self.E[ei]
        fix, notn = E.ops[o]
        np = []
        for i, (t, he) in enumerate(notn):
            np.append(("n", t))
            if i + 1 < len(notn):
                np.append(("h", he, ("loosest",)))     # interior hole: entry `he`, loosest
        T, TE = ("tighter", o), ("tighterEq", o)
        if fix == "closed":  return np
        if fix == "prefx":   return np + [("h", ei, T)]
        if fix == "infx":    return [("h", ei, T)] + np + [("h", ei, T)]
        if fix == "infxl":   return [("h", ei, TE)] + np + [("h", ei, T)]
        if fix == "infxr":   return [("h", ei, T)] + np + [("h", ei, TE)]
        if fix == "postfx":  return [("h", ei, T)] + np
        if fix == "juxt":    return [("h", ei, TE), ("h", ei, T)]

    def cond(self, ei, level, b):
        E = self.E[ei]
        k = level[0]
        if k == "tighter":   return b in E.strict[level[1]]
        if k == "tighterEq": return b in E.refl[level[1]]
        if k == "loosest":   return any(b in E.refl[a] for a in E.loosest)

    def levels(self, ei):
        E = self.E[ei]
        return [("loosest",)] + [(k, o) for o in range(E.n) for k in ("tighter", "tighterEq")]

    def heads_distinct(self):
        for E in self.E:
            seen = set()
            for o in range(E.n):
                h = E.headtok(o)
                if h is None: continue
                if h in seen: return False
                seen.add(h)
        return True

    def var_disjoint(self):
        return all(t not in E.isvar for E in self.E for o in range(E.n) for t in E.nametoks(o))

    def interior_terminates(self, host_too=False):
        """the SHIPPED condition: seam token heads no op of the HOLE's entry, and is not a
           variable there. `host_too` additionally forbids it heading an op of the HOST entry."""
        for ei, E in enumerate(self.E):
            for o in range(E.n):
                for (he, t) in E.seams(o):
                    H = self.E[he]
                    if t in H.isvar: return False
                    if any(H.headtok(oo) == t for oo in range(H.n)): return False
                    if host_too and any(E.headtok(oo) == t for oo in range(E.n)): return False
        return True


def ambiguous(g, maxlen=7):
    gen = {(ei, l): {} for ei in range(len(g.E)) for l in g.levels(ei)}

    def trees(ei, level, n):
        d = gen[(ei, level)].setdefault(n, None)
        if d is not None: return d
        d = {}; gen[(ei, level)][n] = d
        if n <= 0: return d
        E = g.E[ei]
        if n == 1:
            for t in E.isvar:
                d.setdefault((t,), set()).add(("var", t))
        for o in range(E.n):
            if not g.cond(ei, level, o): continue
            parts = g.parts(ei, o)
            holes = [p for p in parts if p[0] == "h"]
            k = sum(1 for p in parts if p[0] == "n")
            rem = n - k
            if rem < len(holes) or (not holes and rem != 0): continue
            for comp in ([()] if not holes else _compositions(rem, len(holes))):
                subsets, ok = [], True
                for (hp, sz) in zip(holes, comp):
                    sub = trees(hp[1], hp[2], sz)
                    if not sub: ok = False; break
                    subsets.append([(fl, tr) for fl, trs in sub.items() for tr in trs])
                if not ok: continue
                for choice in itertools.product(*subsets):
                    fl, ci, kids = [], 0, []
                    for p in parts:
                        if p[0] == "n": fl.append(p[1])
                        else:
                            fl.extend(choice[ci][0]); kids.append(choice[ci][1]); ci += 1
                    d.setdefault(tuple(fl), set()).add(("op", ei, o, tuple(kids)))
        return d

    for ei in range(len(g.E)):
        for level in g.levels(ei):
            for n in range(1, maxlen + 1):
                for fl, trs in trees(ei, level, n).items():
                    if len(trs) > 1:
                        return (ei, level, fl, sorted(trs, key=str)[:2])
    return None


def search(iters, seed, host_too, maxlen=7):
    rnd = random.Random(seed)
    found, tested = [], 0
    for _ in range(iters):
        entries = []
        for ei in range(2):
            nops = rnd.randint(1, 3)
            ops = []
            for _ in range(nops):
                f = rnd.choice(FIX)
                L = rnd.randint(1, 3)
                notn = [(rnd.choice(NAMES), rnd.randrange(2)) for _ in range(L)]
                ops.append((f, notn))
            if rnd.random() < 0.35:
                ops.append(("juxt", []))
            n = len(ops)
            t = [[j for j in range(i + 1, n) if rnd.random() < 0.45] for i in range(n)]
            loosest = [i for i in range(n) if rnd.random() < 0.5] or [rnd.randrange(n)]
            entries.append(Ent(ops, t, loosest, set(VARS)))
        g = G2(entries)
        if not (g.heads_distinct() and g.var_disjoint()): continue
        if not g.interior_terminates(host_too=host_too): continue
        tested += 1
        r = ambiguous(g, maxlen)
        if r:
            found.append((g, r))
            if len(found) >= 2: break
    return found, tested


if __name__ == "__main__":
    for host_too in (False, True):
        f, n = search(60000, 11, host_too)
        tag = "SHIPPED condition" if not host_too else "STRENGTHENED (host entry too)"
        print(f"[{tag}] {n} wellformed 2-entry grammars, {len(f)} ambiguous")
        for g, (ei, level, fl, trs) in f[:1]:
            for i, E in enumerate(g.E):
                print(f"    entry{i}: ops={E.ops} tighter={E.tighter} loosest={E.loosest}")
            print(f"    entry={ei} level={level} flatten={' '.join(fl)}")
            for tr in trs: print(f"      {tr}")
        sys.stdout.flush()
