#!/usr/bin/env python3
"""Untrusted proof search over an immutable actual-Core snapshot.

No theorem trusts this program. It emits rule DATA, never Lean source or an
assumed typing theorem. The separately compiled Lean checker validates every
step. All roots refer to the original complete graph, including inert sort
nodes. Missing intermediate expressions, unsupported typing/conversion and
resource exhaustion fail closed; this is intentionally not a complete kernel.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys

NODE_FIELDS = {0: 1, 1: 1, 2: 2, 3: 0, 4: 0, 5: 1, 6: 2, 7: 2,
               8: 3, 9: 3, 10: 2, 12: 3, 13: 1, 14: 1, 15: 2,
               16: 2, 17: 3, 18: 0, 19: 1}
CHILD_START = {5: 1, 6: 1, 7: 1, 8: 2, 9: 2, 10: 1, 12: 1,
               13: 1, 14: 1, 15: 1, 16: 1, 17: 1}
CONGRUENCE = {5: 35, 6: 36, 7: 37, 8: 38, 9: 39, 10: 40, 11: 41,
              12: 42, 13: 43, 14: 44, 15: 45, 16: 46, 17: 47}


class Unsupported(ValueError):
    """A certificate cannot be produced within this restricted fragment."""


def require(condition, message):
    if not condition:
        raise Unsupported(message)


def encode_numbers(values):
    return ''.join((bin(n)[2:][::-1] if n else '') + ';' for n in values).encode()


class Reader:
    def __init__(self, data):
        require(len(data) <= 8 * 1024 * 1024, 'input exceeds 8 MiB')
        require(data.endswith(b';') and set(data) <= set(b'01;'), 'invalid canonical bytes')
        parts = data[:-1].split(b';')
        require(all(len(p) <= 64 and (not p or p[-1] == 49) for p in parts),
                'noncanonical or excessive natural')
        self.tokens = [int(p[::-1], 2) if p else 0 for p in parts]
        self.position = 0

    def number(self):
        require(self.position < len(self.tokens), 'truncated input')
        n = self.tokens[self.position]
        self.position += 1
        return n

    def vector(self, limit=4096):
        n = self.number()
        require(n <= limit, 'vector limit')
        return [self.number() for _ in range(n)]

    def graph(self):
        count = self.number()
        require(count <= 4096, 'graph node limit')
        nodes = []
        for index in range(count):
            tag = self.number()
            if tag == 11:
                fields = self.vector()
                node = (tag, *fields)
                children = fields
            else:
                require(tag in NODE_FIELDS, 'unsupported graph constructor')
                node = (tag, *(self.number() for _ in range(NODE_FIELDS[tag])))
                children = node[CHILD_START[tag]:] if tag in CHILD_START else []
            require(all(k < index for k in children), 'graph child not backwards')
            if tag == 0:
                require(node[1] < 2**32, 'variable range')
            if tag == 2:
                require(node[1] in (0, 1) and node[2] < 2**63 + node[1] and
                        not (node[1] == 1 and node[2] == 0), 'signed literal range')
            if tag in (8, 9):
                require(node[1] in (0, 1), 'binder flag')
            nodes.append(node)
        return nodes

    def end(self):
        require(self.position == len(self.tokens), 'trailing input')


def graph_tokens(graph):
    yield len(graph)
    for node in graph:
        if node[0] == 11:
            yield 11
            yield len(node) - 1
            yield from node[1:]
        else:
            yield from node


@dataclass
class Snapshot:
    term: int
    type: int
    graph: list
    graph_bytes: bytes

    @classmethod
    def read(cls, retained):
        r = Reader(retained)
        require(r.number() == 3, 'unsupported snapshot schema')
        term, ty = r.number(), r.number()
        start = r.position
        graph = r.graph()
        r.end()
        require(term < len(graph) and ty < len(graph), 'snapshot root outside graph')
        graph_bytes = encode_numbers(r.tokens[start:])
        require(retained == encode_numbers([3, term, ty]) + graph_bytes,
                'snapshot byte identity mismatch')
        return cls(term, ty, graph, graph_bytes)


def children(t):
    if t[0] == 11:
        return t[1:]
    return t[CHILD_START[t[0]]:] if t[0] in CHILD_START else ()


def rebuild(t, xs):
    if t[0] == 11:
        return (11, *xs)
    return (*t[:CHILD_START[t[0]]], *xs) if t[0] in CHILD_START else t


def shift(t, amount, cutoff=0):
    if t[0] == 0:
        return (0, t[1] + amount) if t[1] >= cutoff else t
    if t[0] in (8, 9):
        return (t[0], t[1], shift(t[2], amount, cutoff), shift(t[3], amount, cutoff + 1))
    return rebuild(t, [shift(x, amount, cutoff) for x in children(t)])


def tree_stats(t):
    count, maximum, pending = 0, 0, [(t, 1)]
    while pending:
        node, depth = pending.pop()
        count += 1
        maximum = max(maximum, depth)
        require(count <= 200000 and maximum <= 128, 'tree expansion/depth limit')
        pending.extend((child, depth + 1) for child in children(node))
    return count, maximum


def substitute(t, value, depth=0, _checked=False):
    if not _checked:
        size, nesting = tree_stats(t)
        other, other_depth = tree_stats(value)
        require(size * other <= 200000 and nesting + other_depth <= 128,
                'substitution expansion/depth limit')
    if t[0] == 0:
        if t[1] == depth:
            return shift(value, depth)
        return (0, t[1] - 1) if t[1] > depth else t
    if t[0] in (8, 9):
        return (t[0], t[1], substitute(t[2], value, depth, True),
                substitute(t[3], value, depth + 1, True))
    return rebuild(t, [substitute(x, value, depth, True) for x in children(t)])


def proposition(t):
    return t[0] in (6, 7) or (t[0] == 8 and proposition(t[3]))


def reduce_head(t):
    if t[0] == 10 and t[1][0] == 9:
        return substitute(t[1][3], t[2]), 33
    if t[0] == 16 and t[1][0] == t[2][0] == 1 and t[1][1] + t[2][1] < 2**64:
        return (1, t[1][1] + t[2][1]), 34
    return t, None


def normalize(t, fuel=128, work=None):
    if work is None:
        work = [200000]
    work[0] -= 1
    require(work[0] >= 0, 'normalization work limit')
    require(fuel > 0, 'conversion depth exhausted')
    rebuilt = rebuild(t, [normalize(c, fuel - 1, work) for c in children(t)])
    reduced, rule = reduce_head(rebuilt)
    return normalize(reduced, fuel - 1, work) if rule is not None else rebuilt


class Producer:
    def __init__(self, snapshot):
        self.snapshot = snapshot
        self.raw = []
        self.roots = {}
        self.steps = []
        self.memo = {}
        sizes, depths, total = [], [], 0
        for i, node in enumerate(snapshot.graph):
            ids = node[1:] if node[0] == 11 else (
                node[CHILD_START[node[0]]:] if node[0] in CHILD_START else ())
            size, depth = 1 + sum(sizes[k] for k in ids), 1 + max((depths[k] for k in ids), default=0)
            require(size <= 200000 and depth <= 128, 'decoded graph expansion/depth limit')
            total += size
            require(total <= 2000000, 'aggregate graph expansion limit')
            sizes.append(size)
            depths.append(depth)
            if node[0] in (18, 19) or any(self.raw[k] is None for k in ids):
                t = None
            elif node[0] == 2:
                t = (2, -node[2] if node[1] else node[2])
            else:
                t = rebuild(node, [self.raw[k] for k in ids])
            self.raw.append(t)
            if t is not None:
                self.roots.setdefault(t, i)

    def term(self, root):
        require(root < len(self.raw) and self.raw[root] is not None, 'root reaches an inert sort')
        return self.raw[root]

    def root(self, term):
        require(term in self.roots, f'intermediate term absent from actual graph: {term}')
        return self.roots[term]

    def emit(self, rule, context, subject, target, premises=()):
        key = (rule, tuple(context), subject, target, tuple(premises))
        if key in self.memo:
            return self.memo[key]
        require(len(self.steps) < 4096 and len(context) <= 128, 'proof search limit')
        index = len(self.steps)
        self.steps.append(dict(rule=rule, context=list(context), subject=subject,
                               target=target, premises=list(premises)))
        self.memo[key] = index
        return index

    def form(self, root, ctx=()):
        t = self.term(root)
        tag = t[0]
        if tag in (3, 4):
            rule, premises = tag - 3, []
        elif tag in (5, 6, 7):
            rule = tag - 3
            premises = [self.typed(self.root(x), self.root((3,)), ctx) for x in children(t)]
        elif tag == 8:
            require(t[1] == proposition(t[2]), 'binder mode outside the typed fragment')
            domain, body = self.root(t[2]), self.root(t[3])
            rule, premises = 5, [self.form(domain, ctx), self.form(body, (domain, *ctx))]
        else:
            raise Unsupported('type formation outside the typed fragment')
        return self.emit(rule, ctx, root, root, premises)

    def typed(self, root, target, ctx=()):
        step = self.infer(root, ctx)
        actual = self.steps[step]['target']
        if self.term(actual) == self.term(target):
            return step
        conversion = self.convert(actual, target)
        return self.emit(21, ctx, root, target, [step, conversion])

    def infer(self, root, ctx=()):
        t = self.term(root)
        tag = t[0]
        get = self.root
        sub = lambda x: self.infer(get(x), ctx)
        as_u64 = lambda x: self.typed(get(x), get((3,)), ctx)
        premises = []
        if tag == 0:
            require(t[1] < len(ctx), 'unbound variable')
            ty, rule = shift(self.term(ctx[t[1]]), t[1] + 1), 10
        elif tag in (1, 2):
            ty, rule = (3 if tag == 1 else 4,), 10 + tag
        elif tag == 16:
            ty, rule, premises = (3,), 13, [as_u64(t[1]), as_u64(t[2])]
        elif tag == 17:
            pty = (6, t[2], (16, t[1], (1, 1)))
            ty, rule = (3,), 14
            premises = [as_u64(t[1]), as_u64(t[2]), self.typed(get(t[3]), get(pty), ctx)]
        elif tag == 11:
            ty, rule = (5, (1, len(t) - 1)), 15
            premises = [self.typed(get(x), get((4,)), ctx) for x in t[1:]]
        elif tag == 15:
            require(t[1][0] == t[2][0] == 1 and t[1][1] < t[2][1],
                    'decide requires literal true endpoints in the typed fragment')
            ty, rule = (6, t[1], t[2]), 16
        elif tag == 13:
            ty, rule, premises = (7, t[1], t[1]), 17, [as_u64(t[1])]
        elif tag == 12:
            array_step = sub(t[1])
            aty = self.term(self.steps[array_step]['target'])
            require(aty[0] == 5, 'index requires an array')
            ty, rule = (4,), 18
            premises = [array_step, as_u64(t[2]), self.typed(get(t[3]), get((6, t[2], aty[1])), ctx)]
        elif tag == 9:
            require(t[1] == proposition(t[2]), 'binder mode outside the typed fragment')
            domain = get(t[2])
            formation = self.form(domain, ctx)
            body = self.infer(get(t[3]), (domain, *ctx))
            ty, rule = (8, t[1], t[2], self.term(self.steps[body]['target'])), 19
            premises = [formation, body]
        elif tag == 10:
            function = sub(t[1])
            fty = self.term(self.steps[function]['target'])
            if fty[0] != 8:
                normal = normalize(fty)
                require(normal[0] == 8, 'application needs a Pi')
                function = self.typed(get(t[1]), get(normal), ctx)
                fty = normal
            argument = self.typed(get(t[2]), get(fty[2]), ctx)
            ty, rule = substitute(fty[3], t[2]), 20
            premises = [function, argument]
        else:
            raise Unsupported(f'no typing rule for graph tag {tag}')
        return self.emit(rule, ctx, root, get(ty), premises)

    def convert(self, source, target, fuel=128):
        require(fuel > 0, 'conversion proof search exhausted')
        a, b = self.term(source), self.term(target)
        if a == b:
            return self.emit(30, (), source, target)
        ar, rule = reduce_head(a)
        if rule is not None:
            middle = self.root(ar)
            first = self.emit(rule, (), source, middle)
            if ar == b:
                return first
            last = self.convert(middle, target, fuel - 1)
            return self.emit(32, (), source, target, [first, last])
        br, rule = reduce_head(b)
        if rule is not None:
            reverse = self.convert(target, source, fuel - 1)
            return self.emit(31, (), source, target, [reverse])
        if a[0] == b[0] and a[0] in CONGRUENCE and len(a) == len(b):
            if a[0] in (8, 9):
                require(a[1] == b[1], 'conversion cannot change binder mode')
            premises = [self.convert(self.root(x), self.root(y), fuel - 1)
                        for x, y in zip(children(a), children(b))]
            return self.emit(CONGRUENCE[a[0]], (), source, target, premises)
        na, nb = normalize(a), normalize(b)
        require(na == nb and na != a and nb != b, 'unsupported conversion')
        middle = self.root(na)
        first = self.convert(source, middle, fuel - 1)
        back = self.convert(target, middle, fuel - 1)
        last = self.emit(31, (), middle, target, [back])
        return self.emit(32, (), source, target, [first, last])

    def produce(self):
        s = self.snapshot
        typing = self.typed(s.term, s.type)
        formation = self.form(s.type)
        return dict(graph=s.graph, termRoot=s.term, typeRoot=s.type,
                    typingStep=typing, formationStep=formation, steps=self.steps)


def encode_certificate(certificate):
    c = certificate
    numbers = [2, c['termRoot'], c['typeRoot'], c['typingStep'], c['formationStep'],
               *graph_tokens(c['graph']), len(c['steps'])]
    for s in c['steps']:
        numbers += [s['rule'], len(s['context']), *s['context'], s['subject'],
                    s['target'], len(s['premises']), *s['premises']]
    require(all(isinstance(x, int) and 0 <= x < 2**64 for x in numbers), 'certificate number range')
    return encode_numbers(numbers)


def inspect_certificate(retained):
    """Unproved adapter used only for exact-root/full-graph association tests."""
    r = Reader(retained)
    require(r.number() == 2, 'unsupported certificate schema')
    term, ty, typing, formation = [r.number() for _ in range(4)]
    graph = r.graph()
    count = r.number()
    require(count <= 4096, 'derivation step limit')
    steps = []
    for _ in range(count):
        steps.append(dict(rule=r.number(), context=r.vector(128), subject=r.number(),
                          target=r.number(), premises=r.vector()))
    r.end()
    return dict(graph=graph, termRoot=term, typeRoot=ty,
                typingStep=typing, formationStep=formation, steps=steps)


def produce(retained):
    snapshot = Snapshot.read(retained)
    certificate = Producer(snapshot).produce()
    payload = encode_certificate(certificate)
    # Equality of exact canonical graph bytes and both root IDs, not a hash,
    # binds this untrusted certificate to the once-retained exported snapshot.
    decoded = inspect_certificate(payload)
    require(encode_numbers(graph_tokens(decoded['graph'])) == snapshot.graph_bytes and
            (decoded['termRoot'], decoded['typeRoot']) == (snapshot.term, snapshot.type),
            'certificate changed the actual graph or selected roots')
    return payload


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('snapshot', nargs='?', type=Path)
    args = parser.parse_args()
    if args.snapshot:
        with args.snapshot.open('rb') as stream:
            retained = stream.read(8 * 1024 * 1024 + 1)
    else:
        retained = sys.stdin.buffer.read(8 * 1024 * 1024 + 1)
    try:
        payload = produce(retained)
    except (Unsupported, RecursionError) as error:
        print(f'typing producer rejected: {error}', file=sys.stderr)
        return 1
    sys.stdout.buffer.write(payload)
    return 0


if __name__ == '__main__':
    sys.exit(main())
