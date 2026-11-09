#!/usr/bin/env python3
"""Generate raw VM bytecode fixtures independently of the Hol compiler."""

import sys
from pathlib import Path

class Builder:

    def __init__(self, q=1):
        self.q = q
        self.ts = []
        self.ins = []
        self.cs = []
        self.ns = 0

    def term(self, t):
        self.ts.append(t)
        return len(self.ts) - 1

    def v(self, i):
        return self.term((0, i, 0))

    def c(self, i):
        self.ns = max(self.ns, i + 1)
        return self.term((1, i, 0))

    def app(self, f, x):
        return self.term((2, f, x))

    def apps(self, f, *xs):
        for x in xs:
            f = self.app(f, x)
        return f

    def i(self, *v):
        self.ins.append(tuple(v) + (0,) * (4 - len(v)))
        return len(self.ins) - 1

    def code(self, entry):
        return [1213156401, 1, len(self.ts), len(self.ins), len(self.cs), self.q, entry, self.ns] + [x for t in self.ts + self.ins + self.cs for x in t]
tests = []

def add(name, b, entry, answers):
    tests.append((name, b.code(entry), answers))
b = Builder(0)
add('empty', b, b.i(0), [[]])
b = Builder(2)
add('initial_slots', b, b.i(0), [[0, 0, 0, 1]])
b = Builder()
x = b.v(0)
a = b.c(7)
ret = b.i(0)
add('simple_unify', b, b.i(3, x, a, ret), [[1, 7]])
b = Builder(2)
x = b.v(0)
y = b.v(1)
ret = b.i(0)
add('fresh_common_variable', b, b.i(3, x, y, ret), [[0, 2, 0, 2]])
b = Builder()
x = b.v(0)
a = b.c(0)
z = b.c(1)
ret = b.i(0)
left = b.i(3, x, a, ret)
right = b.i(3, x, z, ret)
add('choice_order', b, b.i(4, left, right), [[1, 0], [1, 1]])
b = Builder()
x = b.v(0)
a = b.c(0)
z = b.c(1)
ret = b.i(0)
no = b.i(1)
left = b.i(3, x, a, no)
right = b.i(3, x, z, ret)
add('undo_failed_branch', b, b.i(4, left, right), [[1, 1]])
b = Builder()
x = b.v(0)
f = b.c(0)
fx = b.app(f, x)
ret = b.i(0)
add('occurs_direct', b, b.i(3, x, fx, ret), [])
b = Builder(2)
x = b.v(0)
y = b.v(1)
f = b.c(0)
fx = b.app(f, x)
ret = b.i(0)
cycle = b.i(3, y, fx, ret)
add('occurs_indirect', b, b.i(3, x, y, cycle), [])
b = Builder()
x = b.v(0)
p = b.c(0)
a = b.c(1)
z = b.c(2)
ret = b.i(0)
b.cs = [(0, 0, b.app(p, a), ret), (0, 0, b.app(p, z), ret)]
add('clause_order', b, b.i(2, b.app(p, x), ret), [[1, 1], [1, 2]])
b = Builder()
x = b.v(0)
p = b.c(0)
q = b.c(1)
a = b.c(2)
z = b.c(3)
ret = b.i(0)
b.cs = [(0, 0, b.app(p, a), ret), (0, 0, b.app(p, z), ret), (1, 0, b.app(q, z), ret)]
tail = b.i(2, b.app(q, x), ret)
add('continuation_rollback', b, b.i(2, b.app(p, x), tail), [[1, 3]])
b = Builder()
x = b.v(0)
t = b.v(1)
h = b.v(1)
t2 = b.v(2)
mem = b.c(0)
cons = b.c(1)
nil = b.c(2)
a = b.c(3)
z = b.c(4)
ret = b.i(0)
first = b.apps(mem, x, b.apps(cons, x, t))
second = b.apps(mem, x, b.apps(cons, h, t2))
body = b.i(2, b.apps(mem, x, t2), ret)
b.cs = [(0, 2, first, ret), (0, 3, second, body)]
lst = b.apps(cons, a, b.apps(cons, z, b.apps(cons, a, nil)))
add('recursive_member', b, b.i(2, b.apps(mem, x, lst), ret), [[1, 3], [1, 4], [1, 3]])

# Clause matching must preserve repeated-variable constraints and materialize
# a structured head only when the goal supplies an unbound argument.
b = Builder()
x = b.v(0)
p = b.c(0)
red = b.c(1)
ret = b.i(0)
b.cs = [(0, 1, b.apps(p, x, x), ret)]
add('head_repeated_variable', b, b.i(2, b.apps(p, red, x), ret), [[1, 1]])
b = Builder()
x = b.v(0)
p = b.c(0)
f = b.c(1)
red = b.c(2)
blue = b.c(3)
ret = b.i(0)
b.cs = [(0, 1, b.apps(p, b.app(f, x), x), ret), (0, 0, b.apps(p, red, blue), ret)]
add('head_structure_retry', b, b.i(2, b.apps(p, x, blue), ret), [[2, 1, 1, 1, 3], [1, 2]])
b = Builder()
x = b.v(0)
p = b.c(0)
f = b.c(1)
ret = b.i(0)
b.cs = [(0, 1, b.apps(p, x, b.app(f, x)), ret)]
add('head_indirect_cycle', b, b.i(2, b.apps(p, b.app(f, x), x), ret), [])
b = Builder(0)
x = b.v(0)
p = b.c(0)
f = b.c(1)
red = b.c(2)
ret = b.i(0)
b.cs = [(0, 0, b.app(p, red), ret), (0, 1, b.app(p, b.app(f, x)), ret)]
add('head_constant_conflict', b, b.i(2, b.app(p, b.app(f, red)), ret), [[]])
b = Builder(0)
x = b.v(0)
p = b.c(0)
red = b.c(1)
ret = b.i(0)
head = p
goal = p
for _ in range(1000):
    head = b.app(head, x)
    goal = b.app(goal, red)
b.cs = [(0, 1, head, ret)]
add('clause_application_spine', b, b.i(2, goal, ret), [[]])

# Protect initial answer slots while internal aliases share a representative.
b = Builder()
x = b.v(0)
p = b.c(0)
ret = b.i(0)
b.cs = [(0, 1, b.app(p, x), ret)]
add('head_fresh_query_representative', b, b.i(2, b.app(p, x), ret), [[0, 4]])
b = Builder(2)
x = b.v(0)
y = b.v(1)
p = b.c(0)
red = b.c(1)
blue = b.c(2)
ret = b.i(0)
shared = b.i(3, x, y, ret)
separate = b.i(3, x, red, b.i(3, y, blue, ret))
b.cs = [(0, 2, b.apps(p, x, y), b.i(4, shared, separate))]
add('internal_alias_rollback', b, b.i(2, b.apps(p, x, y), ret), [[0, 9, 0, 9], [1, 1, 1, 2]])
b = Builder(2)
x = b.v(0)
y = b.v(1)
p = b.c(0)
f = b.c(1)
ret = b.i(0)
cyclic = b.i(3, y, b.app(f, x), ret)
b.cs = [(0, 2, b.apps(p, x, y), b.i(3, x, y, cyclic))]
add('internal_alias_occurs_check', b, b.i(2, b.apps(p, x, y), ret), [])

# A body-only variable must survive restoring a choice made before its first use.
b = Builder()
x = b.v(0)
y = b.v(1)
p = b.c(0)
f = b.c(1)
red = b.c(2)
blue = b.c(3)
ret = b.i(0)
share = b.i(3, x, y, ret)
left = b.i(3, y, b.app(f, red), share)
right = b.i(3, y, blue, share)
b.cs = [(0, 2, b.app(p, x), b.i(4, left, right))]
add('body_only_choice_rollback', b, b.i(2, b.app(p, x), ret), [[2, 1, 1, 1, 2], [1, 3]])

# Constructing an unbound argument can encounter a slot before direct matching does.
b = Builder(2)
x = b.v(0)
y = b.v(1)
p = b.c(0)
f = b.c(1)
red = b.c(2)
blue = b.c(3)
ret = b.i(0)
b.cs = [(0, 1, b.apps(p, b.app(f, x), x), ret), (0, 0, b.apps(p, red, blue), ret)]
add('head_subtree_shared_variable', b, b.i(2, b.apps(p, x, y), ret), [[2, 1, 1, 0, 10, 0, 10], [1, 2, 1, 3]])

# A captured compound is reused by repeated head variables, including its aliases.
b = Builder(2)
x = b.v(0)
y = b.v(1)
p = b.c(0)
f = b.c(1)
ret = b.i(0)
b.cs = [(0, 1, b.apps(p, x, x), ret)]
add('head_captured_structure_alias', b, b.i(2, b.apps(p, b.app(f, x), b.app(f, y)), ret), [[0, 10, 0, 10]])

b = Builder()
x = b.v(0)
a = b.c(0)
z = b.c(1)
ret = b.i(0)
cut = b.i(5, ret)
left = b.i(3, x, a, cut)
right = b.i(3, x, z, ret)
add('query_cut', b, b.i(4, left, right), [[1, 0]])
for kind in ['caller_cut', 'callee_cut', 'cut_then_fail']:
    b = Builder()
    x = b.v(0)
    p = b.c(0)
    q = b.c(1)
    a = b.c(2)
    z = b.c(3)
    c = b.c(4)
    d = b.c(5)
    ret = b.i(0)
    no = b.i(1)
    cut = b.i(5, no if kind == 'cut_then_fail' else ret)
    pbody = b.i(2, b.app(q, x), ret if kind == 'callee_cut' else cut)
    b.cs = [(0, 1, b.app(p, x), pbody), (0, 0, b.app(p, z), ret), (1, 0, b.app(q, a), cut if kind == 'callee_cut' else ret), (1, 0, b.app(q, c), ret)]
    query = b.i(2, b.app(p, x), ret)
    if kind != 'callee_cut':
        query = b.i(4, query, b.i(3, x, d, ret))
    answers = {'caller_cut': [[1, 2], [1, 5]], 'callee_cut': [[1, 2], [1, 3]], 'cut_then_fail': [[1, 5]]}[kind]
    add(kind, b, query, answers)
b = Builder()
x = b.v(0)
f = b.c(0)
t = b.c(1)
ret = b.i(0)
expected = [1, 1]
for _ in range(2000):
    t = b.app(f, t)
    expected = [2, 1, 0] + expected
add('deep_term', b, b.i(3, x, t, ret), [expected])

# Cross the native instruction budget while retaining a clause alternative,
# variable binding, and return continuation.
b = Builder()
x = b.v(0)
p = b.c(0)
a = b.c(1)
z = b.c(2)
ret = b.i(0)
body = b.i(3, x, a, ret)
for _ in range(32770):
    body = b.i(3, x, x, body)
b.cs = [(0, 1, b.app(p, x), body), (0, 0, b.app(p, z), ret)]
add("yield_continuation", b, b.i(2, b.app(p, x), ret), [[1, 1], [1, 2]])


def array(name, values, kind="int64_t"):
    values = values or [0]
    rows = [", ".join(map(str, values[start:start + 24])) for start in range(0, len(values), 24)]
    return f"static const {kind} {name}[] = {{\n    " + ",\n    ".join(rows) + "\n};\n"


output = ["/* Generated bytecode data for machine_test.c; do not edit. */\n"]
for index, (name, code, answers) in enumerate(tests):
    output.append(array(f"code{index}", code))
    output.append(array(f"answer{index}", [word for answer in answers for word in answer]))
    output.append(array(f"size{index}", list(map(len, answers)), "size_t"))
output.append("static const TestCase cases[] = {\n")
for index, (name, code, answers) in enumerate(tests):
    output.append(f'    {{ "{name}", code{index}, {len(code)}, answer{index}, size{index}, {len(answers)} }},\n')
output.append("};\n")
Path(sys.argv[1]).write_text("".join(output))
