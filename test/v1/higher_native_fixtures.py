#!/usr/bin/env python3
"""Independent wordcode fixtures for the higher-order C executor."""
import sys
from itertools import chain
from pathlib import Path


def flat(rows):
    return list(chain.from_iterable(rows))


class Builder:
    def __init__(self, slots=0):
        self.slots = slots
        self.symbols = {}
        self.roles = []
        self.terms = []
        self.facts = []
        self.digits = []
        for name, role in [('true', 3), ('s', 21), ('pi', 9), ('sigma', 10),
                ('typi', 1), ('if', 2), ('and', 6), ('or', 7), ('imply', 8),
                ('cut', 5), ('fail', 4), ('eq', 13), ('debug', 11)]:
            self.symbol(name, role)
        self.builtins = len(self.roles)
        self.fact('eq', self.call('typi', self.lam(self.pi(
            self.call('eq', self.idx(1), self.idx(0), self.idx(0))))))

    def symbol(self, name, role=0):
        if name not in self.symbols:
            self.symbols[name] = len(self.roles)
            self.roles.append(role)
        return self.symbols[name]

    def term(self, tag, a=0, b=0):
        index = len(self.terms)
        self.terms.append([tag, a, b, 0, 0, -1])
        return index

    def const(self, name):
        return self.term(1, self.symbol(name))

    def var(self, slot=0):
        return self.term(0, slot)

    def idx(self, index):
        return self.term(3, index)

    def lam(self, body):
        return self.term(4, body)

    def app(self, function, argument):
        return self.term(2, function, argument)

    def call(self, name, *args):
        result = self.const(name)
        for arg in args:
            result = self.app(result, arg)
        return result

    def pi(self, body):
        return self.call('pi', self.lam(body))

    def sigma(self, body):
        return self.call('sigma', self.lam(body))

    def eq(self, left, right):
        return self.call('eq', self.const('t'), left, right)

    def nat(self, digits):
        offset = len(self.digits)
        self.digits.extend(map(ord, str(digits)))
        return self.term(5, offset, len(str(digits)))

    def fact(self, name, root):
        self.facts.append([self.symbol(name), root])

    def code(self, query):
        header = [0x484f4c31, 2, len(self.terms), len(self.roles), len(self.facts), self.slots, query, 0]
        return (header + [0, -1] * self.slots + self.roles
                + flat(self.terms) + flat(self.facts) + self.digits)

    def answer(self, name):
        return [1, 1, self.symbol(name), -1]

    def below(self, roots):
        reached, stack = set(), list(roots)
        while stack:
            index = stack.pop()
            if index in reached:
                continue
            reached.add(index)
            tag, a, b = self.terms[index][:3]
            stack.extend([a, b] if tag == 2 else [a] if tag == 4 else [])
        return sorted(reached)

    def fragment(self, known, slots, facts, query):
        """The templates below the given roots as wordcode of their own."""
        order = self.below([root for _, root in facts] + ([] if query is None else [query]))
        new = {old: index for index, old in enumerate(order)}
        rows, digits, total = [], [], known
        for old in order:
            tag, a, b, _, _, meta = self.terms[old]
            if tag == 2:
                rows.append([2, new[a], new[b], 0, 0, meta])
            elif tag == 4:
                rows.append([4, new[a], 0, 0, 0, meta])
            elif tag == 5:
                rows.append([5, len(digits), b, 0, 0, meta])
                digits.extend(self.digits[a:a + b])
            else:
                rows.append(self.terms[old])
                if tag == 1:
                    total = max(total, a + 1)
        total = max([total] + [symbol + 1 for symbol, _ in facts])
        if query is not None:
            total = len(self.roles)
        header = [0x484f4c31, 2, len(rows), total, len(facts), slots, -1 if query is None else new[query], 0]
        clauses = flat([symbol, new[root]] for symbol, root in facts)
        return total, header + [0, -1] * slots + self.roles[known:total] + flat(rows) + clauses + digits

    def fragments(self, query):
        """A seed with the built-in symbols, the clauses in two additions, and
        the query. None when a clause mentions a query variable."""
        if any(self.terms[index][0] == 0 for index in self.below([root for _, root in self.facts])):
            return None
        seed = [0x484f4c31, 2, 1, self.builtins, 0, 0, 0, 0] + self.roles[:self.builtins] + [1, self.symbols['true'], 0, 0, 0, -1]
        half = len(self.facts) // 2
        known, first = self.fragment(self.builtins, 0, self.facts[:half], None)
        known, second = self.fragment(known, 0, self.facts[half:], None)
        return [seed, first, second, self.fragment(known, self.slots, [], query)[1]]


cases = []


def add(name, b, query, expected):
    cases.append((name, b.code(query), expected, b.fragments(query)))


b = Builder()
add('beta_dynamic_goal', b, b.app(b.lam(b.const('true')), b.const('a')), [[0]])
b = Builder()
b.fact('p', b.const('p'))
p = b.idx(0)
add('sigma_dynamic_call', b, b.sigma(b.call('and', b.eq(p, b.const('p')), p)), [[0]])
b = Builder()
px = b.call('p', b.idx(0))
add('pi_local_nominal', b, b.pi(b.call('imply', px, px)), [[0]])
b = Builder(1)
add('pi_scope_escape', b, b.pi(b.eq(b.var(), b.idx(0))), [])
b = Builder(1)
add('higher_pattern_identity', b, b.pi(b.eq(b.app(b.var(), b.idx(0)), b.idx(0))), [[1, 4, -1, 3, 0]])
b = Builder()
px = b.call('p', b.idx(0))
inner = b.pi(b.call('imply', px, px))
add('implication_lexical_scope', b, b.call('and', inner, b.call('p', b.const('a'))), [])
b = Builder(1)
b.fact('p', b.call('p', b.const('a')))
query = b.call('imply', b.call('p', b.const('b')), b.call('p', b.var()))
add('program_before_local', b, query, [b.answer('a'), b.answer('b')])
b = Builder(1)
locals_ = b.call('and', b.call('p', b.const('a')), b.call('p', b.const('b')))
add('local_source_order', b, b.call('imply', locals_, b.call('p', b.var())), [b.answer('a'), b.answer('b')])
b = Builder()
eq = b.eq(b.const('a'), b.const('b'))
add('local_equality_precedence', b, b.call('imply', eq, eq), [[0]])
b = Builder()
eq = b.eq(b.const('a'), b.const('a'))
add('failed_local_equality_no_fallback', b, b.call('imply', b.call('if', eq, b.const('fail')), eq), [])
b = Builder(1)
for name in ['a', 'b']:
    b.fact('q', b.call('q', b.const(name)))
b.fact('p', b.pi(b.call('if', b.call('p', b.idx(0)), b.call('and', b.call('q', b.idx(0)), b.const('cut')))))
add('predicate_cut', b, b.call('p', b.var()), [b.answer('a')])
b = Builder(1)
b.fact('inner', b.call('if', b.const('inner'), b.call('and', b.const('cut'), b.const('fail'))))
b.fact('outer', b.call('if', b.call('outer', b.const('a')), b.const('inner')))
b.fact('outer', b.call('outer', b.const('b')))
add('callee_cut_preserves_caller', b, b.call('outer', b.var()), [b.answer('b')])
b = Builder(1)
b.fact('p', b.pi(b.call('p', b.app(b.const('s'), b.idx(0)))))
add('open_successor', b, b.call('p', b.nat(123)), [[1, 0, 0, 0, 0, -1]])
b = Builder(1)
b.fact('decompose', b.pi(b.call('decompose', b.idx(0), b.app(b.const('s'), b.idx(0)))))
add('successor_binding', b, b.call('decompose', b.var(), b.nat(3)), [[1, 6, 1, ord('2')]])
b = Builder(1)
big = '9' * 60
add('big_natural_normalization', b, b.eq(b.var(), b.app(b.const('s'), b.nat(big))), [[1, 6, 61, ord('1'), *([ord('0')] * 60)]])
b = Builder()
b.symbol('formula', 20)
formula = b.const('formula')
add('opaque_formula_not_constructor', b, b.sigma(b.call('and', b.eq(b.idx(0), formula), b.idx(0))), [])
b = Builder()
b.symbol('formula', 20)
add('opaque_formula_direct_service', b, b.const('formula'), [[0]])
# Static and dynamically classified facts share their original source order.
b = Builder(1)
for name, dynamic in [('a', False), ('b', True), ('c', False), ('d', True)]:
    root = b.call('p', b.const(name))
    b.facts.append([-1 if dynamic else b.symbol('p'), root])
add('indexed_dynamic_source_order', b, b.call('p', b.var()), [b.answer(name) for name in ['a', 'b', 'c', 'd']])
b = Builder(1)
b.fact('p', b.call('p', b.const('a')))
b.facts.append([-1, b.call('if', b.call('p', b.const('b')), b.const('cut'))])
b.fact('p', b.call('p', b.const('c')))
add('indexed_dynamic_cut', b, b.call('p', b.var()), [b.answer('a'), b.answer('b')])
b = Builder(2)
b.facts.append([-1, b.app(b.var(0), b.const('a'))])
query = b.call('and', b.eq(b.var(0), b.const('p')), b.call('p', b.var(1)))
add('indexed_flexible_global_head', b, query, [[2, 1, b.symbol('p'), -1, 1, b.symbol('a'), -1]])

# A flexible local head may become rigid after the implication is entered.
b = Builder()
assumption = b.app(b.idx(0), b.const('a'))
body = b.call('and', b.eq(b.idx(0), b.const('p')), b.call('p', b.const('a')))
add('local_flexible_head_after_binding', b, b.sigma(b.call('imply', assumption, body)), [[0]])
b = Builder()
goal = b.app(b.idx(0), b.const('a'))
add('local_nominal_predicate_head', b, b.pi(b.call('imply', goal, goal)), [[0]])

# Failed candidates must yield before the whole table has been inspected. The
# candidates share their first argument, so the index keeps all of them.
b = Builder()
b.facts = []
wrong = b.call('p', b.const('same'), b.const('wrong'))
for _ in range(5000):
    b.fact('p', wrong)
b.fact('p', b.call('p', b.const('same'), b.const('right')))
add('yielded_clause_search', b, b.call('p', b.const('same'), b.const('right')), [[0]])
b = Builder()
b.facts = []
wrong = b.eq(b.const('a'), b.const('b'))
for _ in range(5000):
    b.fact('eq', wrong)
b.fact('eq', b.eq(b.const('a'), b.const('a')))
add('yielded_equality_resume', b, b.eq(b.const('a'), b.const('a')), [[0]])

# A rejected leaf resumes through many failed alternatives without blocking.
# The second clause for p matches every call and fails only in its body.
b = Builder()
b.symbol('print', 19)
b.fact('p', b.call('p', b.const('blue')))
b.fact('p', b.call('if', b.call('p', b.const('blue')), b.call('absent')))
b.fact('walk', b.call('if', b.call('walk', b.nat(0)), b.call('print', b.const('done'))))
body = b.call('and', b.call('p', b.const('blue')), b.call('walk', b.idx(0)))
b.fact('walk', b.pi(b.call('if', b.call('walk', b.app(b.const('s'), b.idx(0))), body)))
add('yield_failed_backtracking', b, b.call('walk', b.nat(5000)), [[0]])

# A clause whose argument has a different rigid head is never tried, so the
# same walk leaves no choice point per level: rejection ends the search at once.
b = Builder()
b.symbol('print', 19)
b.fact('p', b.call('p', b.const('blue')))
b.fact('p', b.call('p', b.const('red')))
b.fact('walk', b.call('if', b.call('walk', b.nat(0)), b.call('print', b.const('done'))))
body = b.call('and', b.call('p', b.const('blue')), b.call('walk', b.idx(0)))
b.fact('walk', b.pi(b.call('if', b.call('walk', b.app(b.const('s'), b.idx(0))), body)))
add('excluded_clause_choice', b, b.call('walk', b.nat(5000)), [[0]])

# A deterministic descent leaves nothing behind: its heap stays near the size
# of the program however long it runs.
b = Builder()
b.fact('descend', b.call('descend', b.nat(0)))
b.fact('descend', b.pi(b.call('if', b.call('descend', b.app(b.const('s'), b.idx(0))), b.call('descend', b.idx(0)))))
add('collected_descent', b, b.call('descend', b.nat(20000)), [[0]])

# The exclusion looks only at rigid heads: a flexible or nominal argument and
# a clause variable keep their clauses, in source order.
b = Builder(1)
b.fact('q', b.call('q', b.call('f', b.const('a')), b.const('one')))
b.fact('q', b.call('q', b.call('g', b.const('a')), b.const('two')))
b.fact('q', b.pi(b.call('q', b.idx(0), b.const('three'))))
b.fact('q', b.call('q', b.call('g', b.const('b')), b.const('four')))
add('excluded_clause_order', b, b.call('q', b.call('g', b.const('a')), b.var()), [b.answer('two'), b.answer('three')])
b = Builder(1)
b.fact('q', b.call('q', b.call('f', b.const('a')), b.const('one')))
b.fact('q', b.call('q', b.call('g', b.const('a')), b.const('two')))
query = b.sigma(b.call('q', b.idx(0), b.var()))
add('excluded_clause_flexible', b, query, [b.answer('one'), b.answer('two')])

# Two different naturals exclude a clause like two different constants: only
# the clause of 40 is instantiated, so the run creates one variable.
b = Builder()
for number in range(1, 51):
    b.fact('p', b.pi(b.call('p', b.nat(number), b.idx(0))))
add('excluded_natural_clause', b, b.call('p', b.nat(40), b.const('a')), [[0]])
b = Builder(1)
b.fact('q', b.call('q', b.nat(1), b.const('one')))
b.fact('q', b.pi(b.call('q', b.app(b.const('s'), b.idx(0)), b.const('two'))))
b.fact('q', b.pi(b.call('q', b.idx(0), b.const('three'))))
b.fact('q', b.call('q', b.nat(2), b.const('four')))
b.fact('q', b.call('q', b.nat(3), b.const('five')))
add('excluded_natural_order', b, b.call('q', b.nat(2), b.var()), [b.answer(name) for name in ['two', 'three', 'four']])

# `flex` is decided by the machine: it inspects the head and binds nothing.
b = Builder()
b.symbol('flex', 22)
add('flex_unbound', b, b.sigma(b.call('flex', b.const('t'), b.idx(0))), [[0]])
b = Builder()
b.symbol('flex', 22)
add('flex_constant', b, b.call('flex', b.const('t'), b.const('a')), [])
b = Builder()
b.symbol('flex', 22)
bound = b.call('and', b.eq(b.idx(0), b.const('a')), b.call('flex', b.const('t'), b.idx(0)))
add('flex_bound', b, b.sigma(bound), [])
b = Builder()
b.symbol('flex', 22)
add('flex_nominal', b, b.pi(b.call('flex', b.const('t'), b.idx(0))), [])
b = Builder()
b.symbol('flex', 22)
applied = b.pi(b.call('flex', b.const('t'), b.app(b.idx(1), b.idx(0))))
add('flex_applied_variable', b, b.sigma(applied), [[0]])
b = Builder()
b.symbol('flex', 22)
expanded = b.call('flex', b.const('t'), b.lam(b.app(b.idx(1), b.idx(0))))
add('flex_under_abstraction', b, b.sigma(expanded), [[0]])
b = Builder()
b.symbol('flex', 22)
rigid = b.call('flex', b.const('t'), b.lam(b.app(b.const('f'), b.idx(0))))
add('flex_rigid_under_abstraction', b, rigid, [])
b = Builder()
b.symbol('flex', 22)
after = b.call('and', b.call('flex', b.const('t'), b.idx(0)), b.eq(b.idx(0), b.const('a')))
add('flex_binds_nothing', b, b.sigma(after), [[0]])

# The machine decides an equality whose type is not the naturals and whose
# sides, as bound, mention no arithmetic; the host decides the others.
b = Builder(1)
add('plain_equality', b, b.eq(b.var(), b.const('a')), [b.answer('a')])
b = Builder(1)
b.symbol('nat', 24)
add('natural_equality', b, b.call('eq', b.const('nat'), b.var(), b.const('a')), [b.answer('a')])
b = Builder(1)
b.symbol('plus', 23)
total = b.call('plus', b.const('a'), b.const('b'))
wire = [2, -1, 2, -1, 1, b.symbol('plus'), -1, 1, b.symbol('a'), -1, 1, b.symbol('b'), -1]
add('arithmetic_equality', b, b.eq(b.var(), total), [[1] + wire])
b = Builder()
side = b.app(b.const('s'), b.idx(0))
add('successor_equality', b, b.sigma(b.eq(side, side)), [[0]])
b = Builder()
b.symbol('plus', 23)
first = b.eq(b.idx(0), b.call('plus', b.const('a'), b.const('b')))
second = b.eq(b.call('f', b.idx(0)), b.call('f', b.idx(0)))
add('bound_arithmetic_equality', b, b.sigma(b.call('and', first, second)), [[0]])
b = Builder()
b.symbol('formula', 20)
add('opaque_equality', b, b.eq(b.const('formula'), b.const('formula')), [])

# The machine enters an implication whose antecedent is a conjunction of atoms
# and clauses with ordinary heads; the host sees the others.
b = Builder(1)
b.fact('p', b.call('p', b.const('a')))
clause = b.call('if', b.call('p', b.const('c')), b.const('true'))
locals_ = b.call('and', b.call('p', b.const('b')), clause)
add('plain_antecedent', b, b.call('imply', locals_, b.call('p', b.var())), [b.answer(name) for name in ['a', 'b', 'c']])
b = Builder(1)
b.fact('p', b.call('p', b.const('a')))
quantified = b.pi(b.call('q', b.idx(0)))
add('quantified_antecedent', b, b.call('imply', quantified, b.call('p', b.var())), [b.answer('a')])
b = Builder(1)
b.symbol('lt', 15)
b.fact('p', b.call('p', b.const('a')))
compared = b.call('lt', b.nat(1), b.nat(2))
add('comparison_antecedent', b, b.call('imply', compared, b.call('p', b.var())), [b.answer('a')])

# A list built from a nominal, innermost element first, is stable: the run
# stays within a small node-visit budget for each term operation, however long
# the list is, and no equality of it reaches the host.
b = Builder()
b.fact('build', b.pi(b.call('build', b.nat(0), b.idx(0), b.const('nil'))))
head = b.call('build', b.app(b.const('s'), b.idx(3)), b.idx(2), b.idx(1))
longer = b.eq(b.idx(1), b.call('cons', b.idx(2), b.idx(0)))
body = b.call('and', b.call('build', b.idx(3), b.idx(2), b.idx(0)), longer)
b.fact('build', b.pi(b.pi(b.pi(b.pi(b.call('if', head, body))))))
add('stable_bottom_up_list', b, b.pi(b.sigma(b.call('build', b.nat(400), b.idx(1), b.idx(0)))), [[0]])

# Only identities in normalized pending frames belong in compact metadata.
b = Builder(1)
b.symbol('print', 19)
normalized = b.app(b.lam(b.nat(123)), b.var())
hyp = b.call('p', b.idx(1), b.idx(0), normalized, b.lam(b.idx(0)), b.term(6))
body = b.call('and', b.call('and', b.call('print', b.const('done')), hyp), hyp)
query = b.pi(b.sigma(b.call('imply', hyp, body)))
add('compact_frame_declarations', b, query, [[1, 0, 0, 0, 0, -1]])

# A table of facts is searched through its first argument: the last of 6000
# naturals, or of 6000 constants, is found without inspecting the others.
b = Builder(1)
for number in range(6000):
    b.fact('row', b.call('row', b.nat(number), b.const('v%d' % (number % 7))))
add('indexed_natural_table', b, b.call('row', b.nat(5999), b.var()), [b.answer('v%d' % (5999 % 7))])
b = Builder(1)
for number in range(6000):
    b.fact('row', b.call('row', b.call('k%d' % number, b.const('a')), b.const('v%d' % (number % 7))))
add('indexed_constant_table', b, b.call('row', b.call('k5999', b.const('a')), b.var()), [b.answer('v%d' % (5999 % 7))])
# A nominal first argument meets no clause that has a constant there. A natural
# and a constant are left to the unifier, as rigid_clash leaves them.
b = Builder(1)
b.fact('q', b.call('q', b.const('a'), b.const('one')))
b.fact('q', b.pi(b.call('q', b.idx(0), b.const('two'))))
b.fact('q', b.call('q', b.const('b'), b.const('three')))
add('indexed_nominal_argument', b, b.pi(b.call('q', b.idx(0), b.var())), [b.answer('two')])
b = Builder(1)
b.fact('m', b.call('m', b.nat(1), b.const('one')))
b.fact('m', b.call('m', b.const('a'), b.const('two')))
b.fact('m', b.call('m', b.nat(2), b.const('three')))
b.fact('m', b.pi(b.call('m', b.idx(0), b.const('four'))))
add('indexed_mixed_keys', b, b.call('m', b.nat(2), b.var()), [b.answer('three'), b.answer('four')])

b = Builder(1)
add('unbound_query', b, b.const('true'), [[1, 0, 0, 0, 0, -1]])
b = Builder(1)
choices = b.call('or', b.eq(b.var(), b.const('a')), b.eq(b.var(), b.const('b')))
add('snapshot_and_assignment', b, choices, [b.answer('a'), b.answer('b')])
b = Builder(1)
choices = b.call('or', b.eq(b.var(), b.const('a')), b.eq(b.var(), b.const('b')))
add('snapshot_before_cut', b, b.call('and', choices, b.const('cut')), [b.answer('a')])

lines = []
parts = ['seed', 'first', 'second', 'query']
for index, (name, code, answers, split) in enumerate(cases):
    flattened = sum(answers, []) or [0]
    sizes = list(map(len, answers)) or [0]
    arrays = [('code', code, 'int64_t'), ('answers', flattened, 'int64_t'), ('sizes', sizes, 'size_t')]
    arrays += [(part, words, 'int64_t') for part, words in zip(parts, split or [])]
    for kind, values, ctype in arrays:
        lines.append(f'static const {ctype} {kind}_{index}[] = {{' + ','.join(map(str, values)) + '};')
lines.append('static const TestCase cases[] = {')
for index, (name, code, answers, split) in enumerate(cases):
    pieces = ', '.join(f'{{{part}_{index}, sizeof({part}_{index}) / sizeof(int64_t)}}' if split else '{NULL, 0}' for part in parts)
    lines.append(f'    {{"{name}", code_{index}, sizeof(code_{index}) / sizeof(int64_t), answers_{index}, sizes_{index}, {len(answers)}, {{{pieces}}}}},')
lines.append('};')
Path(sys.argv[1]).write_text('\n'.join(lines) + '\n')
