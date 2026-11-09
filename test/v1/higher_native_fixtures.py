#!/usr/bin/env python3
"""Independent wordcode fixtures for the higher-order C executor."""
import sys
from pathlib import Path


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
                + sum(self.terms, []) + sum(self.facts, []) + self.digits)

    def answer(self, name):
        return [1, 1, self.symbol(name), -1]


cases = []


def add(name, b, query, expected):
    cases.append((name, b.code(query), expected))


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
b = Builder(1)
add('unbound_query', b, b.const('true'), [[1, 0, 0, 0, 0, -1]])
b = Builder(1)
choices = b.call('or', b.eq(b.var(), b.const('a')), b.eq(b.var(), b.const('b')))
add('snapshot_and_assignment', b, choices, [b.answer('a'), b.answer('b')])
b = Builder(1)
choices = b.call('or', b.eq(b.var(), b.const('a')), b.eq(b.var(), b.const('b')))
add('snapshot_before_cut', b, b.call('and', choices, b.const('cut')), [b.answer('a')])

lines = []
for index, (name, code, answers) in enumerate(cases):
    flattened = sum(answers, []) or [0]
    sizes = list(map(len, answers)) or [0]
    for kind, values, ctype in [('code', code, 'int64_t'), ('answers', flattened, 'int64_t'), ('sizes', sizes, 'size_t')]:
        lines.append(f'static const {ctype} {kind}_{index}[] = {{' + ','.join(map(str, values)) + '};')
lines.append('static const TestCase cases[] = {')
for index, (name, code, answers) in enumerate(cases):
    lines.append(f'    {{"{name}", code_{index}, sizeof(code_{index}) / sizeof(int64_t), answers_{index}, sizes_{index}, {len(answers)}}},')
lines.append('};')
Path(sys.argv[1]).write_text('\n'.join(lines) + '\n')
