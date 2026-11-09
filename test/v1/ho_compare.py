#!/usr/bin/env python3
"""Compare native HOPU with BETA, renaming only generated variable identities."""

import json
import subprocess
import sys
from pathlib import Path


def canonical(words):
    if words in ([0], [-1]):
        return words
    original = {0, 1, 2, 3}
    renamed = {}

    def term(data):
        stream = iter(data)

        def parse():
            tag = next(stream)
            if tag == 0:
                uid, scope, is_type, _ = (next(stream) for _ in range(4))
                if uid not in original:
                    if uid not in renamed:
                        renamed[uid] = 100 + len(renamed)
                    uid = renamed[uid]
                return ("var", uid, scope, is_type)
            if tag == 1:
                return ("con", next(stream), next(stream))
            if tag == 2:
                next(stream)
                return ("app", parse(), parse())
            if tag == 3:
                return ("idx", next(stream))
            if tag == 4:
                next(stream)
                return ("lam", parse())
            if tag == 5:
                return ("nom", next(stream), next(stream), next(stream))
            if tag == 6:
                return ("nat", "".join(chr(next(stream)) for _ in range(next(stream))))
            if tag == 7:
                return ("wild",)
            raise ValueError(f"unknown term tag {tag}")

        result = parse()
        if list(stream):
            raise ValueError("trailing term words")
        return result

    cursor = 2
    output = [1, words[1]]
    for _ in range(words[1]):
        length = words[cursor]
        cursor += 1
        output.append(term(words[cursor:cursor + length]))
        cursor += length
    pending = words[cursor]
    cursor += 1
    output.append(pending)
    for _ in range(2 * pending):
        length = words[cursor]
        cursor += 1
        output.append(term(words[cursor:cursor + length]))
        cursor += length
    if cursor != len(words):
        raise ValueError("trailing result words")
    return output


def main():
    lines = Path(sys.argv[2]).read_text().splitlines()
    failures = 0
    for offset in range(0, len(lines), 3):
        name, source, expected = map(json.loads, lines[offset:offset + 3])
        result = subprocess.run(
            [sys.argv[1]], input=" ".join(map(str, source)), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=3,
        )
        if result.returncode:
            print("ERROR", name, result.stderr)
            failures += 1
            continue
        actual = json.loads(result.stdout)
        if canonical(actual) != canonical(expected):
            print("DIFF", name, "\nBETA", canonical(expected), "\nC", canonical(actual))
            failures += 1
        else:
            print("PASS HOPU differential:", name)
    if len(lines) != 642:
        raise SystemExit("BETA differential fixture list is incomplete")
    if failures:
        raise SystemExit(f"HOPU differential failures: {failures}")


if __name__ == "__main__":
    main()
