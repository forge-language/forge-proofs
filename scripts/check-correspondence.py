#!/usr/bin/env python3
"""Finite Lean/C correspondence checks, not a C refinement proof.

Safe expressions are emitted as C, compiled with UBSan and executed. Expressions
whose Lean checked model returns none are inspected as C text only: no unsafe
native overflow or division by zero is compiled or executed.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MIN, MAX = -(1 << 63), (1 << 63) - 1
CASES = [
    ('negative-div', '/', -7, 3), ('negative-mod', '%', -7, 3),
    ('negative-divisor', '/', 7, -3), ('negative-mod-divisor', '%', 7, -3),
    ('both-negative-div', '/', -7, -3), ('both-negative-mod', '%', -7, -3),
    ('minimum-div-one', '/', MIN, 1), ('minimum-mod-one', '%', MIN, 1),
    ('maximum-div-minus-one', '/', MAX, -1),
    ('maximum-plus-zero', '+', MAX, 0), ('minimum-minus-zero', '-', MIN, 0),
    ('maximum-minus-one', '-', MAX, 1), ('minimum-plus-one', '+', MIN, 1),
    ('large-safe-multiply', '*', 3037000499, 3037000499),
    ('minimum-times-one', '*', MIN, 1), ('minimum-times-zero', '*', MIN, 0),
    ('negative-safe-multiply', '*', -3037000499, 3037000499),
    ('addition-overflow', '+', MAX, 1), ('addition-underflow', '+', MIN, -1),
    ('subtraction-underflow', '-', MIN, 1), ('subtraction-overflow', '-', MAX, -1),
    ('multiplication-overflow', '*', 3037000500, 3037000500),
    ('minimum-times-minus-one', '*', MIN, -1),
    ('division-by-zero', '/', 7, 0), ('remainder-by-zero', '%', 7, 0),
    ('minimum-div-minus-one', '/', MIN, -1), ('minimum-mod-minus-one', '%', MIN, -1),
]


def run(command, cwd, timeout=30):
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout, shell=False)
    if result.returncode:
        raise RuntimeError('Command failed: ' + repr(command) + '\n' + result.stdout + result.stderr)
    return result.stdout


def literal(value):
    # Binary subtraction makes negative operands genuine constant-folded INT
    # nodes, rather than relying on an optimizer handling unary expressions.
    if value == MIN:
        return '((0 - 9223372036854775807) - 1)'
    return '(0 - ' + str(-value) + ')' if value < 0 else str(value)


def lean_expectations(lake, temporary):
    lines = ['import Forge.CheckedInt64', 'open Forge', 'def main : IO Unit := do']
    for name, op, left, right in CASES:
        a, b = '(' + str(left) + ')', '(' + str(right) + ')'
        expression = {'+': f'checkedInt64 ({a} + {b})', '-': f'checkedInt64 ({a} - {b})',
                      '*': f'checkedInt64 ({a} * {b})', '/': f'checkedDiv64 {a} {b}',
                      '%': f'checkedMod64 {a} {b}'}[op]
        lines += [f'  let result := {expression}',
                  f'  IO.println ("{name}:" ++ (match result with | some n => toString n | none => "none"))']
    oracle = temporary / 'oracle.lean'
    oracle.write_text('\n'.join(lines) + '\n')
    output = run([lake, 'env', 'lean', '--run', str(oracle)], ROOT)
    results = {}
    for line in output.splitlines():
        identity, value = line.split(':', 1)
        results[identity] = None if value == 'none' else int(value)
    if set(results) != {case[0] for case in CASES}:
        raise ValueError('Lean oracle did not report every case')
    return results


def emitted_return(text):
    # Inspect the named expression function rather than runtime/header returns.
    match = re.search(r'\b(?:fg_)?evaluate\s*\([^)]*\)\s*\{\s*return\s+([^;]+);', text)
    if not match:
        raise ValueError('Could not locate evaluate return expression in generated C')
    return match.group(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--forge', default='forge', help='Actual Forge compiler executable')
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--cc', default='cc', help='GCC/Clang-compatible host C compiler with UBSan')
    parser.add_argument('--include', type=Path, required=True, help='Installed SDK include directory')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    executables = {name: shutil.which(value) for name, value in [('forge', args.forge), ('lake', args.lake), ('cc', args.cc)]}
    if not all(executables.values()):
        parser.error('Forge, Lake and the host C compiler must be installed')
    run([executables['lake'], 'build'], ROOT, 120)
    records = []
    with tempfile.TemporaryDirectory(prefix='forge-proof-correspondence-') as directory:
        temporary = Path(directory)
        expectations = lean_expectations(executables['lake'], temporary)
        for name, op, left, right in CASES:
            expected = expectations[name]
            expression = '(' + literal(left) + ' ' + op + ' ' + literal(right) + ')'
            source = temporary / (name + '.fg')
            call = 'println(evaluate());' if expected is not None else 'println(0);'
            source.write_text('fn evaluate(): int { return ' + expression + '; }\nnative main { ' + call + ' return 0; }\n')
            emitted = temporary / (name + '.c')
            run([executables['forge'], str(source), '--emit-c', '-o', str(emitted)], temporary)
            body = emitted_return(emitted.read_text())
            if expected is None:
                # The arithmetic operator must remain: a checked guard declines
                # the fold. No C compiler or program invocation occurs here.
                if op not in body:
                    raise ValueError(name + ' unsafe operation was unexpectedly folded: ' + body)
                observed = None
                mode = 'emission-only; unsafe expression not compiled or run'
            else:
                # Isolate the compiler-emitted return expression in a minimal C
                # executable; no runtime symbols/libraries are needed.
                wrapper = temporary / (name + '-wrapper.c')
                wrapper.write_text('#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\nint main(void) { int64_t value = ' + body + '; printf("%" PRId64 "\\n", value); return 0; }\n')
                binary = temporary / (name + '-safe')
                run([executables['cc'], str(wrapper), '-std=c11', '-O1', '-fsanitize=undefined',
                     '-fno-sanitize-recover=undefined', '-I', str(args.include.resolve()), '-o', str(binary)], temporary)
                observed = int(run([str(binary)], temporary).strip())
                if observed != expected:
                    raise ValueError(name + ' Lean/C mismatch: ' + str(expected) + ' != ' + str(observed))
                mode = 'emitted expression executed with UBSan'
            records.append({'case': name, 'operation': op, 'left': left, 'right': right,
                            'lean_result': expected, 'native_result': observed, 'emitted_expression': body, 'validation': mode})
            print('PASS ' + name + ': ' + str(expected) + ' [' + mode + ']')
    if args.report:
        args.report.write_text(json.dumps({'schema_version': 1, 'lean_toolchain': (ROOT/'lean-toolchain').read_text().strip(),
            'scope': 'Finite tested correspondence, not C implementation refinement or runtime arithmetic safety',
            'cases': records}, indent=2) + '\n')
    print(str(len(records)) + ' Lean/emitted-C correspondence cases passed')


if __name__ == '__main__':
    main()
