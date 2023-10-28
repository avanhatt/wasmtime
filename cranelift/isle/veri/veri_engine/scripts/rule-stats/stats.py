#!/usr/bin/env python3

import sys
from collections import Counter, namedtuple

TOP_K = 32

# Instruction classification.

MEM_OPS = ('load', 'store', 'uload8', 'sload8', 'istore8', 'uload16',
           'sload16', 'istore16', 'uload32', 'sload32', 'istore32', 'uload8x8',
           'sload8x8', 'uload16x4', 'sload16x4', 'uload32x2', 'sload32x2',
           'stack_load', 'stack_store', 'stack_addr', 'dynamic_stack_load',
           'dynamic_stack_store', 'dynamic_stack_addr', 'get_frame_pointer',
           'get_stack_pointer', 'table_addr', 'atomic_rmw', 'atomic_cas',
           'atomic_load', 'atomic_store', 'fence')
CTRL_OPS = ('jump', 'brz', 'brnz', 'br_table', 'debugtrap', 'trap', 'trapz',
            'resumable_trap', 'trapnz', 'resumable_trapnz', 'return', 'call',
            'call_indirect', 'func_addr')


# def is_fp(inst):
#     """Given a traced IL instruction string, check if it has anything to
#     do with floating point values.
#     """
#     return ('f32' in inst) or ('f64' in inst)

# Trace parsing.

EventInstruction = namedtuple("TraceInstruction", ["opcode"])
EventRule = namedtuple("TraceRule", ["name", "pos"])

def parse_trace(lines):
    trace = []
    for line in lines:
        parts = line.rstrip().split(None, 3)
        if len(parts) == 0 or parts[0] != "TRACE":
            continue
        assert len(parts) == 4
        assert parts[1] == "-"
        typ = parts[2].rstrip(":")
        fields = parts[3].split(",")
        # TRACE - inst: trap
        if typ == "inst":
            assert len(fields) == 1
            trace.append(EventInstruction(opcode=fields[0]))
        # TRACE - rule: ,src/isa/x64/inst.isle line 4101
        elif typ == "rule":
            assert len(fields) == 2
            trace.append(EventRule(
                name=fields[0],
                pos=fields[1],
            ))
        else:
            assert False, f"unknown trace type: {typ}"
    return trace


def rule_stats(exclude_fp=False, exclude_mem=False, exclude_ctrl=False):
    counts = Counter()
    names = {}

    # Ingest the trace.
    exclude = False
    for event in parse_trace(sys.stdin):
        # Instruction event: starting a new lowering.
        if isinstance(event, EventInstruction):
            # Should we exclude this instruction?
            exclude = False
            #if exclude_fp:
            #    exclude |= is_fp(inst)
            if exclude_mem:
                exclude |= event.opcode in MEM_OPS
            if exclude_ctrl:
                exclude |= event.opcode in CTRL_OPS
            continue

        # Rule event: ISLE rule fired in lowering.
        elif isinstance(event, EventRule):
            if exclude:
                continue
            counts[event.pos] += 1
            names.setdefault(event.pos, event.name)

        else:
            assert False, "unknown trace event"

    # Print the most frequently triggered rules, for fun.
    print(f'Top {TOP_K} most commonly used rules:')
    for rule_id, count in counts.most_common(TOP_K):
        print(count, rule_id, names[rule_id])

    # How many uses (times a rule was triggered) were of named rules?
    named_uses = sum(c for (i, c) in counts.items() if names.get(i))
    total_uses = sum(counts.values())
    print(f'\nNamed uses: {named_uses}/{total_uses} = '
          f'{named_uses/total_uses:.1%}')

    # How many covered rules (used at least once) were named?
    named_covered = sum(1 for (i, c) in counts.items() if names.get(i))
    total_covered = len(counts)
    print(f'\nNamed covered: {named_covered}/{total_covered} = '
          f'{named_covered/total_covered:.1%}')


if __name__ == "__main__":
    rule_stats(
        '--no-fp' in sys.argv[1:],
        '--no-mem' in sys.argv[1:],
        '--no-ctrl' in sys.argv[1:],
    )
