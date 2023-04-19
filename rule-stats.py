import csv
import sys
from collections import Counter

TOP_K = 10

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


def is_fp(inst):
    """Given a traced IL instruction string, check if it has anything to
    do with floating point values.
    """
    return ('f32' in inst) or ('f64' in inst)


def rule_stats(exclude_fp=False, exclude_mem=False, exclude_ctrl=False):
    counts = Counter()
    names = {}
    poss = {}

    # Ingest the trace.
    exclude = False
    for row in csv.reader(sys.stdin):
        rule_id, name, pos, inst = row

        # Log messages either have an opcode/types string (indicating a
        # new instruction is being lowered) or have all the other fields
        # (indicating a rule was triggered).
        if inst:
            assert not (rule_id or name or pos)
            opcode, _ = inst.split(None, 1)

            # Should we exclude this instruction?
            exclude = False
            if exclude_fp:
                exclude |= is_fp(inst)
            if exclude_mem:
                exclude |= opcode in MEM_OPS
            if exclude_ctrl:
                exclude |= opcode in CTRL_OPS

            continue

        # This is a rule invocation event. If it's associated with an
        # instruction we're excluding, don't count it.
        if exclude:
            continue

        rule_id = int(rule_id)

        counts[rule_id] += 1

        if rule_id in names:
            assert names[rule_id] == name
            assert poss[rule_id] == pos
        else:
            names[rule_id] = name
            poss[rule_id] = pos

    # Print the most frequently triggered rules, for fun.
    print(f'Top {TOP_K} rules:')
    for rule_id, count in counts.most_common(TOP_K):
        print(count, rule_id, names[rule_id], poss[rule_id])

    # How many uses (times a rule was triggered) were of named rules?
    named_uses = sum(c for (i, c) in counts.items() if names.get(i))
    total_uses = sum(counts.values())
    print(f'Named uses: {named_uses}/{total_uses} = '
          f'{named_uses/total_uses:.1%}')

    # How many covered rules (used at least once) were named?
    named_covered = sum(1 for (i, c) in counts.items() if names.get(i))
    total_covered = len(counts)
    print(f'Named covered: {named_covered}/{total_covered} = '
          f'{named_covered/total_covered:.1%}')


if __name__ == "__main__":
    rule_stats(
        '--no-fp' in sys.argv[1:],
        '--no-mem' in sys.argv[1:],
        '--no-ctrl' in sys.argv[1:],
    )
