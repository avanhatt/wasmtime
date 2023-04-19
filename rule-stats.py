import csv
import sys
from collections import Counter

TOP_K = 10


def is_fp(inst):
    """Given a traced IL instruction string, check if it has anything to
    do with floating point values.
    """
    return ('f32' in inst) or ('f64' in inst)


def rule_stats(exclude_fp=False):
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
            if exclude_fp:
                exclude = is_fp(inst)
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
    rule_stats('--no-fp' in sys.argv[1:])
