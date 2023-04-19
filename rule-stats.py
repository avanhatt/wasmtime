import csv
import sys
from collections import Counter

TOP_K = 10


def rule_stats():
    counts = Counter()
    names = {}
    poss = {}

    # Ingest the trace.
    for row in csv.reader(sys.stdin):
        rule_id, name, pos, opcode = row

        # Log messages either have an opcode (indicating a new
        # instruction is being lowered) or have all the other fields
        # (indicating a rule was triggered).
        if opcode:
            assert not (rule_id or name or pos)
            print(opcode)
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
    rule_stats()
