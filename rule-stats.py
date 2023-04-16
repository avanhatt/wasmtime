import csv
import sys
from collections import Counter

TOP_K = 10


def rule_stats():
    names = {}
    counts = Counter()

    # Ingest the trace.
    for row in csv.reader(sys.stdin):
        rule_id, name, pos = row
        rule_id = int(rule_id)

        counts[rule_id] += 1

        if rule_id in names:
            assert names[rule_id] == name
        else:
            names[rule_id] = name

    # Print the most frequently triggered rules, for fun.
    print(f'Top {TOP_K} rules:')
    for rule_id, count in counts.most_common(10):
        name = names.get(rule_id)
        print('{}{}: {}'.format(rule_id, f' ({name})' if name else '', count))

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
