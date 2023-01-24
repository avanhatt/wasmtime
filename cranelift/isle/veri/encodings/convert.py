import sys
import re

DECL = "(declare-fun "
ASSERTION = "(assert "
PATTERN = re.compile(r'\{.*?\}')


# assume the line looks like (declare-fun <name> () <type>)
def parse_decl(line):
    name = line.split()[1]
    ty = f'String::from(\"{line.split("()")[1][1:-1]}\")'

    matches = re.findall(PATTERN, name)
    if len(matches) == 0:
        return name, ty

    var = set([m[1:-1] for m in matches])
    named_params = ', '.join([f'{x} = {x}' for x in var])
    return f'format!(\"{name}\", {named_params})', ty


# assume the line looks like (assert <assertion>)
def parse_assertion(line):
    a = line[len(ASSERTION):-1]

    matches = re.findall(PATTERN, a)
    if len(matches) == 0:
        return a

    var = set([m[1:-1] for m in matches])
    named_params = ', '.join([f'{x} = {x}' for x in var])
    return f'format!(\"{a}\", {named_params})'


def main():
    filename = sys.argv[1]

    lines = []
    with open(filename, 'r') as f:
        lines = f.readlines()

    # this converter assumes there's a solver called "solver"
    for line in lines:
        line = line.strip()

        # leave blank lines
        if len(line) == 0:
            print("")
            continue

        # convert comments
        if line[0] == ';':
            print(f'//{line[1:]}')
            continue

        # convert declarations
        if line.startswith(DECL):
            name, ty = parse_decl(line)
            print(f'solver.declare({name}, {ty});')
            continue

        # convert assertions
        if line.startswith(ASSERTION):
            a = parse_assertion(line)
            print(f'solver.assume({a});')
            continue


if __name__ == '__main__':
    main()
