import sys
import re

filename = sys.argv[1]
decl = "(declare-fun "
assertion = "(assert "
pattern = re.compile(r'\{.*?\}')

# assume the line looks like (declare-fun <name> () <type>)
def parse_decl(line):
    name = line.split()[1]
    ty = f'String::from(\"{line.split("()")[1][1:-1]}\")'

    matches = re.findall(pattern, name)
    if len(matches) == 0:
        return name, ty

    var = set([m[1:-1] for m in matches])
    named_params = ', '.join([f'{x} = {x}' for x in var])
    return f'format!(\"{name}\", {named_params})', ty

# assume the line looks like (assert <assertion>)
def parse_assertion(line):
    a = line[len(assertion):-1]

    matches = re.findall(pattern, a)
    if len(matches) == 0:
        return a

    var = set([m[1:-1] for m in matches])
    named_params = ', '.join([f'{x} = {x}' for x in var])
    return f'format!(\"{a}\", {named_params})'

lines = []
with open(filename, 'r') as f:
    lines = f.readlines()

# this converter assumes there's a solver called "solver"
for l in lines:
    line = l.strip()

    # leave blank lines
    if len(line) == 0:
        print("")
        continue

    # convert comments
    if line[0] == ';':
        print(f'//{line[1:]}')
        continue

    # convert declarations
    if line[:len(decl)] == decl:
        name, ty = parse_decl(line)
        print(f'solver.additional_decls.push(({name}, {ty}));')
        continue

    # convert assertions
    if line[:len(assertion)] == assertion:
        a = parse_assertion(line)
        print(f'solver.additional_assumptions.push({a});')
        continue
