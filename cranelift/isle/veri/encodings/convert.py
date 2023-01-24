import sys
import re
import sexpdata

DECL = "(declare-fun "
ASSERTION = "(assert "
PATTERN = r'\{(.*?)\}'


def sexpr_to_rs(sexpr):
    """Generate Rust code to generate an S-expression.

    Convert a parsed S-expression to Rust code (as a string) that
    generates the same thing. The generated code makes calls to a
    `solver` context struct.
    """
    if isinstance(sexpr, sexpdata.Symbol):
        sym = sexpr.value()
        return f'solver.smt.atom("{sym}")'
    elif isinstance(sexpr, list):
        guts = ", ".join(sexpr_to_rs(v) for v in sexpr)
        return f'solver.smt.list(vec![{guts}])'
    elif isinstance(sexpr, int):
        return f'solver.smt.numeral({sexpr})'
    else:
        assert False


def parse_decl(line):
    """Parse a `declare-fun` line.

    The line must look like `(declare-fun <name> () <type>)`. Return
    Rust expressions for the variable's name (a string) and the type (an
    SExpr).
    """
    # Parse the S-expression.
    exp = sexpdata.loads(line)
    assert exp[0].value() == 'declare-fun'
    _, name, args, ret = exp
    name = name.value()

    # Rust code to format the variable name. Format with Rust variables
    # matching the variables in the format string.
    matches = re.findall(PATTERN, name)
    if matches:
        var = [m[0] for m in matches]
        named_params = ', '.join([f'{x} = {x}' for x in var])
        name_rs = f'format!(\"{name}\", {named_params})'
    else:
        name_rs = name  # TODO Should be surrounded in quotes?

    return name_rs, sexpr_to_rs(ret)


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
