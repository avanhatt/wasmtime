# Notes for verifying Cranelift's ISLE rules in SMT

Some exploratory notes for how to structure verification of Cranelift's ISLE lowering rules.
ISLE is a domain-specific language for specifying rewrite rules, primarily for instruction selection.
ISLE source text is [compiled down into Rust
code](https://github.com/bytecodealliance/wasmtime/tree/main/cranelift/isle#implementation).

Documentation on the ISLE-Cranelift integration can be found
[here](../isle-integration.md), and documentation on the language itself can be found
[here](../isle/docs/language-reference.md).

## What do we mean by "verifying" ISLE rules?

At a high level, our goal is to show that ISLE's rules maintain semantic equivalence of program fragments before and after rule application. 
In principal, a fully verified implementation of ISLE would include verification of the rules themselves, the Rust code generation, and the rule application implementation. 
However, as a first step, we are interested in verifying just the first component: the rules themselves. The two reasons I (Alexa) see for starting there:
1. Individual rules are declarative, small, mostly self-contained, and amenable to composable SMT-style verification.
2. Prior related work, such as [Alive](https://web.ist.utl.pt/nuno.lopes/pubs/alive-pldi15.pdf), has shown that only looking at rules can still find impactful bugs.

By "verifying" an individual rule, we can probably rely on simple semantic equivalence rather than something more complicated such as refinement, since Cranelift tries to avoid undefined behavior. 

Thus, for a rule like:
```lisp
(rule (lower (has_type (fits_in_64 ty) (iadd x y)))
      (value_reg (add ty (put_in_reg x) (put_in_reg y))))
```

We would want to show something like (with made-up syntax and some additional side conditions for types/sizes):
```lisp
(forall 
  (x y)
  (=  (iadd x y)
      (get_reg (put_get (add (put_reg x) (put_reg y))))))
```

In a classic SMT-verification style, we would do this by asserting the negation of the property we want and checking for SAT.
An UNSAT model implies no counterexample is found and the semantic equivalence holds.
```lisp
(declare-const x y (_ BitVec 64))
(declare-fun get_reg ...)
(declare-fun put_reg ...)
(assert (let 
    (lhs (bvadd x y))
    (rhs (get_reg (put_get (bvadd (put_reg a) (put_reg b)))))
    (not (=  lhs rhs))))

; If this result is (unsat), the rule holds since no counterexample
; is found. If it returns (sat), the model provides a counterexample.
(check-sat)
```

If we can show this equivalence for every rule, we raise our assurance that ISLE correctly implements instruction lowering for all possible inputs both in terms of the programs Cranelift is compiling and all possible inputs to those programs. 

## Why SMT?

Cranelift is primarily a production engineering project, so our solution should focus on a high degree of automation.
SMT should free engineers from having to construct proofs themselves.
We can also build on existing projects for large-scale instruction set architecture (ISA) semantics that support SMT to handle many "right hand sides" of rules. 

## Existing ISA semantics

There have been several recent advances in modeling the semantics of real-world ISAs. Our goal should be to build on these as much as possible. 

1. [SAIL semantics, including for arm (POPL 19)](https://www.cl.cam.ac.uk/~pes20/sail/sail-popl2019.pdf)
2. [K-framework semantics for x86 (PLDI 19)](https://dl.acm.org/doi/10.1145/3314221.3314601)
3. [Stoke semantics for x86](https://github.com/StanfordPL/stoke)

However, it's important to note that ISLE rules are not _required_ to compile "all the way" to ISA instructions on the right hand side. Rather, many rules write to temporary values that enable downstream rewrites.

In addition, each of the existing ISA projects had their own slightly different use cases, so we can expect some difficulty massaging them to this use case:
- We need to specify symbolic values not just for registers, but for constant arguments as well, which is likely in a meta-syntax that will differ for each tool. 
- Each tool has its own memory model and helper function for read/writes to registers, and at least for SAIL, the output is a superset of SMTLIB that cannot be fed directly into a solver.

