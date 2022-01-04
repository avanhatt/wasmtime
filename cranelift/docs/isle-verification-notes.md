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

In a classic SMT-verification style, we would do this by asserting the negation of the property we want and checking for SAT with a model that would be a counterexample:
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

If we can show this equivalence for every rule, we raise our assurance that ISLE correctly implements instruction lowering for _all_ possible inputs both in terms of the _programs_ Cranelift is compiling and _their_ input arguments.