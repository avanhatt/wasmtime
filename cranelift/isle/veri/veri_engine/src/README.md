# Cranelift ISLE Verification Prototype

This crate is a prototype for verifying Cranelift's ISLE lowering rules using an SMT solver.

Currently, term semantics are specified manually in `isle_annotations.rs`. These should be replaces by annotations on ISLE terms that are then parsed to our Verification IR.  


## Testing

To see an example of our current output, run tests without capturing standard out:
```bash
cargo test -- --nocapture
```