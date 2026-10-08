# Forge proofs

Lean 4 models and proofs for Forge AST evaluation, type checking, optimization, ownership, matching and mailbox behavior. These are executable formal models; their relationship to the C compiler implementation requires separate validation.

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build
```

`lean-toolchain` pins Lean 4.14.0 and `lake-manifest.json` records the dependency graph. Apache 2.0; see [LICENSE](LICENSE) and [PROVENANCE.md](PROVENANCE.md).

The October 2026 corrective work adds `Forge.BoundedMailbox` (capacity, FIFO,
rejection without queue mutation and a payload disposal token) and
`Forge.CheckedInt64` (accepted-result bounds, zero-division and minimum-integer
division guards). The expression evaluator and optimizer now use truncation
toward zero for negative division/remainder, matching C rather than Lean's
default Euclidean division. Existing optimizer correctness theorems still build.

These are proofs of explicit models. They do not prove C implementation
refinement, heap disposal, race freedom, scheduler liveness or full Forge type
and memory safety. The mathematical optimizer uses unbounded integers; the
bounded guard model is separate, and native emitted arithmetic still inherits
the C backend's overflow behavior. The ownership model does not include aliases
or lifetimes. There are no `sorry` or extra axioms in these modules.
