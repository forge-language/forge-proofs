# Forge proofs

Lean 4 models and proofs for Forge AST evaluation, type checking, optimization, ownership, matching and mailbox behavior. These are executable formal models; their relationship to the C compiler implementation requires separate validation.

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build
```

`lean-toolchain` pins Lean 4.14.0 and `lake-manifest.json` records the dependency graph. Apache 2.0; see [LICENSE](LICENSE) and [PROVENANCE.md](PROVENANCE.md).
