import Forge.AST
import Forge.Eval
import Forge.Optimize
import Forge.OptimizeCorrect
import Forge.Ownership
import Forge.Match
import Forge.Mailbox
import Forge.BoundedMailbox
import Forge.CheckedInt64

/-!
# Forge formal verification

Root module for the Lean 4 proofs accompanying the [Forge](https://github.com/forge-language/forge)
language implementation.

## Verified components

| Module | C counterpart | Property |
|--------|---------------|----------|
| `Forge.OptimizeCorrect` | abstract expression optimizer | optimization preserves the mathematical model's semantics |
| `Forge.Ownership` | ownership-state model | moved bindings cannot be read or moved again in the model |
| `Forge.Match` | `examples/match.fg` | first matching `match` arm is selected |
| `Forge.Mailbox` | unbounded mailbox model | send then recv delivers the message |
| `Forge.BoundedMailbox` | `forge-runtime/src/scheduler.c` admission contract | capacity bound, FIFO admission, unchanged rejection and payload disposal token |
| `Forge.CheckedInt64` | `compiler/optimize.c` guard specification | accepted results fit int64; zero division and minimum divided by negative one rejected |

These proofs do not establish refinement of the C implementation, heap safety,
thread safety, runtime liveness or correctness of the full compiler. The original
optimizer model uses mathematical integers, not bounded native integers.

## Build

```bash
cd forge-proofs
lake build
```

Requires [Lean 4](https://leanprover.github.io/) ≥ 4.14.0 (`elan` recommended).
-/
