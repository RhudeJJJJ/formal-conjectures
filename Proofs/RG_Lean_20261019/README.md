# Partial RG: universal U/J norm identities

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

This checkpoint proves the both-long-arm U/J norm identities for every real residual degree and every positive ordinate. The logarithmic and actual-graph bridges are available for every positive residual degree, under their explicitly stated polynomial-margin premise. No universal strict-fusion or global path-minimum proof is claimed.

The degree dependence is quartic. Exact interpolation at 0, 2, 3, 4 and 5 replaces an infeasible direct rational expansion. All 64 modules in the endpoint dependency closure were accepted by the pinned Lean 4.33.1 verifier, with only propext, Classical.choice and Quot.sound. Verification used matching retained compiler checkpoints and fresh kernel exports; this is not a fresh rebuild of every historical module. The receipt identifies each mode and binds source and dependency hashes.

To rebuild from source, obtain Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474 with its official Lean 4.33.1 toolchain and dependencies, run its cache get command, then from this directory run:

```sh
python3 verify_extension.py --mathlib-project /absolute/path/to/mathlib4 --endpoint Proofs.RadenkovicGutmanLongArmBothAllDegrees --workers 1 --module-timeout 7200
```

No binary checkpoints are included in this source checkpoint. The retained LeanCert sources and upstream hash metadata satisfy the verifier's pin checks.

Still open globally: residual degree one, remaining finite-degree long-arm cases, remaining small orders and exhaustive finite coverage, and unconditional nonpath decomposition. The degree-six continuation is being checked separately. The existing upstream PR #7399 remains a statement submission; its two research statements retain sorry and no complete formal_proof certificate is claimed.
