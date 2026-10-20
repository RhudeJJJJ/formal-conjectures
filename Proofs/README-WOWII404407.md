# Complete Lean certificates for WOWII 404–407

All four original numbered inequalities in PR #7381 now have complete external
Lean certificates. The statements use finite simple trees of order greater
than two, maximum cardinality among critical independent sets, open private
external neighbors, and the original integer subtractions.

| Target | Complete theorem |
|---|---|
| WOWII 404 | `WOWII404406Proof.conjecture404` |
| WOWII 405 | `WOWII405407Proof.conjecture405` |
| WOWII 406 | `WOWII404406Proof.conjecture406` |
| WOWII 407 | `WOWII405407Proof.conjecture407` |

The existing bipartite critical-union/corona bridge and corona exchange proof
show that the common left side is zero. For 404, the new proof supplies a
support vertex. For 406, it proves that a leaf's neighbor cannot be a leaf in
a connected graph of order greater than two, identifies the private-neighbor
count of the nonleaf set with the leaf count, and uses the two distinct leaves
of a nontrivial tree. These steps prove nonnegativity of both integer right
sides. The excluded orders, especially the two-vertex tree, are not silently
admitted into the 406 identity.

## Sources and reused work

Written proof: Jonas J. Gebendorfer, *The Corona of a Graph Is 2-Dominating*,
31 August 2026, revision R2, Corollary 4.2. The [public source archive](https://github.com/user-attachments/files/33373103/Gebendorfer_WOWII_404_407_Intake_2026-10-13.zip)
includes the manuscript and frozen WOWII statements/definitions. The new
formalization follows its nonnegativity argument. The critical-set bridge is
established literature credited there to Larson, Levit–Mandrescu and
Jarden–Levit–Mandrescu. Mathlib supplies the tree leaf-existence theorems.

The four source files used for 405/407 are unchanged from the earlier
certificate package at `a4b3b22c9d4c7d5904210fc20b676430dd4ab7c4`.
`WOWII412dCore.lean` retains blob `9860f8a4c1931f5d33191fd5561783dc9ec7b1e4`;
`CoronaTwoDominatingProof.lean` retains blob
`6a17b67d160ca4bdbf92a88e419dd7492940ccac`.
This update adds the 404/406 proofs and a guard for all four numbered targets;
it does not count the reused lemmas as new results.

OpenAI Codex assisted with formalization and validation.

## Reproduction

Use official Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The certificate checkout includes
the exact imported statement module at base commit
`5b0dd480ac6eaa3bdc986cbe7bd3acb35ba551d1`. From the repository root:

```bash
lake exe cache get
bash Proofs/WOWII404407Validation/check.sh
```

The script checks source hashes, builds the exact statement scope and freshly
exports all six local proof/audit modules. Warnings are errors; implicit
variable creation is disabled. The combined audit restates the exact 404/406
targets and checks all four end-theorem transitive axiom closures against
`propext`, `Classical.choice` and `Quot.sound`. It also verifies that the same
whitelist rejects `sorryAx` as a negative control. The earlier exact-target
audit for 405/407 is rerun as well.

Logs and validation metadata are in `WOWII404407Validation/`. The disclosed
`environment/process_path.c` adapter retries only a failed numeric lookup of
the current process's executable through `/proc/self/exe`; the sandbox needs
it, ordinary systems do not. No Lean binary or kernel rule is changed.

## Scope

This closes the formal-proof gaps for the four original inequalities.
The manuscript's equality/slack classification, the full KE converse and the
complete universal theorem for WOWII 412d are separate targets. Kernel checks
and successful builds are distinct from new external review or upstream
acceptance.
