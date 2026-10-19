# Actual source isomorphism and two-input RG assembly

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**UNVERIFIED DRAFT.** The source at c915df24f63b3cc97b03677560d6f3b7316f8eb0 has not been accepted by the Lean kernel. The [21-module check](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39283598761) is queued during a reported GitHub Actions incident. The two new modules have no completed axiom audit. The declarations below describe the implemented candidate, not a verified closure of the decomposition input. The unconditional universal energy theorem remains unproved in Lean.

The local Windows API probe timed out at 60 seconds. A further probe without Mathlib timed out at 30 seconds. The existing Ubuntu environment failed before starting its discovery shell with Wsl/Service/E_UNEXPECTED. These are environment and resource observations, not mathematical counterexamples. See the captured probe receipts and the primary GitHub status snapshot in the local draft package.

## Target and witness identity

The new `SourcePresentation.sourceIso` relabels the very `PendantFork G` obtained in the previous checkpoint. It maps the residual to Fin m and the two actual walk tails to Fin (p+1), Fin (q+1). The physical arm lengths are exactly the lengths of those same selected walks. Label zero on each arm is its attachment neighbor, including the single-edge case.

The candidate contains proof terms for bijectivity of the vertex map from the disjoint union of that residual and those two arm tails to the original vertex set. It addresses all nine adjacency blocks: core/core, both path blocks, both root attachments in both directions, and absence of cross-arm edges. The induced-path argument uses acyclicity to exclude omitted ambient edges. These proof terms are still awaiting type checking.

`core_tree` and `core_root_degree` transport the tree property and the actual surviving third root neighbor to the Fin-labelled residual. There is no independently optimized core, root, path, energy witness, or graph substituted for the original fork.

## Exact decomposition and global targets

`nonpath_source` states that every finite nontrivial nonpath tree is graph-isomorphic to an actual `CoreQuotient.source C u p q`, with C on Fin m, C a tree, and 1 <= C.degree u.

The candidate `decomposesAbove N` targets the exact `GlobalAssembly.DecomposesAbove N` predicate for every natural cutoff N. Its implementation does not use a lower bound on N. An empty vertex type cannot carry a connected tree. The singleton is already a path. The intended range agrees with the previous positive-order energy targets, including order one. Kernel acceptance is still required before this input can be called discharged.

The candidate `universal_conclusion_of_inputs`, `path_minimum_of_inputs` and `path_equality_of_inputs` reuse the checked global assembly with two intended remaining hypotheses:

1. `SmallOrders N`: both energy conclusions for every tree of order 2 <= n < N.
2. `StrictFusionAbove N`: uniform strict energy decrease for every admissible actual source/fused pair of source order at least N.

The declarations target the minimum and equality-up-to-path-isomorphism conclusions for all positive tree orders under these two inputs. The cutoff remains symbolic. No kernel-checked two-input reduction, analytic certificate table, numerical cutoff, exhaustive finite coverage, or unconditional universal energy proof is asserted for this draft.

## Verification and limits

The two new modules are `RadenkovicGutmanArmEmbedding.lean` and `RadenkovicGutmanSourcePresentation.lean`. The endpoint closure includes the previous actual-fork, residual-tree and global-assembly modules. The final receipt must bind every checked source hash and contain only {propext, Classical.choice, Quot.sound} in the printed axiom profiles. Failed development attempts are retained as failures.

The configured verification uses official Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, with official Mathlib caches. Its requested fresh local exports have not run. Such exports would be distinct from a source bootstrap of Mathlib. One module worker, `-j1` and `-DElab.async=false` do not assert a single operating-system thread. Warnings are configured as errors. The prior local Windows prerequisite timeout is not a completed replay, and no new Windows replay is claimed.

At the final source commit in RhudeJJJJ/formal-conjectures:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanSourcePresentation --workers 1 --module-timeout 900 --print-receipt

All 71 preceding RG source modules are retained byte-for-byte. There are now 73 RG source modules and a 21-module endpoint closure. The original statement module at PR head 3654bf2bddc5217f904b7b85207b1091e833de49 remains a separate statement submission with its two placeholders.

The legacy verifier fields `global_rg=NOT_PROVED` and `complete_submission=NOT_SUBMITTED` concern the unconditional universal Lean proof. The separately cited written computer-assisted theorem, kernel acceptance, finite replay, independent review, public supplement, acceptance and merge remain separate statuses.

## Remaining work and submission

The next required action is to read the result of the existing queued run 39283598761, then fix any compiler errors and complete the source-bound axiom audit. Do not start another run merely because this one has not yet produced output. If this endpoint is accepted, its decomposition can be reused and the next mathematical inputs are uniform actual-graph strict fusion and exhaustive finite coverage. Until then the earlier three-input global assembly remains the latest checked global reduction.

[Upstream PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) remains a statement submission. This checkpoint supplies no universal `formal_proof` certificate.
