# Actual pendant forks and their residual tree

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

Verified structural Lean component, 19 October 2026. The unconditional universal RG Lean proof remains open.

## Exact structural result

For every finite nontrivial vertex type V and every tree G on V that is not graph-isomorphic to the path of order card V, `NonpathFork.nonpath_fork_with_residual` supplies a `PendantFork G` with these properties:

- Two actual simple walks in G start at the same root, each with positive length.
- Their endpoints are leaves of G. Every other nonroot arm vertex has degree at most two in G.
- The root has degree at least three in G. The two walk supports intersect only at that root.
- A nonroot arm vertex has no neighbor outside that arm's support.
- The residual is the graph induced from G after removing all nonroot vertices of these very two arms.
- This same induced residual is a tree, and its root has degree at least one.

The result requires no energy inequality, analytic certificate, finite certificate table, assumed decomposition predicate, or numerical cutoff. It is a uniform structural theorem, not a finite enumeration of tree instances. Positive arms include the single-edge case; the residual root is retained.

## Proof and witness identity

`nonpath_has_pendant_fork` first uses the checked maximum-degree-two path characterization to obtain a branching vertex. Among all branching vertices it chooses one farthest from a fixed root. Tree path uniqueness proves `parent_unique`, so at most one of its neighbors points inward and at least two point outward.

For each of those two actual edges, `maximal_outward_path` selects a longest path whose distance from the fixed root increases by exactly one at every step. Finiteness bounds the path length. A maximal path ends in a leaf, since another neighbor would extend it; the uniqueness of an inward neighbor rules out a second backward exit. Every vertex farther than the chosen branch has degree at most two by its maximality. Unique prefixes show that the two paths intersect only at their common root.

`path_nonroot_closed` compares the walk's one or two actual path neighbors with the original degree bound, proving that no additional neighbor can leave the arm. The residual boundary is consequently just the common root. `residual_connected` collapses removed vertices to that root and transports walks to reachability in the residual. Acyclicity follows by induction of the original acyclic graph. A third original root neighbor lies on neither chosen arm and therefore survives in the residual. It witnesses positive residual root degree.

These are the same walks, supports, root and residual throughout. No independently chosen or optimized replacement graph is substituted.

## Remaining source-presentation obligation

This checkpoint completes the actual arm selection and residual admissibility. It does not yet prove `GlobalAssembly.DecomposesAbove N`.

The next missing bridge is the explicit graph isomorphism from G to `CoreQuotient.source C u p q`, with the residual relabelled to Fin m and the chosen arms relabelled to Fin (p+1), Fin (q+1), preserving both attachment edges. The physical arm lengths must be the lengths of these chosen walks. This is a remaining formal proof obligation, not a presumed consequence recorded as proved.

The previously checked global assembly still has three explicit inputs: `DecomposesAbove N`, `StrictFusionAbove N`, and `SmallOrders N`. The uniform strict-energy input, remaining analytic certificates and exhaustive finite coverage remain open. The universal endpoints in the upstream statement module retain their two placeholders. The separately cited written computer-assisted theorem is not independently re-audited by this work.

## Verification and reproduction

- [Immutable source checkpoint](https://github.com/RhudeJJJJ/formal-conjectures/tree/b546e3edbad3e45182649bc798182bf30a7457fe/Proofs/RG_Lean_20261019).
- [Successful 19-module Linux check](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39275364923).
- [Source-bound receipt](linux_nonpath_fork_receipt.json): every local module has a FRESH_KERNEL_EXPORT record and all printed axiom profiles are contained in {propext, Classical.choice, Quot.sound}.
- [Development attempts](CI_ATTEMPTS.json). Failed checks and the local Windows prerequisite timeout are retained as such and are not successful exports.
- [Previously checked conditional global assembly](https://github.com/RhudeJJJJ/formal-conjectures/blob/8ab451d5c04f0ac660b8cda182778c813d22f1b2/RG_GLOBAL_ASSEMBLY_20261019/README.md).

The new endpoint is `Gebendorfer.RadenkovicGutman.NonpathFork.nonpath_fork_with_residual`. Both new modules are checked with the unchanged global-assembly endpoint. The 19-module fresh-export phase took 52.974 seconds; that duration excludes dependency preparation.

The Linux verification uses official Lean 4.33.1, Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474 and the existing LeanCert pin. Official Mathlib caches are used; this is not a source bootstrap of Mathlib. The local exports are fresh. The verifier uses one module worker, `-j1`, `-DElab.async=false`, and warnings as errors, without asserting one operating-system thread.

At the final source commit in RhudeJJJJ/formal-conjectures:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanGlobalAssembly --endpoint Proofs.RadenkovicGutmanForkResidual --workers 1 --module-timeout 900 --print-receipt

The two new modules are `Proofs/RadenkovicGutmanNonpathFork.lean` and `Proofs/RadenkovicGutmanForkResidual.lean`. All 69 prior RG source modules are retained byte-for-byte; the package contains 71 RG source modules. The two new modules and the global assembly share a 19-module checked closure. Axioms must be contained in {propext, Classical.choice, Quot.sound}; the verifier rejects placeholders, native evaluation and custom axioms.

The legacy receipt fields `global_rg=NOT_PROVED` and `complete_submission=NOT_SUBMITTED` concern the unconditional universal Lean proof. They do not erase the existing statement submission or turn this structural result into a universal energy proof.

## Submission

[Upstream PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) remains a statement submission. This structural supplement supplies no universal `formal_proof` certificate. Kernel acceptance, publication of the supplement, independent review, acceptance and merge remain distinct.
