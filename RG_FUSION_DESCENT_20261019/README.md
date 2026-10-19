# RG fusion: tree preservation and exact leaf descent

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

Verified partial Lean component, 19 October 2026. The universal Lean path-minimum and equality theorems remain open.

## Exact statement

For every finite vertex type, residual graph C, root u and natural recurrence indices p,q, assume that CoreQuotient.source C u p q is a tree and 1 <= C.degree u. Then CoreQuotient.fused C u p q is a tree on the same number of vertices, and

    leafCount (source C u p q) = leafCount (fused C u p q) + 1.

The physical arm lengths are p+1 and q+1, so both singleton-arm cases are included. The named endpoint is Gebendorfer.RadenkovicGutman.FusionDescent.fusion_tree_and_leaf_count; fusion_leaf_count_strict gives the natural-number descent.

The counted unit is an actual degree-one vertex. The proof first uses the original labelled rewiring with u = Sum.inl u, v = Sum.inr (Sum.inl (Fin.last p)) and w = Sum.inr (Sum.inr 0). It then transfers the count through the existing explicit fusedIso. The positive residual-degree hypothesis keeps the old root from becoming a new leaf.

The generic module also proves connectedness, tree preservation, edge-count preservation and exact leaf descent for the same delete/add operation on an arbitrary finite labelled graph.

## Verification and sources

- [Immutable source checkpoint](https://github.com/RhudeJJJJ/formal-conjectures/tree/136a858c29929133b5cae58c5fe7ccd2e82bbe56/Proofs/RG_Lean_20261019).
- [Successful Linux check at that exact commit](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39243728295).
- [Source-bound Linux receipt](linux_fusion_descent_receipt.json): all 13 local modules in the endpoint closure have FRESH_KERNEL_EXPORT records. Every axiom profile is contained in {propext, Classical.choice, Quot.sound}.
- [Windows generic-module receipt](windows_rewire_topology_receipt.json): the generic rewiring module was also compiled, with eight accepted profiles. This Windows check covers the generic module; the actual-graph closure is covered by the Linux check.
- [Development run history](CI_ATTEMPTS.json). Failed or lint-failing runs are not successful proof checks.

Both platforms use official Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Mathlib binary caches were used; this is not a source bootstrap of Mathlib. The two new files contain no placeholders, custom axioms or native evaluation. The 64 pre-existing RG source modules are retained byte-for-byte; the package now has 66 RG source modules. This run checks the 13-module endpoint closure.

The verifier uses one module worker, -j1, -DElab.async=false and warnings as errors. These are compiler scheduling options, not a claim of one operating-system thread. The legacy receipt fields global_rg=NOT_PROVED and complete_submission=NOT_SUBMITTED concern the universal Lean proof, not the existing statement PR or the separately cited written computer-assisted proof.

## Reproduce

Check out the immutable source commit above in RhudeJJJJ/formal-conjectures. With the pinned toolchain, run from that repository:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanFusionDescent --workers 1 --module-timeout 900

The verifier checks source and dependency hashes, rejects placeholders/native evaluation/custom axioms in the local closure, compiles it and writes its completed receipt. It supports --lean-bin-directory for an installed native toolchain and --print-receipt for CI collection.

## Remaining global obligations

The full Lean path-minimum/equality proof still requires the remaining analytic certificate cases, finite coverage and an unconditional decomposition of nonpath trees. The new result supplies tree preservation and a strict descent after the concrete source presentation is supplied. It does not establish existence of such a presentation for every nonpath tree, or an energy inequality for every fusion.

[Upstream PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) remains a statement submission. Its two target placeholders do not acquire a complete formal_proof link from this partial component. The written computer-assisted theorem, kernel checking, independent mathematical review, acceptance and merge are separate statuses.
