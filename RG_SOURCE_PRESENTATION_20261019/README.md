# Actual source isomorphism and two-input RG assembly

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**VERIFIED STRUCTURAL CLOSURE AND CONDITIONAL ENERGY RESULT.** `SourcePresentation.decomposesAbove N` proves the exact `GlobalAssembly.DecomposesAbove N` predicate for every natural cutoff N, without any additional hypothesis. The global path-minimum and equality conclusions now have two remaining explicit inputs, `SmallOrders N` and `StrictFusionAbove N`. The unconditional universal energy theorem remains unproved in Lean.

Checked source: [ad06b651590a02d406dd75f83c8ff7eec06e5636](https://github.com/RhudeJJJJ/formal-conjectures/commit/ad06b651590a02d406dd75f83c8ff7eec06e5636). The [successful Linux check](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39286747536), job 118175385639, freshly exported the full 21-module endpoint closure on 19 October 2026. This evidence and the submission supplement were prepared on 20 October. See `linux_source_presentation_receipt.json` for the source and output hashes and all printed axiom profiles.

## Exact target and same witnesses

`SourcePresentation.sourceIso` relabels the very `PendantFork G` from the [previous checked fork/residual checkpoint](https://github.com/RhudeJJJJ/formal-conjectures/blob/6b902831b8ec33771ccfb6df525dc21a0775cbad/RG_NONPATH_FORK_20261019/README.md). Its actual induced residual becomes the core on Fin m. Its two actual walk tails become Fin (p+1) and Fin (q+1), in their original path order. Physical arm lengths are exactly the lengths of those same selected walks; label zero is each actual attachment neighbor. Single-edge arms are included.

The vertex map is bijective. Its proof checks all nine adjacency blocks: core/core, both path blocks, both root attachments in both directions, and absence of cross-arm edges. Acyclicity proves the actual walk subgraph is induced, excluding omitted ambient edges. `core_tree` and `core_root_degree` transport treehood and the same surviving third root neighbor to the labelled residual. The proof retains the selected core, root, arms, attachment edges and original graph.

`nonpath_source` states that every finite nontrivial nonpath tree is isomorphic to an actual `CoreQuotient.source C u p q`, where C is a tree on Fin m and 1 <= C.degree u. The subsequent `decomposesAbove` discharges the exact assembly input for every N. An empty vertex type cannot carry a connected tree, and the singleton is already a path. No spectral, certificate, finite-coverage or cutoff assumption enters this structural result.

## Two remaining inputs

`SourcePresentation.universal_conclusion_of_inputs`, `path_minimum_of_inputs` and `path_equality_of_inputs` reuse the checked global assembly and prove, for every positive n and every tree T on Fin n:

    laplacianEnergy (pathGraph n) <= laplacianEnergy T
    laplacianEnergy T = laplacianEnergy (pathGraph n)
      iff Nonempty (T is graph-isomorphic to pathGraph n)

Their two explicit hypotheses, at a symbolic cutoff N, are:

1. `SmallOrders N`: both conclusions for every tree of every order 2 <= n < N.
2. `StrictFusionAbove N`: for every m, C, u, p and q, if the actual source has order at least N, is a tree and has 1 <= C.degree u, then the energy of that same fused graph is strictly less than the energy of that source.

The existing assembly transports the actual fused graph back to Fin n, preserves order and treehood, and uses its exact one-leaf descent. The singleton conclusion remains proved directly. Energy retains all Laplacian eigenvalues, with multiplicities, centered at the actual mean degree 2m/n; the minimum and equality convention match the original statement. No numerical cutoff, completed analytic certificate table, exhaustive finite coverage, or unconditional universal energy proof is supplied here.

## Verification and reproducibility

The two new modules are `RadenkovicGutmanArmEmbedding.lean` and `RadenkovicGutmanSourcePresentation.lean`. All 71 preceding RG source modules are unchanged; there are now 73 source modules. The endpoint closure contains 21 freshly exported local modules, including the unchanged fork, residual and global-assembly sources. Export time was 80.428 seconds, excluding dependency preparation. All recorded axiom profiles are contained in {propext, Classical.choice, Quot.sound}; there is no sorryAx or added axiom in the checked closure. Warnings were errors.

Toolchain: official Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; retained LeanCert pin 621a43d7cf21f87872392a01e874f2f1dbddc926. Official Mathlib caches were used. Fresh local kernel exports are distinct from a source bootstrap of Mathlib. One module worker, `-j1` and `-DElab.async=false` do not imply one operating-system thread.

At the checked source commit in RhudeJJJJ/formal-conjectures:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanSourcePresentation --workers 1 --module-timeout 900 --print-receipt

`CI_ATTEMPTS.json` retains both failed development checks and the successful check. The first failure concerned the graph-connectedness API; the second concerned rewriting a dependent Fin cardinality. Neither is counted as a successful export. During a reported GitHub Actions incident the jobs API continued to say queued after execution had completed. Actual compiler logs, timestamps and final success were checked separately; queued metadata was not proof that no compiler ran.

The Windows API probe timed out at 60 seconds, and a probe without Mathlib timed out at 30 seconds. The existing Ubuntu environment failed before its discovery shell with Wsl/Service/E_UNEXPECTED. These are recorded environment observations, not completed local proof replays or mathematical counterexamples. No new successful Windows replay is claimed. The initial [unverified draft](https://github.com/RhudeJJJJ/formal-conjectures/blob/623327a201fc20b8f6be488e6b2d66152890f1c9/RG_SOURCE_PRESENTATION_DRAFT_20261019/README.md) is retained as a historical draft, superseded for current status by this checked source.

## Submission and remaining work

[Upstream PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) remains a statement submission at statement head 3654bf2bddc5217f904b7b85207b1091e833de49, with its two original placeholders. This external checkpoint supplies a checked structural closure and a conditional two-input energy reduction. It supplies no universal `formal_proof` certificate. Submission, acceptance and merge are separate events.

The next mathematical obligations are uniform actual-graph strict fusion, including the remaining analytic certificates, and exhaustive finite coverage below the chosen cutoff. Reuse the proved decomposition and checked global assembly. The legacy receipt fields `global_rg=NOT_PROVED` and `complete_submission=NOT_SUBMITTED` concern the unconditional universal Lean proof. This work does not change or independently re-audit the separately cited written computer-assisted theorem or the alternative hand-proof route.
