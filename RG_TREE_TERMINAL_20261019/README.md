# RG tree terminal and final fusion step

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

Verified partial Lean component, 19 October 2026. The universal Lean path-minimum and equality theorems remain open.

## Exact statements

For every finite nontrivial vertex type and every tree G,

    leafCount G = 2 + sum_v (G.degree v - 2),

where subtraction is natural subtraction at each vertex. Moreover,

    leafCount G = 2
      iff Nonempty (G is isomorphic to pathGraph (Fintype.card V)).

The equivalent maximum-degree condition is proved, rather than assumed. Every nonpath tree in this range has at least three leaves. The singleton tree is excluded from the two-leaf characterization: its leaf count is zero. The two-vertex case is included.

For every actual RG source presentation C,u,p,q with source C u p q a tree and 1 <= C.degree u,

    branchingExcess (source C u p q)
      = branchingExcess (fused C u p q) + 1.

Thus the source cannot already be a path. If it has exactly three leaves, the actual fused graph is isomorphic to the path of its order. Physical arm lengths are p+1 and q+1, including both singleton-arm cases.

The new modules are Proofs.RadenkovicGutmanTreeTerminal and Proofs.RadenkovicGutmanFusionTerminal. The principal endpoints are tree_two_leaves_iff_path, nonpath_has_three_leaves, fusion_branching_excess and three_leaf_fusion_is_path, in the corresponding Gebendorfer.RadenkovicGutman namespaces.

## Proof and counted units

A leaf is one actual vertex of degree one. The degree excess is summed over all actual vertex labels. Equality with a path means a graph isomorphism, with the same vertex count.

The degree-sum formula and the tree edge count give the exact leaf identity. For a path between two leaves in a graph of maximum degree two, its subgraph already has every neighbor of each of its vertices. Connectedness therefore makes it spanning. Minimal connectedness of a tree then identifies its edges with the original tree. Mathlib's explicit path-graph isomorphism supplies the terminal isomorphism.

The fusion corollaries compose this characterization with the previously checked actual source/fused tree preservation and exact one-leaf descent. They retain the original source/fused definitions and explicit rewiring isomorphism.

## Verification and reproducibility

- [Immutable source checkpoint](https://github.com/RhudeJJJJ/formal-conjectures/tree/70fb8fc8b817e3a61c1d4f0dd59c922106452b69/Proofs/RG_Lean_20261019).
- [Successful Linux check at that commit](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39256915486).
- [Source-bound receipt](linux_fusion_terminal_receipt.json): all 15 local modules in the endpoint closure have FRESH_KERNEL_EXPORT records. Every printed axiom profile is contained in {propext, Classical.choice, Quot.sound}.
- [Development checks](CI_ATTEMPTS.json). Earlier compiler- or lint-failing runs are not counted as successful checks.
- [Previous actual fusion checkpoint](https://github.com/RhudeJJJJ/formal-conjectures/blob/c54312b2885e0799160f54653f2c52b9bc23cc06/RG_FUSION_DESCENT_20261019/README.md).

The pinned toolchain is official Lean 4.33.1 (819816b2e0a3bf405af45ae5c7af2491d8f5bee6), with Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Official Mathlib caches were used. This is a fresh export of the 15 local modules, not a source bootstrap of Mathlib. The two new files contain no placeholders, custom axioms or native evaluation. The 66 previous RG source modules are retained byte-for-byte; there are now 68 RG source modules.

From the repository at the immutable source commit, run:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanFusionTerminal --workers 1 --module-timeout 900 --print-receipt

The verifier checks pins, source/dependency/output hashes and axiom profiles. Compiler flags include -j1, -DElab.async=false and warnings as errors. These specify scheduling, not one operating-system thread. A slow native Windows attempt was intentionally interrupted during development; no Windows verification of the new terminal closure is claimed.

## Remaining universal obligations and submission

The new result closes the nontrivial two-leaf terminal characterization and the final three-leaf fusion case once an actual RG source presentation is supplied. It does not establish such a presentation for every nonpath tree or an energy inequality for every fusion.

The universal Lean path_minimum and path_equality proofs still require unconditional nonpath decomposition, remaining analytic certificate cases, exhaustive finite coverage and final composition. The legacy receipt fields global_rg=NOT_PROVED and complete_submission=NOT_SUBMITTED refer to that universal Lean proof, not the existing statement PR or the separately cited written computer-assisted theorem.

[Upstream PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) remains a statement submission. This supplement is a checked partial proof, without a universal formal_proof certificate. Written proof status, kernel checking, independent review, acceptance and merge remain separate.
