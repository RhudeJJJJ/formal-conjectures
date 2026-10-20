# The first actual strict fusion, with an exact remaining cutoff

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**VERIFIED:** `MinimalFusion.strictFusion_four` proves strict Laplacian-energy decrease for every actual admissible source/fused pair of source order four. The source is a tree and the residual root has positive degree. The same core C, root u and physical arms p and q occur on both sides. No additional energy or strict-fusion premise is assumed. The exact energy drop is `3 - 2*sqrt(2)`.

Checked source [4cc1385bdeaf46ba68c0c66307b99822606c1e5a](https://github.com/RhudeJJJJ/formal-conjectures/commit/4cc1385bdeaf46ba68c0c66307b99822606c1e5a); [successful Linux kernel check](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39409834388), job 118584589830. The full receipt binds all 25 source and output hashes and printed axiom profiles.

## Same source and same fusion

The existing theorem excludes a path source whenever the residual root degree is positive. An arbitrary four-vertex source is relabelled to Fin 4, with a graph isomorphism back to that exact source. The exhaustive four-vertex classification identifies it as the star. It has exactly three leaves. The checked fusion theorem preserves treehood and order and removes exactly one leaf. The checked three-leaf terminal theorem therefore identifies this source's own fused graph as the four-vertex path. Exact energy transport gives source energy 5 and fused energy `2 + 2*sqrt(2)` with the actual mean degree and all eigenvalue multiplicities.

`minimal_parameters` shows that every such source written over Fin m necessarily has m=2, p=q=0 and residual root degree 1. Thus the two physical arms each have one edge. The theorem quantifies over all admissible labelled cores and arms at this order, not just a displayed example. The spectral calculation is inherited from the [previous checked basis](https://github.com/RhudeJJJJ/formal-conjectures/blob/a67bd674ac879e33b06d54123573013d3687c73e/RG_ORDER_FOUR_20261020/README.md); the new work establishes its application to the actual source/fused pair.

## Exact OPEN frontier

Every admissible source has order at least four. The new strict inequality covers every admissible source order below five. Therefore `strictFusionAbove_iff_five` proves `StrictFusionAbove N <-> StrictFusionAbove 5` for each N<=5, and `uniformStrictFusion_iff_cutoff_five` proves uniform actual strict fusion equivalent to `StrictFusionAbove 5`.

An equivalence does not prove either unrestricted proposition. Actual strict fusion at source orders five and above remains OPEN. The complete finite tree basis is still exactly `SmallOrders 5`; no order-five tree-energy result or analytic certificate cutoff is added. With the previously proved source decomposition and global assembly, the universal positive-order minimum and equality characterization remain conditional on `StrictFusionAbove 5`. A larger analytic cutoff N also requires complete finite coverage of every tree at every order 5<=n<N. The separately cited written computer-assisted theorem and alternative hand-proof route are unchanged and have not been independently re-audited.

## Verification and reproduction

One new source module, `RadenkovicGutmanMinimalFusion.lean`. All 76 predecessor RG sources are byte-identical; there are 77 modules in the source package. All 25 modules in this endpoint closure were freshly kernel-exported, warnings as errors, with only propext, Classical.choice and Quot.sound in the printed axiom profiles. `CI_ATTEMPTS.json` preserves development attempts. Official Lean 4.33.1 / commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and retained LeanCert pin 621a43d7cf21f87872392a01e874f2f1dbddc926. Official Mathlib caches were used; this is not a Mathlib source bootstrap. Local exports took 64.472 seconds, excluding dependency preparation. No new Windows/WSL replay is claimed. The earlier bounded Windows Init timeout is retained as environment evidence and was not repeated.

From the checked source with its pinned toolchain and dependencies:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanMinimalFusion --workers 1 --module-timeout 900 --print-receipt

## Submission preparation

[PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) is still a statement submission at head 3654bf2bddc5217f904b7b85207b1091e833de49. Its two universal placeholders are retained. This component supplies no universal `formal_proof` certificate. A current supplement is prepared separately; this record does not claim that it was posted, reviewed, accepted or merged.
