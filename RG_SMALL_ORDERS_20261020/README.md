# Exact small-order basis and the conditional cutoff-four reduction

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**VERIFIED:** `SmallOrders.smallOrders_four` discharges the exact `GlobalAssembly.SmallOrders 4` predicate. Both the path-minimum and equality-up-to-path-isomorphism statements are proved for every tree at every positive order below four. The already checked singleton case is reused. The new global endpoints have the single explicit hypothesis `StrictFusionAbove 4`. That hypothesis is still unproved; the unconditional universal Lean proof remains OPEN.

Checked source: [18238b02e819a1e9598bb104f6453589eb6baa4c](https://github.com/RhudeJJJJ/formal-conjectures/commit/18238b02e819a1e9598bb104f6453589eb6baa4c). [Successful Linux check](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39389761101), job 118518154443. See `linux_small_orders_receipt.json` for all 22 source-bound fresh exports and printed axiom profiles.

## Exact range and proof

For n = 2 or 3, every degree in a graph on Fin n is less than n, so every degree in a tree is at most two. The checked tree-terminal theorem provides an isomorphism to the path of the same order. The existing energy-isomorphism theorem then gives the minimum and equality conclusions. This covers every labelled tree in those orders, without sampling or floating-point eigenvalue calculations.

`smallOrders_four` has type `GlobalAssembly.SmallOrders 4` with no extra premise. `smallOrders_of_le_four` covers every cutoff N <= 4. For an arbitrary N, `smallOrders_iff_from_four` says exactly that `SmallOrders N` is equivalent to supplying both energy conclusions for every tree at each order 4 <= n < N. No finite coverage at a larger cutoff is asserted.

## Global reduction and structural threshold

`universal_conclusion_of_strictFusion_four`, `path_minimum_of_strictFusion_four` and `path_equality_of_strictFusion_four` prove the original positive-order conclusions conditionally on `StrictFusionAbove 4`. They reuse the [proved source decomposition](https://github.com/RhudeJJJJ/formal-conjectures/blob/9c605d6057233b683ab6bd6b581d2efb6f208217/RG_SOURCE_PRESENTATION_20261019/README.md) and the checked global assembly.

Every admissible core with positive root degree has at least two vertices. Each of its two physical arms has at least one vertex beyond the root. `four_le_source_order` therefore proves that every admissible actual source has order at least four. `uniformStrictFusion_iff_cutoff_four` proves that `StrictFusionAbove 4` is equivalent to strict energy decrease on every admissible actual source/fused pair, without an order cutoff. The same C, u, p and q occur on both sides. This is an equivalence of hypotheses, not a proof of the energy inequality.

Four is the structural lower bound, not a numerically certified analytic cutoff. A method that establishes fusion only above a larger cutoff N still needs complete finite coverage at every order 4 <= n < N. The previous symbolic two-input reduction remains valid. The written computer-assisted theorem and alternative hand-proof route are not changed or independently re-audited.

## Verification

One new module, `Proofs/RadenkovicGutmanSmallOrders.lean`, is added. All 73 preceding RG source modules are unchanged; the package contains 74 RG modules. The full endpoint closure has 22 freshly kernel-exported local modules. All printed axiom profiles are contained in {propext, Classical.choice, Quot.sound}. There is no sorryAx, custom axiom or native evaluation certificate in this closure. Warnings are errors.

Official Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6; pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; retained LeanCert pin 621a43d7cf21f87872392a01e874f2f1dbddc926. Official Mathlib caches were used. Fresh local exports are distinct from a Mathlib source bootstrap. One module worker, `-j1` and `-DElab.async=false` do not imply one operating-system thread. Local exports took 64.164 seconds, excluding dependency preparation.

From the checked source commit, after obtaining the pinned toolchain and Mathlib dependencies:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanSmallOrders --workers 1 --module-timeout 900 --print-receipt

`CI_ATTEMPTS.json` records actual development checks. Earlier Windows startup timeouts and the failed WSL discovery are retained in the previous checkpoint; they were not repeated and no new successful Windows replay is claimed.

## Submission boundary

[PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) is a statement submission at head 3654bf2bddc5217f904b7b85207b1091e833de49. Its original two placeholders are not replaced by this conditional result. This checkpoint supplies no universal `formal_proof` certificate. Publishing this evidence, supplementing that PR, independent review, acceptance and merge are separate events.

The next mathematical obligation is the exact uniform strict-fusion inequality, or fusion above a larger certified cutoff together with all remaining finite orders from four up to that cutoff. The first nonpath energy comparisons occur at order four.
