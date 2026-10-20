# Exact first nonpath energy case and complete tree coverage below five

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**VERIFIED:** `OrderFour.smallOrders_five` proves the exact `GlobalAssembly.SmallOrders 5` predicate without any extra premise. Both the energy minimum and equality up to path isomorphism now hold for every labelled tree at every positive order below five. The new global endpoints have the single unproved hypothesis `StrictFusionAbove 5`. The unconditional universal Lean proof remains OPEN.

Checked source: [04922f451294d96bb9a2c00d60ee0e47e487e4d7](https://github.com/RhudeJJJJ/formal-conjectures/commit/04922f451294d96bb9a2c00d60ee0e47e487e4d7). [Successful Linux check](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39407148136), job 118575734511. `linux_order_four_receipt.json` binds every checked source and all printed axiom profiles.

## Actual graph spectra and energies

`FourVertexSpectrum` works with the actual graph Laplacians of `pathGraph 4` and `starGraph (0 : Fin 4)`. Their characteristic polynomials are exactly

    P4: X * (X - 2) * (X^2 - 4*X + 2)
    K13: X * (X - 1)^2 * (X - 4).

The complete root multisets, including multiplicities, are respectively

    [0, 2 - sqrt(2), 2, 2 + sqrt(2)]
    [0, 1, 1, 4].

The checked spectral-sum bridge identifies these roots with all actual Laplacian eigenvalues. The actual mean degree is 3/2 in both graphs. Their energies are exactly 2 + 2*sqrt(2) and 5. The strict inequality follows from the exact square-root identity and its nonnegative sign. No floating-point approximation or external root oracle is used.

The path characteristic polynomial reuses the all-length actual path determinant recurrence. The star polynomial is obtained from its actual four-by-four Laplacian. Repeated eigenvalue 1 is retained twice. The computation does not replace either graph or its centering with an independently chosen spectrum.

## Exhaustive coverage

If a four-vertex tree is not a path, the checked maximum-degree-two theorem forces a vertex of degree at least three. The universal degree bound forces its degree to be exactly three, so it is adjacent to every other vertex. The star centered there is a connected subgraph of the given tree. Tree minimality makes that star the whole original tree. An explicit graph isomorphism moves its center to zero. These arguments cover all labelled four-vertex trees without enumerating a sample.

Exact energy transport proves `conclusion_four`, including strictness for each nonpath tree and equality precisely for path isomorphisms. The [previous complete basis below four](https://github.com/RhudeJJJJ/formal-conjectures/blob/48e06634d7bf6281ebef6f8b8ccacf0472d79d45/RG_SMALL_ORDERS_20261020/README.md) then gives `SmallOrders 5`. `smallOrders_iff_from_five` identifies the remaining finite obligation at any larger cutoff N as every tree at every order 5 <= n < N.

This is a complete finite energy result and a conditional global reduction, not a uniform pendant-fusion proof. No general source/fused inequality is inferred just from the path/star calculation. The global assembly still preserves the actual source/fused witnesses. Its source decomposition is already proved for every cutoff.

## Verification and reproduction

Two new modules, `RadenkovicGutmanFourVertexSpectrum.lean` and `RadenkovicGutmanOrderFour.lean`, are added. All 74 previous RG sources are unchanged; the source package now contains 76 modules. All 24 modules in this endpoint closure were freshly kernel-exported, with warnings as errors and only {propext, Classical.choice, Quot.sound} in all printed axiom profiles. Source and output hashes are in the receipt. Development attempts are retained in `CI_ATTEMPTS.json`.

Official Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; retained LeanCert pin 621a43d7cf21f87872392a01e874f2f1dbddc926. Official Mathlib caches were used. Fresh local exports are not a Mathlib source bootstrap. One module worker, `-j1` and `-DElab.async=false` do not imply one operating-system thread. Local exports took 89.547 seconds, excluding dependency preparation. No new Windows or WSL proof replay is claimed.

From the checked source commit with its pinned toolchain and dependencies:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanOrderFour --workers 1 --module-timeout 900 --print-receipt

## Submission and OPEN frontier

[PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) remains a statement submission at original statement head 3654bf2bddc5217f904b7b85207b1091e833de49. Its two universal placeholders are not replaced by this finite result and conditional reduction. No universal `formal_proof` certificate is supplied. Public proof evidence, a PR supplement, independent review, acceptance and merge remain distinct events.

The next mathematical obligation is `StrictFusionAbove 5`, or fusion beyond a larger certified cutoff N plus exhaustive finite coverage at 5 <= n < N. The separately cited written computer-assisted theorem and alternative hand-proof route are not changed or independently re-audited.
