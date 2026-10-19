# Conditional RG global assembly

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

Verified conditional Lean component, 19 October 2026. The unconditional universal Lean proof remains open.

## Exact result and its three inputs

For any natural order cutoff N, the new module proves both path-minimum targets for every positive tree order n, from these explicit hypotheses:

1. SmallOrders N: for every 2 <= n < N and every tree G on Fin n, the path minimum and equality characterization hold.
2. DecomposesAbove N: every nonpath tree G on Fin n with N <= n has a specified graph isomorphism to an actual source C u p q, with C on Fin m and 1 <= C.degree u.
3. StrictFusionAbove N: for every actual source/fused pair with source order at least N, source treehood and positive residual root degree, the fused energy is strictly smaller than the source energy.

Under those inputs, for all n >= 1 and trees G on Fin n:

    laplacianEnergy (pathGraph n) <= laplacianEnergy G

    laplacianEnergy G = laplacianEnergy (pathGraph n)
      iff Nonempty (G is graph-isomorphic to pathGraph n).

The named endpoints are GlobalAssembly.path_minimum_of_inputs and GlobalAssembly.path_equality_of_inputs, under Gebendorfer.RadenkovicGutman. The combined endpoint is universal_conclusion.

These are conditional theorems. None of the three input predicates is proved in this module. In particular, a partial analytic estimate does not supply the uniform StrictFusionAbove input. Finite coverage and the source presentation must satisfy the stated quantifiers. The cutoff N stays symbolic; no numerical cutoff or completed certificate table is asserted.

## What is closed here

The singleton case is proved directly, without using any of the three inputs. The finite base input therefore starts at order two.

For a larger nonpath tree, concrete_descent uses the very source presentation supplied by DecomposesAbove. The corresponding actual fused graph is transported back to Fin n using the source isomorphism and the previously proved exact equality of vertex counts. This same graph is a tree, has exactly one fewer leaf and has strictly smaller energy under StrictFusionAbove. The residual graph, root and physical arm lengths p+1,q+1 are retained, including singleton arms.

Strong induction on the actual leaf count then combines the local step with the checked two-leaf path terminal. In each nonterminal case the lower bound is strict, which proves the equality characterization along with the minimum. An independently selected graph or independently optimized witness is not substituted for the actual fusion.

The module also proves energy_decidable_irrel and energy_iso. They transport the same Laplacian energy between classical and concrete adjacency decision procedures. This resolves the concrete path-decider mismatch without changing the energy definition. Energy sums the absolute deviations of all Laplacian eigenvalues, with multiplicities, from the actual mean degree 2m/n.

## Sources and verification

- [Immutable source checkpoint](https://github.com/RhudeJJJJ/formal-conjectures/tree/997d8d2931b45ea792aa12e812e2ae34153b086e/Proofs/RG_Lean_20261019).
- [Successful Linux check at that commit](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39263424867).
- [Source-bound receipt](linux_global_assembly_receipt.json): all 17 local modules in the endpoint closure have FRESH_KERNEL_EXPORT records and every printed axiom profile is contained in {propext, Classical.choice, Quot.sound}.
- [Development checks](CI_ATTEMPTS.json). Failed checks are retained and are not counted as successful exports.
- [Previous actual-fusion and terminal checkpoint](https://github.com/RhudeJJJJ/formal-conjectures/blob/f31f8c895cea4e87732a326a69065ac34fd395d0/RG_TREE_TERMINAL_20261019/README.md).
- [Original statement module at PR head](https://github.com/RhudeJJJJ/formal-conjectures/blob/3654bf2bddc5217f904b7b85207b1091e833de49/FormalConjectures/Paper/RadenkovicGutmanLaplacianEnergy.lean). Its target includes every positive order and equality up to graph isomorphism. Its two placeholders remain.

The new file is Proofs/RadenkovicGutmanGlobalAssembly.lean. All 68 previous RG source modules are retained byte-for-byte; there are now 69 RG source modules. The new local closure contains no placeholders, native evaluation or custom axioms. Explicit theorem hypotheses remain explicit hypotheses even when the axiom report contains only standard axioms.

The check uses official Lean 4.33.1 (819816b2e0a3bf405af45ae5c7af2491d8f5bee6) and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Official Mathlib caches were used. The 17 local exports are fresh; this is not a source bootstrap of Mathlib. The check uses one module worker, -j1, -DElab.async=false and warnings as errors, without asserting one operating-system thread.

## Reproduce

At the immutable source commit in RhudeJJJJ/formal-conjectures:

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanGlobalAssembly --workers 1 --module-timeout 900 --print-receipt

The verifier checks pins, source/dependency/output hashes and axiom profiles. The legacy receipt fields global_rg=NOT_PROVED and complete_submission=NOT_SUBMITTED concern the unconditional universal Lean proof, not this conditional component or the existing statement submission.

## Remaining obligations and submission

The formal composition is now available under its exact inputs. Discharging DecomposesAbove, StrictFusionAbove and SmallOrders remains the route to an unconditional universal Lean proof. The remaining analytic certificates and exhaustive finite coverage are part of those inputs.

[Upstream PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) remains a statement submission. This conditional supplement supplies no universal formal_proof certificate. The separately cited written computer-assisted theorem, kernel checks, independent review, acceptance and merge remain distinct.
