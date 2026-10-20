# Actual fusion integrals and the original certificate ranges

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**VERIFIED unconditional bridges; universal Lean proof OPEN.** Four new modules connect the same actual core, root and physical arms to the determinant integral, transport at the moving mean and the fifteen arm classes. The exhaustive seven-range assembly is a conditional theorem. All seven fields of `OriginalAssembly.Inputs` remain unproved in Lean. No inhabitant of `Inputs` and no universal `formal_proof` certificate is supplied.

Checked source [1028e4ca7505545e50387c666ba5c471dd2185ab](https://github.com/RhudeJJJJ/formal-conjectures/commit/1028e4ca7505545e50387c666ba5c471dd2185ab); [successful kernel check](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39422253672), job 118625869622. The receipt binds the 45 freshly exported modules to source/output hashes and printed axiom profiles. All 77 predecessor RG sources are byte-identical; the package now has 81 RG source modules.

## Proved without analytic positivity inputs

`MixedStopLoss.integral_eq` proves the exact stop-loss integral identity for two different finite vertex types with equal order and edge count. Graph isomorphisms preserve stop loss and eigenvalue counts.

`ActualFusionIntegral` discharges order equality, edge equality, integrability and the one-unit count gap for the actual source/fused graph pair. Its integral difference is Lipschitz in the threshold. For every admissible tree source, with actual complete order n,

    LE(source) - LE(fused) = 2 * normalizedIntegral(2 - 2/n).

Thus strict fusion is equivalent to positivity at the actual moving mean. A reserve I(2)>2/n is sufficient. An anchor certificate at threshold 2-2/a transports with exactly |2/n-2/a|. This is a theorem about the same graph pair at two thresholds, not a proof of any stored anchor bound. The original anchor producer additionally requires actual order n<=a; that validity condition remains part of the certificate obligation.

`ClassEnvelope.graph_lower` applies any proved class lower function to the exact graph determinant quotient and actual Schur disk. `integral_lower` integrates the one fixed unordered class pair selected by the actual physical arm lengths. The integrability and class-bound hypotheses are explicit. No pointwise minimum across fifteen different class payments is substituted. Original positive physical lengths P,Q correspond to Lean recurrence indices p=P-1,q=Q-1.

## Conditional assembly and remaining work

The original revised manuscript and component sources were read selectively to identify these exact ranges. No new Python reconstruction or independent full-paper audit was performed.

| Lean input, all OPEN | Original range | Remaining certificate obligation |
| --- | --- | --- |
| degreeOneSmall | d=1,n<=13 | Complete rooted-core census and exact spectral certificates |
| degreeOneMiddle | d=1,14<=n<=52 | Validated anchor integrals and exhaustive residual census |
| degreeOneLarge | d=1,n>=53 | Fifteen class bounds with I(2)>189/5000 |
| degreeTwoThree | d=2 or 3, all n | Uniform class bounds plus complete small exceptions |
| degreeGeFourSmall | d>=4,n<=12 | Complete rooted-core census and spectral certificates |
| degreeFourToFortyfive | 4<=d<=45,n>=13 | 630 degree/class bounds with I(2)>2/13 |
| degreeGeFortysix | d>=46, all n | Compactified degree bounds with I(2)>2/47 |

`inputs_imply_uniform` checks exhaustive composition, exact cutoff payments and actual order bounds. `universal_conclusion_of_original_inputs` then yields the positive-order minimum and equality characterization from `Inputs`, using the previously proved decomposition, terminal result and `SmallOrders 5`. This conditional result does not prove any of its seven inputs. The user's broader request to implement all remaining components is still IN_PROGRESS.

The checked source-order-four strict-fusion result and the equivalence of uniform fusion to `StrictFusionAbove 5` are retained. Complete tree-energy coverage is still `SmallOrders 5`; no order-five census is added. The written computer-assisted theorem is separate from the incomplete Lean formalization. Historical partial component reports are not the scope of the assembled written proof.

## Source inventory and reproduction

`ORIGINAL_CERTIFICATE_OBLIGATIONS.json` records SHA-256 provenance and exact outstanding obligations. The source tree contains 1302 mathematical expected witnesses (16/658/628), plus two degree-two/three summary JSON files. Inventory hashes are not proofs, full readings or fresh replay. The finite middle-degree-one source reports 10600 order/arm instances, 688 anchors covering 10592 instances, and 1203 rooted-core cases over the remaining eight parameter instances. These numbers were read from stored source reports, not newly reproduced.

All 45 modules in this extension closure were freshly kernel-exported with warnings as errors, standard axioms only (propext, Classical.choice, Quot.sound). Official Lean 4.33.1 / commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; retained LeanCert pin 621a43d7cf21f87872392a01e874f2f1dbddc926. Official Mathlib caches were used; no Mathlib source bootstrap or fresh Windows/WSL replay is claimed. Local source exports took 151.425 seconds, excluding dependency preparation. CI_ATTEMPTS.json retains development attempts.

    lake exe cache get
    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanOriginalAssembly --workers 1 --module-timeout 900 --print-receipt

## Submission preparation

PR #7399 remains a statement submission at head 3654bf2bddc5217f904b7b85207b1091e833de49, open and not merged when read this turn. The two original placeholders remain. A current replacement description is prepared locally. No upstream description write, acceptance or merge is claimed in this step.
