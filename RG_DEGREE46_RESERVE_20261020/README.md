# Original degree-46 reserve and tail integrals

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**VERIFIED scalar reserve and integration; universal Lean proof OPEN.** Two new modules prove the original transcendental reserve uniformly for every real d>=46, the exact original improper tail integral, tail costs and gains, the scaled escape integral, and conditional composition of the four original regions. All seven fields of `OriginalAssembly.Inputs` are still unproved. The user's request to implement every remaining component remains IN_PROGRESS.

Checked [source 11df1bdd7029fcc3e4870bc6f9eee0b5ac1bfed0](https://github.com/RhudeJJJJ/formal-conjectures/commit/11df1bdd7029fcc3e4870bc6f9eee0b5ac1bfed0); [kernel run 39429074614](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39429074614), job 118649046477. All 47 modules in this closure were freshly kernel-exported, warnings as errors, with only propext, Classical.choice and Quot.sound. The package contains 83 RG modules; all 81 predecessor sources are byte-identical. This is a 47-module fresh check, not a fresh check of all 83 modules.

## Exact original quantities

The source is the revised universal manuscript, equations (other-17)--(other-20), and `proof_components/other_degrees/source/rg_multiarm_large_degree_integral_certificate.py`, with cutoff 46, x0=653/2000 and payment P=21/25. This continuation uses the original t(y), phi(y), J(Y), scaling and physical graph pair.

    t(y) = (sqrt(y^2+4)-y)/2
    phi(y) = -log(1+t(y)^2)/2
    J(Y) = integral over (Y,infinity) of phi(y)
         = -((t-1/t)*log(1+t^2)-2*t+4*atan(t))/2, t=t(Y).

`TailIntegral.phi_integral` proves the improper integral identity for every Y>0, including integrability and the limit at infinity. `tail_cost` proves J(Y)>=-1/(2Y) for Y>0. `tail_gain` proves -J(Y)>=2/(5Y) for Y>=4; `escape_start_gain` applies it at x0*d. `tail_cost_1024` proves the exact reusable cost -1/2048. `escape_integral` proves that the original density P/(d*(1+(y/d)^2)) integrates over [x0*d,10*d] to P*(atan(10)-atan(x0)).

Set A=-(8/3)*log(2)-2*log(3), and

    reserveAt(d) = (A+2/(5*x0))/d-log(2)/2+J(1/2)
                   +P*(atan(10)-atan(x0))+J(10*d).

`LargeDegreeReserve.uniform_transport_paid` proves 2/47 < reserveAt(d)/pi for every real d>=46. The proof uses rational logarithm-series bounds, derivative-based arctangent bounds, exact square-root bounds and rational algebra. No stored Python interval endpoint, decimal approximation or assumed positive numerical margin is imported. The fixed d=46 reserve and its positivity are also proved.

## Remaining graph obligations

`four_region_lower` composes the original gap-free regions (0,1/2), [1/2,x0*d], [x0*d,10*d], and (10*d,infinity). The low-strip integral lower bound and the pointwise middle/tail and escape comparisons are explicit premises. It proves the integral reserve from those premises; it does not prove them. `strict_fusion_of_four_regions` applies this result to the actual source/fused logarithm and actual degree, using its already proved integrability, order and threshold transport. No optimized replacement graph or different arm class is substituted.

The remaining high-degree work is to prove those actual graph low-strip and pointwise bounds from the original polynomial certificates. A generic d>=2 tail beginning at y=1 does not justify a high-degree tail beginning at y=1/2. The low-strip arsinh primitive is not proved in this delivery. The other six analytic/census input families remain OPEN as recorded in ORIGINAL_CERTIFICATE_OBLIGATIONS.json. No inhabitant of Inputs and no universal formal_proof certificate is supplied. SmallOrders 5 and the exact source-order-four fusion are retained; no complete order-five census is added.

The written computer-assisted theorem and its incomplete Lean formalization have different statuses. Original source files were consulted selectively; no new full-paper reading or Python certificate-family replay is claimed.

## Reproduction and submission

Official Lean 4.33.1 / commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; retained LeanCert pin 621a43d7cf21f87872392a01e874f2f1dbddc926. Official dependency caches were used. Fresh local source exports took 136.986 seconds, excluding dependency preparation. CI_ATTEMPTS.json and the complete CI logs retain development failures and the final successful source-bound check. No fresh Windows/WSL compiler result is claimed.

    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanTailIntegral --workers 1 --module-timeout 900 --print-receipt

The replacement description for statement PR #7399 is prepared locally. The two original statement placeholders are retained. No upstream description update, complete-proof submission, acceptance or merge is claimed.
