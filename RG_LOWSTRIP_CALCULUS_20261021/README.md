# Original RG low-strip analytic frontier

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**VERIFIED analytic and conditional actual-graph components. Universal Lean proof OPEN.**

The joint 74-module closure at [source d8d6a616b87213e514519e01e67a32d304a22767](https://github.com/RhudeJJJJ/formal-conjectures/tree/d8d6a616b87213e514519e01e67a32d304a22767/Proofs/RG_Lean_20261019) was freshly exported in [run 39516155963](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39516155963), job 118948681270. It uses official Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, warnings as errors and only propext, Classical.choice and Quot.sound. All 87 predecessor sources at 658a1eff4995058c71f0873f623ac48f50448136 are byte-identical. The source commit contains 223 RG modules; this is not a fresh check of all of them.

## Checked original calculus

For s>0, P(s)=s*log(2+sqrt(s^2+4))-s*log(s)+2*arsinh(s/2) equals s*arsinh(2/s)+2*arsinh(s/2), and P'(s)=arsinh(2/s). The extension is continuous at zero, with P(0)=0. Integrability at the singular endpoint is proved by comparison with the checked scalar logarithmic kernel. For every B>0, the integral from 0 to B of arsinh(2/s) is P(B). In particular it equals (8/3)*log(2)+2*log(3) at B=8/3.

`LowStripPrimitive.original_graph_lowstrip_lower` proves the original graph integral payment

    (-(8/3)*log(2)-2*log(3))/d-log(2)/2

on (0,1/2), under the two original pointwise graph comparisons on (0,8/(3*d)] and [8/(3*d),1/2]. Scaling, integrability and interval assembly are proved. The intervals leave no gap and the singular endpoint is not dropped.

## Checked original geometry and coverage

`QuadraticDisk.convex_nonneg` proves the original strictly convex disk criterion. The outside condition is gradientSq-4*(a*r)^2>=0. The directed sign and the full reserve directed^2-16*(a*r)^2*gradientSq are retained. These three conditions imply nonnegativity on every point of the same disk.

`LowStripGeometry` proves the exact source Apollonius quadratic identity and the actual tangent graph quotient comparison under those signs. `LowStripCoordinates.tangent_coordinate_exists` proves that s=4*c/(1-c^2),0<c<=1/2 covers every 0<s<=8/3; it uses the exact inverse c=s/(2+sqrt(s^2+4)). `LowStripConstantGeometry` proves positivity of the original constant-strip leading coefficient and its actual graph bound under the original outside/directed/full-reserve signs, at target modulus 1/2.

`LowStripSignAssembly.strict_fusion_of_original_sign_families` reduces actual high-degree strict fusion to three explicit remaining families: original tangent signs, original constant-strip signs, and the original correlated escape signs. Every sign is evaluated on the same core C, root u and physical arms p+1,q+1. The original c/2 tangent target, 1/2 constant target, parameter intervals and complete error squares are retained. No replacement graph, arm sample, separate numerator/denominator extrema or stored Python PASS report is used as a proof premise.

`HighDegreeInputFromSigns.normalized_lower_of_original_sign_families` additionally proves the exact original target 2/47 < normalizedIntegral C u p q 2 for every actual root degree >=46, conditional on those same three original sign families. This retains the normalized margin required by `OriginalAssembly.Inputs.degreeGeFortysix`; proving strict fusion alone would not supply that field. Four-region integral assembly and the scalar reserve pay the original margin. No complete Input field is supplied until the remaining original sign families are established.

`LowStripParityBridge.actual_signs_of_three_parity_boxes` transfers all three original sign conditions from the odd/odd, odd/even and even/even source boxes to every actual physical arm pair. The even/odd case follows from proved coefficient symmetry. The original alpha=y*A and alpha=(y+A)/(1+y) arm forms, complete parameter boxes and the same graph degree are retained. Its normalized-target corollary uses exactly those box families; their polynomial sign certificates remain inputs.

## Exact remaining scope

Those sign families are inputs to this checkpoint. It does not supply their polynomial certificates or positive clearing identities. The original tangent signs in all three physical parity cases and the original constant-strip chart signs still require work. The separate correlated-escape certificate run has its own evidence; its later failing, pending or skipped endpoints cannot be inferred from this receipt.

All seven complete `OriginalAssembly.Inputs` fields remain OPEN, including remaining degree ranges and rooted-core census completeness. Uniform strict fusion from source order five and the universal Lean path-minimum/equality theorem remain OPEN. SmallOrders 5 and actual order-four fusion are retained. The separate written computer-assisted theorem is unchanged. No full 1302-witness replay, full-paper reading, peer review, acceptance, merge or universal formal_proof certificate is claimed.

## Reproduction

    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project /absolute/path/to/pinned/mathlib4 --endpoint Proofs.RadenkovicGutmanLowStripCombined --workers 1 --module-timeout 600 --print-receipt

Use `combined_kernel_receipt.json` and `combined_verification.json` for the current joint source. The earlier three-module calculus and 51-module convex receipts are preserved as historical component checks at their own immutable sources; their counts are not added to the 74-module job. Original producer hashes and reading scope are in `original_source_provenance.json`.
