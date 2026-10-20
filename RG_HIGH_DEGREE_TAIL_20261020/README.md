# Actual high-degree graph half-tail

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**VERIFIED actual graph inequality. Universal Lean proof OPEN.** For every finite core C with actual root degree at least 46, every two actual physical arms, and every real y>=1/2,

    phi(y) <= logarithm(source C u p q, fused C u p q, threshold 2, y),
    phi(y) = -log(1+((sqrt(y^2+4)-y)/2)^2)/2.

`HighDegreeTail.graph_lower` has no polynomial positivity or numerical certificate premise. It uses the same core C, root u and arms p+1,q+1. Treehood is not needed for this pointwise inequality. The generic certificate is proved for every real d>=46 and every a,b in [0,1], with P=y+a/y,Q=y+b/y and the original disk center 2-d+i*(y+d/(2y)), radius d/(2y).

Checked [source ba472fc6c49267399bb4e341a352af1a72393dac](https://github.com/RhudeJJJJ/formal-conjectures/commit/ba472fc6c49267399bb4e341a352af1a72393dac); [successful kernel run 39439735351](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39439735351), job 118686120774. All 61 modules in this closure were freshly exported with warnings as errors and only propext, Classical.choice and Quot.sound. The source tree now has 87 RG modules; all 83 predecessor sources are byte-identical. This is not a fresh check of every one of the 87 modules.

## Original polynomial certificate and exact graph bridge

The original producers are `rg_multiarm_tail_halfplane_certificate.py` and `auxiliary_certificates.py:extra_tail(46,1/2)`, with `tail_half_all_d_ge46.json`. The two tensor degrees are (1,14,3,3) and (2,30,6,6), comprising 480 and 4557 coefficients. Their 101 and 833 power terms are reconstructed exactly. The supplied integer scales are 46 and 2116. `TailHalfCertificate.v_accepted` and `k_accepted` evaluate the proved integer Bernstein checker in the Lean kernel with `decide +kernel`; no native evaluator or stored PASS report is trusted. The accompanying symbolic identities prove that the data represent the original forms, rather than an unrelated positive polynomial.

`TailHalfGeometry` proves the original affine identity for |B|^2|N|^2-|A|^2|D|^2, and retains the full error square V^2-r^2*(X^2+T^2). V>=0 and that square margin imply the half-plane bound on every point of the same disk. Denominator nonvanishing follows from the original pole separation. The infinity ratio is bounded by 1/(1+t(y)^2), with the exact original quadratic t(y)^2+y*t(y)=1. Taking logarithms gives phi(y).

`HighDegreeTail` proves the positive rescaling identities h=1/d,u=1/y, including the u^7 factor for the imaginary affine coefficient. It applies the two complete tensor checks on 0<=h<=1/46,0<=u<=2 and 0<=a,b<=1. The actual arm recurrence supplies a=arm(y,p),b=arm(y,q) in [0,1] for every index; the concrete graph determinant quotient and actual Schur disk then give `graph_lower`. No arm sample, replacement graph or pointwise minimum across class payments is used.

`LowStripParity` additionally proves the original physical-parity boxes for every y>0 and every arm index. At index 2*n (odd physical length), arm=y*A with A in [0,1]. At index 2*n+1 (even physical length), arm=(y+A)/(1+y) with A in [0,1]. `actual_parameter` retains the actual index parity while proving exhaustive coverage. These are the actual recurrence enclosures required by the original low-strip producer, not proofs of its twelve sign conditions.

`TailHalfGeometry.infinity_ratio_ge_half` proves |A|^2/|B|^2>=1/2 for every y>0,P>=y,Q>=y. Consequently `tangent_lead_pos` proves the exact original tangent-strip leading coefficient |A|^2-(c^2/4)|B|^2 is strictly positive for every 0<=c<=1/2. This discharges that original condition in all three parity cases. The other three conditions, outside, directed and reserve, remain OPEN; the full error square is retained.

## Remaining high-degree and universal obligations

`strict_fusion_of_lowstrip_escape` discharges the middle and far-tail premises of the previous four-region endpoint. Its only analytic graph premises are now the original low-strip integral lower bound and the original escape pointwise comparison. These two premises remain unproved. The scalar reserve, improper tail primitive and exact escape integral are retained from the preceding checkpoint. This module does not inhabit `OriginalAssembly.Inputs.degreeGeFortysix`.

Here the remaining integral over (0,1/2) includes the original tangent strip 0<d*y<=8/3, the subsequent constant ordinate strip, and their integration. The new pointwise half-tail starts at 1/2 and does not discharge those smaller ordinates.

All seven original input families still require work, including the finite rooted-core censuses and the other degree ranges. `ORIGINAL_CERTIFICATE_OBLIGATIONS.json` records the narrowed frontier. The all-remaining task stays IN_PROGRESS. Uniform strict fusion from source order five and the universal Lean minimum/equality theorem remain OPEN. SmallOrders 5 and the exact actual order-four fusion remain unchanged. No universal formal_proof certificate is supplied.

The separate written computer-assisted theorem is not reclassified by this partial Lean extension. Original files were read selectively; the scalar producer and half-plane producer were fully read in the continuation, and the auxiliary producer was read fully for this step. No full-paper reading, full-family replay or independent peer review is claimed.

## Reproduction and submission preparation

Pinned Lean 4.33.1 / 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and retained LeanCert pin 621a43d7cf21f87872392a01e874f2f1dbddc926. Official dependency caches were used; no new Windows/WSL replay is claimed. The job first exports the 49-module geometry closure from scratch, then extends it to all 61 modules using content- and dependency-checked exports from that same job. Every local module is freshly exported in the current job; no predecessor local binary checkpoint is reused. The full receipts, CI timing, generator provenance and development attempts are retained.

    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project . --endpoint Proofs.RadenkovicGutmanHighDegreeTail --workers 1 --module-timeout 900 --print-receipt

The optional generator in scripts/ accepts --lean-root, --output and --original-source. Reconstructing its data requires the original producer directory; replaying the supplied Lean proof does not. Generator execution alone is not kernel verification.

The replacement description for statement PR #7399 is prepared locally. The two original statement placeholders remain. No upstream description write, complete-proof submission, acceptance or merge is claimed.
