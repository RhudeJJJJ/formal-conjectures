# Complete original correlated-escape tensors

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**PROVEN: both complete original integer polynomials are nonnegative on their full four-dimensional unit boxes. Original clearing identities and the actual graph specialization remain OPEN.**

`EscapeDirectedAcceptance.unit_box_nonneg` and `EscapeReserveAcceptance.unit_box_nonneg` prove nonnegativity for every v:Fin 4 -> Real with every coordinate in [0,1]. All 23 directed rows and all 45 reserve rows are included. Their complete Bernstein degree vectors are [22,28,4,4] and [44,52,8,8], with 16,675 and 193,185 coefficients. The full reserve square, original coefficient data and complete parameter box are retained. These are polynomial inequalities on entire boxes, not sampled graph or parameter checks.

The original direct-escape producer uses h=1/d, h<=1/46, x in [653/2000,10], and both arm-error coordinates in [0,1]. The unit coordinates are H=46*h and U=(x-653/2000)/(19347/2000), with the same two arm-error coordinates. The two positively cleared original polynomial identities still have to connect the checked integer tables to the original directed and full-reserve expressions. Positivity of the tables alone does not prove those identities or the graph bound.

## Exact verification scope

The joint endpoint `Proofs.RadenkovicGutmanEscapeTensorAcceptance` succeeded in [run 39517520436](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39517520436), job 118953146159, at [source 244dd5166714ec0baa091b99080c861b6a2f38e6](https://github.com/RhudeJJJJ/formal-conjectures/tree/244dd5166714ec0baa091b99080c861b6a2f38e6/Proofs/RG_Lean_20261019). Its completed receipt contains **130 modules: three fresh kernel exports and 127 explicitly restored earlier-job exports**. The receipt is not a fresh replay of all imports. The additional 183 individual records collected by the job include unused prior exports; they are not a larger endpoint closure.

The prior exports come from the completed records of run 39503978917, job 118908155072 (which reached its 90-minute limit after reserve row 39), and the five successful row jobs in run 39515064640. The importer checks each immutable run/source, the complete archive digest, exact JSON records and output-object hashes. The verifier independently recomputes each current source and full local dependency-closure hash before reuse. Every retained import is labelled PRIOR_VERIFIED_JOB_EXPORT with its original run, job and artifact. No prior export is relabelled fresh. The implementation has exact-restore and changed-origin/record rejection controls.

Official Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 are pinned. The three new modules are checked with warnings as errors. All theorem axiom profiles contain only propext, Classical.choice and Quot.sound; no sorry, custom axiom or native evaluation is used.

## Remaining obligations

Both original symbolic clearing identities and the actual graph escape endpoint are separate obligations. The original tangent-strip signs for all three physical parity boxes, constant-strip chart signs, remaining degree ranges and finite rooted-core census completeness remain OPEN. All seven complete `OriginalAssembly.Inputs` fields and the universal Lean minimum/equality theorem remain OPEN. The written computer-assisted theorem is a separate result.

## Fresh reproduction

With a built Mathlib checkout at the exact pin, official Lean 4.33.1 and the supplied local proof sources:

    python3 -B Proofs/RG_Lean_20261019/verify_extension.py --mathlib-project /absolute/path/to/pinned/mathlib4 --endpoint Proofs.RadenkovicGutmanEscapeTensorAcceptance --workers 2 --module-timeout 3600 --print-receipt

Omitting --resume requests fresh local exports. This can be considerably slower than the reported composition check. Hashing this package is not a new Lean replay. Aletheion was untouched in this phase under the user's explicit instruction.
