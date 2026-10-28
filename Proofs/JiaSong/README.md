# Jia–Song Conjecture 3.8: complete original refutation

The exact submitted negative endpoint is proved by the actual graph twoCliqueJoin5 (the bowtie). This certificate does not prove corrected_minimum or corrected_equality.

The proof derives connectivity, six edges and the actual distance matrix from graph walks; computes remoteness3/2; factors the actual characteristic polynomial; and sorts the full spectrum [(5+sqrt41)/2,(5-sqrt41)/2,-1,-1,-3] with multiplicities. Its objective4-sqrt41/2 is strictly less than the published bound13/4-sqrt6 by exact rational separating inequalities.

## Checked scope

Five modules, in order: Bounds, Geometry, Spectrum, Full, ExactAudit. All passed strict local Lean4.33.1, pinned Mathlib0df444a360eaa60ab8c11dca51a86af692955474, warningAsError=true, autoImplicit=false, relaxedAutoImplicit=false.

ExactAudit checks definitional equality of the full original target type using rigid shared universe parameters. An unrelated proposition is rejected. The full certificate, remoteness and ordered-spectrum endpoints depend only on propext, Classical.choice, Quot.sound. The original admitted theorem retains sorryAx only as a negative control; the certificate does not depend on it. There is no sorry, custom axiom, native_decide or compiler-trust axiom in the certificate.

The local original-source overlay changes only the umbrella import and three category/AMS attributes. Every mathematical source character is preserved. The replacement imports and both source SHA256 hashes are retained in source-overlay-receipt.json. The original imported definitions and the full target, including the DecidableRel binder and the at-least-two-missing-edges domain, are unchanged.

## Reproduction with untouched original imports

Use the pinned lean-toolchain and lake-manifest in this branch, obtain Mathlib cache, then run:

    lake --wfail build FormalConjectures.Paper.JiaSongRemoteness

Compile the five modules in the above order, with their olean files under .lake/build/lib/lean/Proofs/JiaSong/, using:

    lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false -o .lake/build/lib/lean/Proofs/JiaSong/NAME.olean Proofs/JiaSong/NAME.lean

The bounded ci_loop.py does this against the untouched original module, protects original source and dependency pins, and publishes diagnostics including the actual checked source SHA separately from the workflow event SHA.

Original-import CI40712710434 is queued and has not passed at this snapshot:
https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/40712710434

The complete upstream Build project (including documentation) and Test scripts passed on9c6563ea0bcae3dc4271e88ac9abdcc83ea88613 in run40715503966; all eleven active head checks succeeded and deployment was skipped:
https://github.com/google-deepmind/formal-conjectures/actions/runs/40715503966

The statement repository's upstream full build is a separate check from this external certificate run.

## Sources and credit

Primary source: Jia and Song (2018), Conjecture3.8 and the introductory remoteness/distance-eigenvalue definitions:
https://link.springer.com/article/10.1186/s13660-018-1663-5

Written argument: the linked24August2026 v2 manuscript, family-spectrum proposition and exact H5 comparison:
https://github.com/user-attachments/files/33368385/Jia_Intake_Gebendorfer_2026-10-13.zip

The earlier public6August2026 bowtie/two-clique report remains disclosed by the original module and intake. This is a Lean certification of an existing witness, with no first-disproof, historical-novelty, global corrected-extremum, independent-review-replay or merge claim.
