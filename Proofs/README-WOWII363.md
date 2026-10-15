# WOWII 363 — checked counterexample

Jonas J. Gebendorfer, 15 October 2026. OpenAI Codex assisted with formalization.

The complete certificate is `WOWII363Proof.lean`, theorem
`WOWII363Proof.conjecture363`. The independent statement/definition audit is
`WOWII363Audit.lean`, theorem `WOWII363Audit.exact_target`.

## Exact scope

For a finite simple tree of order greater than two, let S be the vertices adjacent
to a leaf, i(T[S]) the number of isolated vertices in the induced support graph,
and B the vertices of maximum eccentricity. Distances are ambient shortest-path
distances. The average is the mean of min(b in B) dist(v,b) over vertices outside B.
The certificate refutes i(T[S]) + average/2 <= gamma_t(T).
All quantities are finite rational numbers; the rational inequality has the same
meaning as its real-valued counterpart.

The 27-vertex witness has B={5,10}, six isolated supports, positive-distance sum
151 over 25 vertices, and a total dominating set of size nine. Thus the proposed
lower bound is 451/50 > 9 >= gamma_t. We prove the upper bound gamma_t <= 9,
which already refutes the conjecture. We do not claim an exact minimum, minimal
counterexample order, or a formalized infinite family.

The graph and distance table are explicit data. The kernel verifies the table
by constructing walks and proving that every walk has at least the listed
length. Treehood, total domination, support isolation, and the final strict
inequality are all proved. No `sorry`, custom axiom, or `native_decide` is used.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
both final theorems.

## Sources and normalization

- Manuscript and submission: https://github.com/google-deepmind/formal-conjectures/issues/7360
- Manuscript PDF: https://github.com/user-attachments/files/33503424/gebendorfer-wowii363.pdf
- The half coefficient is the explicitly transcribed version from the manuscript
  and the pinned KuberLabs problem record at commit
  `2455820ef9b925c0746cfb72561bca61105b1aa2`, file
  `data/wowii-conjectures.json`. Older archived HTML can omit the multiplier.
  We have not independently recovered that archived glyph.
- The boundary-distance average is the mean positive distance to the SET B
  (Definition 109), not the average over pairs (b,v).
- The distance-certificate argument adapts Gebendorfer's existing WOWII 360
  certificate. The audit additionally checks a negative normalization control:
  vertex 17 has distance 9 to B, while the distance between 5 and 10 is 10.

## Reproduce

This branch retains the Formal Conjectures project configuration. Use official
Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` (the pinned v4.33.1 dependency).
From the repository root run `bash Proofs/check-WOWII363.sh`.
Only the needed dependency modules are fetched and built. The script compiles
both source files with warnings as errors and rejects unexpected axiom output.

The attached `WOWII363-checked.log` records the successful local run on
15 October 2026. In this hosted environment, a small readlink adapter maps only
`/proc/<pid>/exe` to `/proc/self/exe` for executable-path discovery. It does not
change the official Lean binary, kernel, source files, or elaborated proof terms.
It is not needed in ordinary environments.
