# WOWII 352 — complete finite counterexample

Jonas J. Gebendorfer, 15 October 2026. OpenAI Codex assisted with formalization.
The 18-vertex witness is the r=3 member of Gebendorfer's 30 August 2026 note;
it is isomorphic to Siddhant Dubey's earlier public witness. No first-refutation
or new global-minimality claim is made.
Source note and prior-work links:
https://github.com/google-deepmind/formal-conjectures/issues/7264

`WOWII352Proof.conjecture352` refutes the literal closed-neighborhood claim
for trees of order greater than two: gamma_t(T) >= components(T[N[D2]]) plus
the ceiling of half the average eccentricity of the maximum-degree vertices.
All degrees and distances are measured in the ambient tree. The closed set
explicitly includes D2, as the source's printed union requires.

The kernel verifies the 18-vertex tree, the actual shortest-path distance table,
a total dominating set of size seven, and the unique maximum-degree vertex 0
whose eccentricity is eleven. It proves at least two components in the induced
closed degree-two neighborhood by two vertices that cannot be connected there.
Thus the claimed lower bound is at least 2+6=8, while gamma_t <= 7.
These bounds suffice; an exact minimum, exact component count, minimal witness
order, and the infinite family are not asserted as formalized here.

The distance proof adapts the WOWII 363/360 walk-certificate method.
The audit identifies the closed neighborhood as D2 union the open neighborhood
union, checks the separator vertex, and restates the entire universal negation.

## Reproduce

Use official Lean 4.33.1 and pinned Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
Run `bash Proofs/check-WOWII352.sh` from the repository root.
Proof and audit compiled with warnings as errors and implicit variables disabled.
Every printed theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, custom axiom, or `native_decide` occurs in either source.
The successful local output is `WOWII352-checked.log`.
The hosted executable-path readlink adapter described in README-WOWII363.md
was used; the official Lean binary and kernel were unchanged.
