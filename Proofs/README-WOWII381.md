# WOWII 381 — complete Lean proof

Jonas J. Gebendorfer, 15 October 2026. OpenAI Codex assisted with formalization.

The complete theorem is `WOWII381Proof.conjecture381_ratio` in
`WOWII381Proof.lean`. The definition audit is `WOWII381Audit.exact_target`.

For every finite simple tree T of order greater than two, S is the full set of
vertices adjacent to a leaf, N(S) is the union of OPEN ambient neighborhoods,
b is the maximum AMBIENT degree of a support, and z is the number of isolated
vertices in T[N(S)]. The certificate proves z/(b-1) <= gamma_t(T).
Rational arithmetic is exact and equivalent to the real-valued inequality.
The denominator is strictly positive: the proof establishes b >= 2.

The argument formalizes a direct covering proof of Gebendorfer's bound. Every
total dominating set D contains S. Write J for the isolated supports. Each
isolated vertex in T[N(S)] lies in N(J). Cover N(J) by D minus S and, for each
j in J, its neighbors outside D. The latter set has at most b-1 vertices because
D contains a neighbor of j. Hence z <= |D minus S| + |J|(b-1) <= |D|(b-1).
A minimum total dominating set exists because a nontrivial connected graph has
no isolated vertices. This proves the original tree claim without a finite
search or a conjectural intermediate lemma. The generic covering lemma also
applies to arbitrary finite simple graphs under its explicitly stated premises.

The manuscript additionally proves a stronger connected-graph result and
sharpness families. Those additional claims are not asserted as formalized by
the final tree theorem. The audit checks isolation in the induced graph,
N(S) as the union of the ambient neighbor sets, and P4 as a control where N(S)
contains S; it does not silently replace N(S) by N(S) minus S.

Source: Jonas J. Gebendorfer, *Support neighborhoods and total domination:
a proof of Written on the Wall II 381*, 14 October 2026.
Manuscript and original submission:
https://github.com/google-deepmind/formal-conjectures/issues/7334
The manuscript's unavailable original supplement is not claimed as replayed.
The no-adjacent-leaves lemma adapts the same author's WOWII 397c certificate.

## Reproduce

Use official Lean 4.33.1 and the project's pinned Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.
From the repository root run `bash Proofs/check-WOWII381.sh`.
Both files were compiled with warnings as errors, autoImplicit=false, and
relaxedAutoImplicit=false. Final theorems report only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorry`, custom axiom, or
`native_decide` is used. The successful local output is `WOWII381-checked.log`.

In the hosted environment a readlink adapter maps only `/proc/<pid>/exe` to
`/proc/self/exe` for executable-path discovery. It changes neither the official
Lean binary nor the kernel or proof terms; normal environments do not need it.
