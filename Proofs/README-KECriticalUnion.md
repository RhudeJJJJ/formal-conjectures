# KE critical-union certificate

This companion proves the exact `critical_union_private_neighbors` statement
in PR #7381 for every finite simple graph satisfying the submitted KE equation.
It imports the actual definitions in
`FormalConjectures.WrittenOnTheWallII.GraphConjecture404To407`.
The empty graph is included. There is no connectedness, tree or order hypothesis.

`criticalUnion` is the union of the largest-cardinality critical independent
sets. It must not be silently replaced by the union of all critical sets.
The integer difference, external-neighbor filter and real-valued matching-number
supremum are the actual imported definitions.

For every matching and every vertex set J, each matching edge has total endpoint
weight at least two when the weight is membership in V minus J plus membership
in N(J). Matching edges have disjoint endpoint sets. Summing gives
`2 * |M| <= |V minus J| + |N(J)|`. Passing to the existing real supremum gives
the same inequality for the matching number, without assuming attainment.
The KE equation then bounds every integer difference by `2 * alpha - n`.
Every maximum independent set attains this bound because its neighborhood is
its complement. Thus the maximum-cardinality critical independent sets are
exactly the maximum independent sets, and their actual unions agree.
The rechecked corona exchange theorem excludes one external neighbor.

The critical-set bridge is established literature: Jarden, Levit and Mandrescu,
[Critical and Maximum Independent Sets of a Graph](https://arxiv.org/pdf/1506.00255),
31 May 2015, Theorem 1.6 and Corollary 2.3, with their cited antecedents.
The corona exchange argument and the selected KE specialization also appear
in Gebendorfer's manuscript revision R2 in
[the issue source archive](https://github.com/user-attachments/files/33373103/Gebendorfer_WOWII_404_407_Intake_2026-10-13.zip).
This certificate does not assert new priority for the literature bridge.
Written source: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization
and validation.

Reproduce with the pinned Lean and Mathlib in this checkout:

```sh
lake exe cache get
lake --wfail build FormalConjectures.WrittenOnTheWallII.GraphConjecture404To407
lake env lean -DwarningAsError=true Proofs/KECriticalUnionProof.lean
```

The printed target and helper axiom lists must contain only `propext`,
`Classical.choice` and `Quot.sound`. A successful build of the imported
placeholder-bearing statements alone does not certify the companion proof.
The four numbered tree bounds 404-407 and the converse KE characterization
are outside this certificate. The previously certified corona theorem is
reused and rechecked; it is not counted as another new target.
Repository admission, journal peer review and worldwide priority are separate.
