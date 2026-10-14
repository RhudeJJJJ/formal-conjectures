# Complete Lean disproof of WOWII 396

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization and execution under the author's direction, 14 October 2026.

Written source: *Connected counterexamples to Written on the Wall II Conjecture 396*, 13 October 2026. The full manuscript and source archive are attached to [intake #7308](https://github.com/google-deepmind/formal-conjectures/issues/7308).

## Scope and source conventions

The certificate disproves the proposed 2-domination upper bound for connected finite simple graphs of order greater than two. A 2-dominating set imposes a two-neighbor requirement only on vertices outside the selected set.

The right side is the number of distinct modal degrees plus their common frequency plus the number of edges crossing from degree-at-least-three vertices to the remaining vertices. The source describes the vertex set of the smallest modal degree; its cardinality is precisely that common modal frequency. The lemma frequency_of_mode records the bridge for any modal degree. All possible degrees lie in 0,...,|V|-1, so the finite degree search covers every possible positive frequency.

The witness has exactly two tied modes, 6 and 7, both of frequency eight. It therefore avoids the source's unspecified unique-mode convention. Every degree is at least three, so the boundary edge term is zero. The implementation counts boundary edges by their unique orientation from the high-degree to the low-degree side; it does not double count an undirected edge.

## What the proof checks

The 39 vertices are labeled consecutively in cliques of orders 4,5,6,7,8,9, with offsets 0,4,9,15,22,30. The five bridges are (0,4),(5,9),(10,30),(31,15),(32,22), exactly as in the manuscript under this labeling.

A decreasing parent-height certificate proves actual root reachability and connectedness. Degree calculations give modal set {6,7}, common frequency eight and right side ten.

For each of the six clique parts, two explicitly named vertices have no neighbors outside that part. The proof treats arbitrary selected sets: if both private vertices are selected there are already two selections in the part; otherwise the unselected private vertex needs two selected neighbors in that same part. Summing over the disjoint fibers forces at least twelve selected vertices. A displayed twelve-element set is verified to be 2-dominating. The minimum exists because the full vertex set is 2-dominating. Thus gamma_2=12>10.

There is no exhaustive search through all 2^39 subsets. Finite local facts are checked by ordinary kernel-checked decide; the lower bound for every selected set is proved structurally.

The certificate refutes the complete universal assertion using this finite witness. The manuscript's chordal infinite family, maximum-degree bounds for its copies, unbounded deficit and asymptotic ratio are not formalized here. No minimum-order or worldwide priority claim is made.

## Reproduction and audit

Pins: Lean4.33.1; Mathlib0df444a360eaa60ab8c11dca51a86af692955474.

```sh
lake exe cache get
lake build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/WOWII396Proof.olean Proofs/WOWII396Proof.lean
lake env lean Proofs/WOWII396Audit.lean
```

The full proof and separate audit compile without warnings. All nine audited declarations depend only on [propext, Classical.choice, Quot.sound]. No sorryAx, custom axiom or native-evaluation trust is used. The audit independently defines every invariant and writes the exact proposed repository statement; it imports no upstream placeholder statement.

This environment used the already disclosed narrow readlink adapter: a failed /proc/<own-pid>/exe lookup falls back to /proc/self/exe. The official Lean executable, sources, elaborator and kernel are unchanged. The verified official toolchain archive SHA256 is 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Normal supported installations need no adapter.

SHA256:
- WOWII396Proof.lean: aebd90df59455f00f568b9cf08a4ab6ea2f0f1b465a2d3734e6ca0696c20c16d
- WOWII396Audit.lean: 8933bca7691436fbeb386cbbdc247cb157f8f49e1526bc70b087ed74128871f9

This is an author-workflow kernel certificate, not independent peer review or maintainer acceptance. A formalization upgrades evidence for an existing target; it is not an additional solved conjecture.

