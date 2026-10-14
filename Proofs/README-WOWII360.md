# Complete Lean disproof of the explicit half-average version of WOWII 360

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization and execution under the author's direction, 14 October 2026.

Written source: *Center distance and total domination in trees: a counterexample to Graffiti.pc Conjecture 360*, 13 October 2026. The complete manuscript and source records are attached to [intake #7305](https://github.com/google-deepmind/formal-conjectures/issues/7305).

## Exact scope

The statement audited is c(G[S union L]) + avg_pos(C,V)/2 <= gamma_t(G) for finite simple trees of order greater than two. Here L is the leaf set, S its neighboring support set, C the metric center, c counts connected components, and distances are shortest-path distances in the ambient tree. The positive-pair average has denominator |C|(|V|-1); it excludes zero self-distances rather than averaging over all |C||V| pairs.

The older July frozen HTML has a blank multiplier at the relevant position. The public AI-Village raw HTML and Kuber transcription explicitly supply 1/2. This certificate concerns that explicitly transcribed half-average version. It does not assert that every archival rendering contains the same visible coefficient. Source provenance and this ambiguity are recorded in the manuscript and intake.

## Certificate

The vertex type is Fin 41. Vertices 0,...,9 form a path in this order. Vertex 10 is a leaf at 3, vertex 11 a leaf at 6, and vertices 12,...,40 are leaves at 1.

The proof does not merely substitute a precomputed distance table. It defines a candidate distance delta by backbone position and leaf offset, constructs actual walks of that length, and proves that every walk has length at least delta using an edge Lipschitz bound. Consequently G.dist = delta is proved for every pair. Connectedness and the exact edge count then prove that the witness is a tree.

Kernel-checked finite facts determine the center {4,5} and distance sum 321, hence positive average 321/80. A walk-invariant label separates four representatives in the induced leaf/support graph, proving at least four connected components. The set {1,2,3,6,7,8} is verified to be total dominating, proving gamma_t <= 6. Therefore 6 < 4 + 321/160 contradicts the proposed lower bound.

Only these sufficient inequalities are formalized: the certificate does not claim a formal exact value of gamma_t or an exact component count. Nor does it formalize the manuscript's infinite family, packing lower bound, or a minimum-order assertion. A finite witness suffices to refute the complete universal statement.

## Reproduction

Pins: Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

```sh
lake exe cache get
lake build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/WOWII360Proof.olean Proofs/WOWII360Proof.lean
lake env lean Proofs/WOWII360Audit.lean
```

The proof and independent exact-statement audit compile without warnings. All ten audited declarations use only [propext, Classical.choice, Quot.sound]. There is no sorryAx, custom axiom, or native-evaluation trust. The audit independently defines the center, positive average, and leaf/support set; it imports no repository placeholder theorem.

This environment used the already disclosed narrow readlink adapter: a failed /proc/<own-pid>/exe lookup falls back to /proc/self/exe. The official Lean executable, sources, elaborator and kernel are unchanged. Official toolchain archive SHA256: 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Supported normal installations need no adapter.

SHA256:
- WOWII360Proof.lean: bfc8b2e5db14c94850bba10dd4bb997c9306dd741b09a02e2518f8cf3bdad4c2
- WOWII360Audit.lean: 5db2a34692f726c84b678de5964503b22d9a88e136a7ef1d5ae97d2c126b6b00

This is a completed author-workflow kernel certificate. It is not independent peer review, maintainer acceptance, or an additional mathematical closure beyond the existing written result.

