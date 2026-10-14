# Complete Lean disproof of WOWII 373

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization, source comparison, execution and submission under the author's direction, 14 October 2026.

Written source: *Peripheral distance and total domination in trees: a counterexample to WOWII 373*, 13 October 2026, attached with source records to [intake #7306](https://github.com/google-deepmind/formal-conjectures/issues/7306). This certificate concerns the explicit WOWII373 statement dated 18 February 2009.

## Statement and witness

For a finite tree of order n>2, the periphery B consists of vertices of maximum eccentricity. The conjecture proposes gamma_t >= (2/3) avg_pos(B,V), with positive-pair average denominator |B|(n-1). Distances are shortest-path distances in the ambient tree, not in an induced peripheral graph. This is not an eccentricity-center or transmission-minimizer definition.

The witness has Fin150 as its vertex type. Vertices 0,...,21 form a path. Vertices 22,...,31 are leaves at0, vertex32 is a leaf at21, and vertices33,...,149 are leaves at20. This is exactly T(5,10,117) in the manuscript under its stated labeling.

The proof constructs actual walks of the candidate distance and proves a lower bound for every walk from an edge Lipschitz certificate. The candidate therefore equals Mathlib's G.dist. The large distance checks are arithmetic proofs by vertex type, not a single massive truth-table certificate. Connectedness and149 edges prove the tree property.

The exact eccentricity formula yields periphery {22,...,32}, of cardinality11. The distance numerator is29514 and denominator1639. The twelve-element set {0,1,4,5,8,9,12,13,16,17,20,21} is total dominating. Consequently gamma_t <=12 < (2/3)(29514/1639) =12+8/1639.

The finite witness fully disproves the universal inequality. Exact total-domination optimality, the full infinite family, the valid replacement inequality and asymptotic coefficient claims in the manuscript are not formalized by this certificate. No minimum-order or global-priority claim is made.

## Reproduce

Pins: Lean4.33.1 and Mathlib0df444a360eaa60ab8c11dca51a86af692955474.

```sh
lake exe cache get
lake build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/WOWII373Proof.olean Proofs/WOWII373Proof.lean
lake env lean Proofs/WOWII373Audit.lean
```

Both files compile without warnings. All nine audited declarations depend only on propext, Classical.choice and Quot.sound; there is no sorryAx, custom axiom or native-evaluation trust. The separate audit independently restates the periphery, average and exact universal statement, without importing an upstream placeholder theorem.

The execution environment used the previously disclosed narrow readlink adapter: a failed /proc/<own-pid>/exe lookup falls back to /proc/self/exe. The official Lean executable, elaborator, sources and kernel are unchanged. Official toolchain archive SHA256:890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Normal supported installations need no adapter.

SHA256:
- WOWII373Proof.lean:442eb9a940dcd57900e2a37350f2274244ea3e35f777b62592759a0969ed904e
- WOWII373Audit.lean:19303c7c8c45e9201ceddb59e9583e0d91aa39a95468dd3a7c5a317df0e4e7fa

A fresh Python reconstruction separately reproduces the graph, all-pairs BFS distances, periphery, numerator, denominator and an exact tree optimizer's value12. That check is a regression audit, not a premise of the Lean disproof. The complete external Lean proof is an author-workflow certificate, not maintainer acceptance or independent peer review.

