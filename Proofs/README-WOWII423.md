# Complete Lean proof of WOWII 423 and its additive cut strengthening

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization, 13 October 2026.

The external proof covers all finite simple graphs, without a finite-order cutoff. Its main cut theorem needs only one crossing edge. The source corollary covers every connected graph of order greater than three, including regular graphs. The proof uses two maximal independent extensions and explicit cardinality-preserving transport to induced graphs. It does not replace independent domination or independence number with a bespoke finite checker.

## Source fidelity

Written source: *Independent Domination Across a Vertex Cut and a Resolution of WOWII Conjecture 423*, 1 September 2026, Theorem 1.1 and its corollary. The complete manuscript, frozen primary HTML and verification scripts are publicly attached to [intake #7272](https://github.com/google-deepmind/formal-conjectures/issues/7272).

Entry 423 dates from 8 December 2010. Its surviving comparison glyph is blank. We explicitly use the non-strict upper-bound reading: the reverse direction fails on K4, and strict `<` fails on the sharpness family. The Lean certificate proves this specified reading; it does not establish historical author intent or exclusive priority. The closed neighborhood is A together with all vertices adjacent to some vertex in A. Both endpoints must lie in the maximum-degree set for the `internalEdges` term.

## Reproduction

The inherited `lean-toolchain` pins Lean 4.33.1; `lake-manifest.json` pins Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The upstream base is e47a327f7befa3df97115abf87aa8ed35c381f1f. Its three imported graph API files match the tested local source blobs exactly.

Run from the repository root:

```sh
lake exe cache get
lake build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/WOWII423Proof.olean Proofs/WOWII423Proof.lean
lake env lean Proofs/WOWII423Audit.lean
```

The proof and audit both exit 0 without warnings. All five audited declarations use exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, custom axiom, native evaluation dependency or graph-order cap. The audit independently writes the full source statement without the proof's neighborhood abbreviation, and proves the original subtract-one form of the cut bound. Unrelated placeholder statements in the repository are not proof dependencies.

In the execution environment used here, the previously documented executable-path compatibility adapter changes only a failing readlink of the current process executable to its `/proc/self/exe` alias. Lean's executable, sources, elaborator and kernel are unchanged. Ordinary supported Lean installations do not need this adapter.

## Mathematical structure

1. A maximum-cardinality independent extension of a seed is maximal within its prescribed region and therefore dominates that region.
2. Extend a fixed outside endpoint of a crossing edge to an independent set I in V minus A.
3. Extend the empty set to a maximal independent set J among vertices of A having no neighbor in I.
4. I union J is independent and dominating; adding the fixed outside endpoint to J gives an independent set in N[A]. These two estimates save one vertex.
5. Positive independence numbers convert the additive bound to the product bound for a nonempty proper cut.
6. If every vertex has minimum degree, it also has maximum degree. In this regular branch, independent domination is bounded by the edge count using a proper maximal independent set and the connected-graph spanning-tree inequality.

This publication is a formal certificate and statement contribution, not maintainer acceptance, independent third-party execution, or a new additional mathematical solution.

## Source hashes

- WOWII423Proof.lean: 11fba8ca2df7f2c39c960fe53b9ea7a736490d1b672197911cdda6973439056f
- WOWII423Audit.lean: d82bca3c2c42bac4bd543a0ada73c875f54e7e64dcafefa20fc0e31891824284
