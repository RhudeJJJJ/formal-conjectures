# Complete Lean proof of WOWII 317

Author: Jonas J. Gebendorfer. Formalization assisted by OpenAI Codex, 13 October 2026.

This branch hosts the long external proof requested in google-deepmind/formal-conjectures PR #7225. It is not an additional mathematical solution or a claim of maintainer acceptance.

## Statement

For every finite simple connected graph with more than one vertex, if the number of complement edges is at most the largest induced-tree order, all inclusion-minimal total dominating sets have the same cardinality. The proof establishes the stronger conclusion that each such set has cardinality two. Hypotheses and definitions coincide with the submitted statement, including K2 and open-neighborhood total domination.

Written source: Gebendorfer, *Three Well-Total-Domination Conjectures from the Written on the Wall II List*, 28 July 2026, Theorem 4.5, https://doi.org/10.5281/zenodo.21650036.

## Reproduction

The inherited lean-toolchain and lake-manifest.json pin Lean 4.33.1 and Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Run from the repository root:

```sh
lake exe cache get
lake build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/WOWII317Proof.olean Proofs/WOWII317Proof.lean
lake env lean Proofs/WOWII317Audit.lean
```

The audit independently restates the PR type and applies the proved theorem. All three printed axiom lists are exactly `[propext, Classical.choice, Quot.sound]`. The proof compilation exits 0 with no warnings; the audit exits 0. Neither file contains `sorry`, `admit`, `native_decide`, new axioms, or a finite-order restriction. Axioms of unrelated statement placeholders elsewhere in this repository are not dependencies of these theorems.

In the execution environment used here, an already documented compatibility adapter replaces only a failed readlink of the current process executable with its /proc/self/exe alias. Lean's executable, elaborator, kernel and mathematical sources are unchanged. This path-discovery adaptation is not required in ordinary supported Lean installations.

## Structure

1. Tree/complement edge counting bounds the total number of missing edges by four.
2. Minimality gives a private neighbor for each selected vertex.
3. Two selected neighbors at one selected vertex force five distinct missing edges, so the selected subgraph is a matching.
4. Two selected matching edges exhaust the complement as a four-cycle.
5. Every induced tree in that exception has order at most three, contradicting the original bound.

The sixteen membership cases in step 5 are a symbolic case split for arbitrary vertices and arbitrary graph order, not a graph census. All proof terms are checked by Lean's kernel.

## Verified source hashes

- WOWII317Proof.lean: c56335f3db43965c1c9f7f5da8f6a628d2273d68c01d6419f4d34920c227b54f
- WOWII317Audit.lean: fa5f5b7de45bdf8579a63465271ec7c0dfe4f105910a70cc8bce19b999f0d329
