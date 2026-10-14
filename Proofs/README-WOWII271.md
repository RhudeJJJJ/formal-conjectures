# Complete Lean proof of WOWII 271

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization and verification, 14 October 2026.

The proof establishes the original square-root ceiling bound for every finite simple connected graph with at least two vertices. The maximum distance is measured in the original graph between maximum-degree vertices, including equal pairs. The maximum-degree set is nonempty; a separate audit proves its pair set is nonempty. The total domination number uses open neighborhoods, including domination of selected vertices.

Written source: *Total domination and distance between maximum-degree vertices*, 12 October 2026, Theorem 1. The complete manuscript and frozen source are attached to [intake #7235](https://github.com/google-deepmind/formal-conjectures/issues/7235). The classical diameter inequality is credited to DeLaVina, Liu, Pepper, Waller and West, *Some conjectures of Graffiti.pc on total domination* (2007), Lemma 3. Its component-sensitive proof is included here rather than assumed.

## Proof structure

1. A shortest walk has distance equal to its index from the initial endpoint.
2. All path indices reached from one selected component span at most its order plus one. This follows by mapping an actual short path inside the component back into the original graph.
3. Those index sets cover the geodesic, even though they may overlap and need not be intervals. Summing their cardinality bounds gives distance plus one at most the selected order plus twice the number of selected components.
4. Total domination excludes singleton selected components, giving the classical diameter bound for every total dominating set.
5. If the selected set has order two, open-neighborhood counting forces maximum-degree vertices to be at distance at most two. For order three the component count is at most one, giving distance at most four. The remaining orders follow from the general estimate.
6. A minimum total dominating set is proved to exist on the connected nontrivial domain. The squared inequality yields the real square root and its natural-number ceiling.

No graph-order cutoff, finite graph enumeration, imported conjecture placeholder, native evaluation or custom axiom is a premise. The proof also establishes the squared bound for every total dominating set, not only a minimum one.

## Reproduction

The inherited `lean-toolchain` pins Lean 4.33.1; `lake-manifest.json` pins Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Run from the repository root:

```sh
lake exe cache get
lake build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/WOWII271Proof.olean Proofs/WOWII271Proof.lean
lake env lean Proofs/WOWII271Audit.lean
```

The proof compilation and separate audit both exit 0 without warnings. All seven audited declarations depend only on `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, native-evaluation or custom-axiom dependency. The audit independently writes the exact proposed repository type and applies the proved theorem without importing the upstream placeholder statement.

The execution environment used the already documented compatibility adapter for failed reads of `/proc/<current-pid>/exe`, substituting the `/proc/self/exe` alias only on that failure. Lean's official executable, sources, elaborator and kernel were unchanged. The official Linux archive was verified against its release SHA-256 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Ordinary supported installations do not need the adapter.

## Source hashes and status

- WOWII271Proof.lean: 37a776689aedcee777942922e971130911cc6e66b9405964a38249c6dcbf7b59
- WOWII271Audit.lean: b0a63bf92c535918b2f5d24561e82ed98b2cfa63941268b35fca34a7e3fa6198

This is an author-workflow formal certificate, not independent external peer review or a maintainer acceptance. The historical WOWII open marker and present secondary transcription do not establish worldwide priority. A complete Lean proof strengthens the evidence for the same mathematical target; it does not add another solved conjecture to the portfolio count.
