# Written on the Wall II, Conjecture 161

This project proves the full finite connected-graph inequality
`maxLocalIndependence Gᶜ ≤ Ls G`.
The left side is the maximum independence number of an open neighbourhood in
the complement. The right side is the maximum number of degree-one vertices
among spanning trees of the original graph.

The theorem includes the one-vertex graph. Spanning trees are subgraphs and
need not be induced. No extra mathematical hypothesis, custom axiom, finite
graph enumeration, or native-evaluation premise is used.

## Main declarations

| Declaration | Content |
| --- | --- |
| `WrittenOnTheWallII.GraphConjecture161.conjecture161` | The complete original inequality |
| `WOWII161.proper_clique_card_le_Ls` | Every proper clique is bounded by the spanning-tree leaf number |
| `WOWII161.degree_le_Ls` | Every vertex degree is bounded by the spanning-tree leaf number |
| `WOWII161.tree_degree_le_leaves` | Every tree degree is bounded by the number of degree-one vertices |

`Challenge.lean` is a 54-line independent statement surface. Its imports are
only Mathlib and its pinned dependency closure. It states both graph invariants
explicitly. Its single deliberate `sorry` is a statement placeholder.
`Solution.lean` supplies the proof, through `WOWII161/Proof.lean`.
The proof development contains no `sorry`, `admit`, custom axiom, or
`native_decide`.

## Proof

A finite tree has at least as many leaves as the degree of any one vertex.
For a nontrivial tree, every vertex has positive degree. If a vertex has degree
one, adding its leaf indicator to its degree gives two; otherwise its degree
is already at least two. Sum this inequality over all vertices except the
chosen vertex, and combine it with the handshaking identity and the tree
edge-count identity. The singleton case is handled separately.

For a vertex of a connected graph, intersect the graph with the star centred
at that vertex. This is an acyclic subgraph and retains all edges incident to
the centre. Mathlib's acyclic-subgraph extension theorem places it inside a
spanning tree. The tree degree bound gives at least as many leaves as the
original vertex degree. Conversion to a spanning `Subgraph G` then places
this leaf count in the supremum defining `Ls G`.

A nonempty proper clique has an edge to its complement by connectedness.
The endpoint in the clique is adjacent to every other clique vertex and to
one extra vertex, so its degree is at least the clique cardinality. The empty
clique is handled using nonnegativity.

Finally, an independent set in a neighbourhood of the complement is a clique
of the original graph. It is proper because it excludes the neighbourhood's
centre. Apply the preceding bound and take the finite maximum.

## Source and statement audit

The original archived WOWII entry is dated **8 August 2005**. Its HTML encodes
an overline on the graph in the local-independence term. Linked definitions
1, 4 and 31 define the spanning-tree leaf number, neighbourhood independence,
and complement. The archived source hashes were checked directly against
recovered bytes and agree with the 28 October manuscript:

- HTML: `8af2a12bcad483e4577963585b8bfc12abe1fca2521e1137ff827e8e8d647d59`
- Definitions: `695b7262acbf4398a88530e7375715912e4a1ac628ad9be2e56ecd122023a703`

[West's independent presentation](https://dwest.web.illinois.edu/regs/graffiti.html)
states the same conjecture and defines both invariants. The mathematical
source is Gebendorfer's
[28 October 2026 preprint](https://www.researchgate.net/publication/417064781_Proper_cliques_and_spanning-tree_leaves_An_elementary_proof_of_Graffitipc_Conjecture_161),
DOI [10.13140/RG.2.2.31746.44485](https://doi.org/10.13140/RG.2.2.31746.44485).

The definitions are copied without semantic changes from Formal Conjectures
at [fd57f5d489321515f695ea205913d0ac3289f41c](https://github.com/google-deepmind/formal-conjectures/tree/fd57f5d489321515f695ea205913d0ac3289f41c):

- `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/SpanningTree.lean`
- `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`

The separate [original-import certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/9c8f5667ab2c64a348b86abf6870a35dd471c6e3/Proofs/WOWII161/Proof.lean)
was checked against these actual imports using Lean **4.33.1** and Mathlib
**0df444a360eaa60ab8c11dca51a86af692955474**.
[Run 41638457934](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/41638457934)
succeeded on 3 November 2026. Its bounded development job records the checked
source separately from the workflow-event commit: the successful source was
**9c8f5667ab2c64a348b86abf6870a35dd471c6e3**.

That audit confirmed definitional equality of the full theorem types and
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
The unproved statement was also audited as a negative control and contained
`sorryAx`. Full diagnostics are in `original_import_audit.json`.

## Standalone build and Comparator

This standalone package uses Lean **4.35.0-rc2** and Mathlib
**065356127b1dc0016f66b7283ce0ce2c4055aa55**, as pinned in the manifest.
This newer toolchain is required by the current Palomar verifier. Its CI
separately checks this port; the older original-import run does not certify
the port by itself.

```sh
lake exe cache get
lake --wfail build WOWII161 Solution
lake build Challenge
lake env lean -DwarningAsError=true Audit.lean
lake comparator comparator.json
```

The workflow also invokes Palomar's complete mechanical preflight at pipeline
**14aa8d6b3c2f14a8540605e37144560b9a00e7e7** with `mode: full`.
A successful preflight is a mechanical check, not registry submission,
editorial review, or registration. No Palomar identifier is claimed here.

## Scope and provenance

The complete original inequality is formalized. The manuscript's separate
sharpness family and clique-number strengthening are not claimed as Lean
results. The leaf-supremum and spanning-subgraph conversion helpers adapt the
corresponding Apache-2.0 helpers in
[MiskinAleksandr23/WOWII-1](https://github.com/MiskinAleksandr23/WOWII-1/blob/eda16f6e96b313bd112351ae9859133b77d537c9/WOWII1/GraphConjecture1.lean).
That project concerns WOWII1.

AI assistance was used for proof construction and source comparison. No
independent human review, current curator acceptance, journal acceptance, or
worldwide first-priority claim is made. The original historical O marker is
not evidence for any of those statuses.

