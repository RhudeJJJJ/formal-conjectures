# Complete Lean certificates for WOWII 412d

Both submitted targets are proved with their exact definitions and hypotheses:

- `WOWII412dProof.conjecture412d_isolate_free`: for every finite bipartite graph
  without isolated vertices, the total domination number is at most the corona
  cardinality, and the corona equals the maximum-critical independent-set union.
- `WOWII412dProof.conjecture412d`: the original connected formulation for graphs
  of order greater than two, bounded by that critical union's cardinality.

The strengthened theorem has no hidden connectedness or order assumption.
Critical differences remain integers; maximum critical means greatest
cardinality among independent difference maximizers. Total domination covers
selected vertices as well.

## Construction and sources

Written source: Jonas J. Gebendorfer, *Total domination and the union of maximum
critical independent sets in bipartite graphs*, revision 11 October 2026,
[public manuscript](https://github.com/user-attachments/files/33355645/wowii-412d-total-domination.pdf).
The manuscript credits the bipartite critical-set characterization separately;
this certificate makes no new priority claim for it or for Hall's theorem.

Two earlier files are reused unchanged from checkpoint
`a4e07d0a5b53345446859e852daf80efa518e7c6`:

- `WOWII412dCore.lean`, Git blob `9860f8a4c1931f5d33191fd5561783dc9ec7b1e4`,
  proves the mixed-set and core/corona reductions and strict Hall inequality.
- `WOWII412dAssembly.lean`, Git blob `ed327805d4d1c4bc487e28ab6c098ec0a65a12f8`,
  proves assembly conditional on a bounded core cover, and the empty-core case.

Their module comments describe their original, partial scope. The new files
below discharge the missing cover assumption; no conditional step remains in
the two final certificates.

1. `StrictHallForest.lean`: apply Mathlib's finite Hall theorem for distinct
   representatives. Strict Hall provides an escaping incidence for every
   nonempty subfamily. Eliminating these gives a strictly decreasing rank for
   second representatives. Their undirected graph is acyclic; indexed edges
   are distinct, so parallel indexed edges are not silently collapsed.
2. `RankedForestCover.lean`: prove simultaneous vertex and edge covers in the
   ranked forest with combined size at most its vertex count. At a leaf,
   select its neighbor for the vertex cover and the incident edges of all
   leaf neighbors for the edge cover; delete those vertices and induct.
   Isolated ground vertices are covered by an additional incident family
   member, charged to their own cardinality. This proves the needed incidence
   cover directly, without assuming the manuscript's cover/packing duality.
3. `WOWII412dForest.lean`: independently instantiate the forest selection on
   the actual core/excluded neighborhoods.
4. `WOWII412dCover.lean`: construct the bounded core/excluded cover and apply
   the earlier assembly reduction.
5. `WOWII412dProof.lean`: identify the submitted definitions exactly and prove
   both submitted targets.
6. `WOWII412dAudit.lean`: restate both exact target types and check the complete
   transitive axiom closures, including the new combinatorial steps.

OpenAI Codex assisted with the ranked-forest construction, formalization and
validation. These are new complete compositions of reused foundations, not
new proofs of every imported lemma.

## Reproduction and validation

Use official Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The certificate is based on the
submitted statement commit `bca3fde7df59d1ca618d02456a3c40383e874fdf`.
From the repository root:

```bash
lake exe cache get
bash Proofs/WOWII412dValidation/check.sh
```

The script checks the source hashes, builds the exact statement module and
freshly exports all eight proof/audit modules with warnings treated as errors
and implicit variables disabled. The audit allows only `propext`,
`Classical.choice` and `Quot.sound`. Both final certificates and all checked
construction steps pass. A negative control verifies that `sorryAx` fails the
same whitelist. Imported statement placeholders do not enter the final axiom
closures; the statement repository retains its usual external-proof format.

Logs, checksums and metadata are in `WOWII412dValidation/`. The disclosed
`environment/process_path.c` adapter retries only a failed numeric lookup of
the current process's executable through `/proc/self/exe`; this sandbox needs
it, ordinary systems do not. No Lean binary, kernel rule or mathematical
axiom is modified.

The complete original and strengthened WOWII 412d statements are covered.
Kernel validation and successful builds do not establish new human review,
priority over earlier literature, or upstream admission.
