# Full Lean refutation of the original WOWII72 reading

Theorem: WOWII72.full_conjecture72 in Full.lean.

The source assertion is tree(G) >= ceil(A(G)+Lambda(G)/3). Only Lambda is divided by three. The different ceil((A+Lambda)/3) reading is not refuted.

The theorem negates the universal assertion on every Fin(n+2), representing every nontrivial finite graph order. It does not assert that every graph violates the inequality. The actual connected witness has 31 vertices with the complete edge relation in Graph.lean: a clique on 24 vertices attached to vertex 24, the path 24-25-26-27, and independent vertices 28, 29, 30 each adjacent exactly to 24, 25, 26.

## Certificate scope

* Tree.lean proves that the repository's actual largestInducedTreeSize is at most 5. Two clique vertices plus any exterior part force a triangle at the attachment. Otherwise the projection to 8 types is injective on the actual induced tree. A kernel-checked exhaustive finite lemma says every type subset of order greater than 5 has a triangle, a 4-cycle or an isolated vertex. These lift to a contradiction in the original tree.
* Eccentricity.lean proves connectedness and uses two one-Lipschitz natural-number potentials, zero at the relevant endpoints, to bound actual distances from below. Their maximum sums to 114, so averageEccentricity>=114/31.
* Four explicit independent neighbours show maxLocalIndependence>=4. Hence A+Lambda/3>=466/93>5, so the ceiling cannot be at most the largest induced tree order.

This is a full counterexample proof of the original universal assertion. The exact equalities for all invariants and the manuscript's two-parameter unbounded-deficit family are not claimed as formalized.

## Source and priority

Jonas J. Gebendorfer, An unbounded deficit in Written on the Wall II Conjecture72 (28 October 2026), submitted at https://github.com/google-deepmind/formal-conjectures/issues/7662.

The earlier public VibeMathed report (submitted 17 August 2026, referring to a 23 July post) already reports that this reading is false:
https://vibemathed.com/problem/wowii-conjecture-72-two-induced-trees-pin-down-tree-g

No first-disproof or family-novelty claim is made. The contribution is formal certification of this explicit witness and the original reading. AI assistance: Codex assisted with proof development and verification. No independent peer review is claimed.

## Checks

Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 are pinned by the base repository 5a2fb85045c86e4a184b15ce7531ba199a3c4580. All certificate modules are checked with warningAsError=true, autoImplicit=false and relaxedAutoImplicit=false. The full target and tree/metric/finite-obstruction bridges use only propext, Classical.choice and Quot.sound. No sorry, custom axioms, native_decide or compiler-trust axioms occur in the certificate.

The local audit checks exact equality with the prepared submitted negative declaration and verifies that this is the negation of the original positive predicate specialised to every Fin(n+2). Original statements are admitted type/axiom negative controls and are absent from the certificate dependency graph. The local positive-source import overlay changes only its umbrella import and attributes; the submitted negative control additionally has its namespace renamed to avoid collision. CanonicalAudit.lean imports the untouched original positive module and checks the exact same source reading. That separate replay must be reported as pending until its workflow completes.

Reproduce with the exact commands in .github/workflows/wowii72-proof.yml.
