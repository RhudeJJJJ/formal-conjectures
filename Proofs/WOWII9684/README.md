# Complete Lean proof of WOWII 96

Theorem: WOWII96.full_conjecture96 in Full96.lean.

For every finite connected graph on at least two vertices:

alpha(G) <= 1 + min_v distEven(v) * (max_v indepNeighborsCard(G,v) - 1).

The root is counted at distance zero. The singleton graph is excluded, as in the original Formal Conjectures declaration.

## Source and scope

Jonas J. Gebendorfer, Local independence along breadth-first layers: a proof of Written on the Wall II Conjecture96 (28 October 2026):
https://github.com/google-deepmind/formal-conjectures/issues/7664

The proof formalizes the original conjecture96 endpoint. It uses a BFS-parent partition of an arbitrary independent set, a one-unit saving in each non-root fibre, and a separate maximum-local-independence-one case. It does not claim the manuscript's sharper sum of individual local independence numbers or its equality classification.

The definitions and original target are pinned to upstream5a2fb85045c86e4a184b15ce7531ba199a3c4580. Lean4.33.1 and Mathlib0df444a360eaa60ab8c11dca51a86af692955474 are pinned by the base repository.

## Verification

BFS.lean, Charge.lean and Full96.lean are checked with warningAsError=true, autoImplicit=false and relaxedAutoImplicit=false. The exact full type matches WrittenOnTheWallII.GraphConjecture96.conjecture96 with shared rigid universe parameters. The full theorem and its cardinality bridges use only propext, Classical.choice and Quot.sound. There is no sorry, custom axiom, native_decide or compiler-trust axiom in the certificate.

The admitted original is inspected only as a type/axiom negative control; it is absent from the certificate's dependency graph. Locally its umbrella import is replaced by the two exact definition modules and its three category/AMS attributes are removed, preserving every mathematical source character. CanonicalAudit96.lean imports the untouched original; the GitHub workflow independently builds and checks that path. A queued or pending workflow is not a pass.

AI assistance: Codex assisted with proof development and verification. This is not a claim of independent peer review, first priority, or merge acceptance.

## Reproduce with the original import

Run the commands from .github/workflows/wowii96-proof.yml. First build FormalConjectures.WrittenOnTheWallII.GraphConjecture96, then compile BFS, Charge and Full96 into .lake/build/lib/lean/Proofs/WOWII9684 and run CanonicalAudit96.lean.
