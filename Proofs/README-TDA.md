# Total domination and the annihilation number

This package targets the exact statement in
[PR 7388](https://github.com/google-deepmind/formal-conjectures/pull/7388):

```lean
theorem total_domination_annihilation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 ≤ Fintype.card V) :
    G.totalDominationNumber ≤ G.annihilationNumber + 1
```

The certificate entry point is `Proofs/TDACertificate.lean`. Its final check must
print `TDA_EXACT_CERTIFICATE_PASS`; a file compiling with a placeholder does not
satisfy that check. The guard checks the full transitive axiom closure of
`TotalDominationAnnihilationProof.total_domination_annihilation`, permitting only
`propext`, `Classical.choice`, and `Quot.sound`. The existing open
`SimpleGraph.annihilationNumberEq` declaration is a negative control for the
guard. It is never used as a mathematical premise.

The graph may have pendant vertices, adjacent supports, or strong supports.
The annihilation number is the repository's actual degree-submultiset supremum.
No equivalence to its alternative sorted-prefix definition is assumed.

## Proof organization

1. `TDAHypergraphBase` and `TDAUniform` prove the indexed three-uniform
   Chvátal–McDiarmid bound. The low-incidence case uses a four-coloring of the
   conflict graph, whose degree is at most four and whose clique number is at
   most four. High incidences are removed by induction.
2. `TDAMixedBase` and `TDAMixed` prove the mixed transversal bound for edge
   sizes one through three, with potential `2n + 4e1 + 2e2 + e3`.
   Original indices are retained, including repeated edges.
3. `TDANeighborhood`, `TDACoreCover`, `TDAGraphBasics`, `TDALeafCounts`, and
   `TDAGeneralBound` prove `6 gamma_t <= 3n + 2l + b`, where `l` and `b` count
   vertices of degrees one and two. This Lean route pays the core degree-one
   correction directly from leaf multiplicities. It covers strong supports
   without a separate leaf-deletion induction.
4. `TDABudget`, `TDAOptimal`, `TDADegreeBudget`, and `TDAGraphBudget` connect
   actual vertex sets to the multiset invariant, realize its maximum, and
   prove the smallest-high-degrees budget. If all degree-one and degree-two
   vertices fit the budget, they give `gamma_t <= a`.
5. `TDATreeColor` and `TDATreeBound` prove `2 gamma_t <= n + l` for trees.
   The explicit vertex coloring gives both colors in every neighborhood of
   size at least two. Adding the supports to either color class provides the
   two total dominating sets used for the cardinality bound.
6. `TDATransfer`, `TDAGraphEdge`, `TDAMaxTwo`, and `TDACycleEdge` handle the
   low-budget branch. In a non-tree with a vertex of degree at least three,
   one can delete a cycle edge incident with such a vertex, preserve
   connectedness, and transfer the annihilation budget. `TDAFull` closes the
   exact universal statement by induction on the edge count. Order two is
   checked separately.

These are proof constructions; finite graph enumeration is not a premise.

## Sources and attribution

- Jonas J. Gebendorfer, *A mixed transversal bound and the
  total-domination–annihilation conjecture*, 11 October 2026.
  [Manuscript archive](https://github.com/user-attachments/files/33357596/Total_Domination_Annihilation_Intake_2026-10-12.zip).
  Source archive SHA256:
  `d067e88bdbf41f4fd4405b61e7cc71acfc9e4a6a6e64d7ca8d55f35b289d2afc`.
- Cs. Bujtás and M. Jakovac, *Relating the total domination number and the
  annihilation number of cactus graphs and block graphs* (2019),
  [DOI](https://doi.org/10.26493/1855-3974.1378.11d).
- M. Jakovac, [arXiv:2609.10795v2](https://arxiv.org/abs/2609.10795v2).
  These references fix the original conjecture and credit the prior reductions.
- V. Chvátal and C. McDiarmid, *Small transversals in hypergraphs*,
  Combinatorica 12 (1992), 19–26. The indexed-edge convention is also stated by
  Henning and Löwenstein in [arXiv:1401.4851](https://arxiv.org/abs/1401.4851).
  The bound is proved inside this Lean package.
- `ZajacBrooks.lean` reuses Nick Winter's formalization of Mariusz Zając's
  [Brooks proof](https://arxiv.org/abs/1805.11176):
  [original Lean source](https://github.com/nwinter/erdos-617-r5/blob/32f1bfe6759299ef3a1c6e8b4c3c637528a9881b/lean617/Lean617/R6/Brooks.lean).
  The previously rechecked Lean 4.33.1 port is pinned at
  [443db1e29bebcef2b4f9f16c753cb509ca59d9a6](https://github.com/RhudeJJJJ/formal-conjectures/blob/443db1e29bebcef2b4f9f16c753cb509ca59d9a6/Proofs/ZajacBrooks.lean).
  The only additional change here generalizes three vertex-type binders from
  `Type` to `Type*`. Its original attribution and options remain visible.

The new formalization and composition were developed by Jonas J. Gebendorfer
with OpenAI Codex assistance. Reuse of Brooks is credited to its mathematical
and Lean authors. This package makes no claim of external peer review,
acceptance, or exhaustive bibliographic priority.

## Reproduction

Use Lean **4.33.1** and the repository's pinned Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Keep the repository
`lake-manifest.json` and `lean-toolchain` files. The development workflow is
`.github/workflows/tda-full-proof.yml`.

After `lake exe cache get`, build the actual statement imports:

```sh
lake --wfail build FormalConjectures.Paper.TotalDominationAnnihilation
```

Compile the proof modules in this order, writing their object files under
`.lake/build/lib/lean/Proofs/`, as the workflow does:

```text
TDABudget TDAHypergraphBase ZajacBrooks TDAUniform TDAMixedBase TDAMixed
TDAOptimal TDADegreeBudget TDANeighborhood TDAGraphBasics TDACoreCover
TDALeafCounts TDAGeneralBound TDAGraphBudget TDATreeColor TDATreeBound
TDATransfer TDAGraphEdge TDAMaxTwo TDACycleEdge TDAFull TDACertificate
```

Each module is checked with `lake env lean -DwarningAsError=true`.
The statement repository intentionally keeps its long theorem as `by sorry`
and links to the immutable external certificate through `formal_proof`.
The certificate check is independent of that placeholder and rejects any
placeholder in its own proof dependency closure.
