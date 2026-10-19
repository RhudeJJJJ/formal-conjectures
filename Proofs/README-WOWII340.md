# WOWII 340: exact Lean refutation

The certificate proves the negation of the literal universal inequality in
WOWII entry 340. Its witness is Gebendorfer's double broom D(5,5): the path
on vertices 0 through 11, five additional leaves at 0 and five at 11.

The kernel checks that this graph is a tree of order 22, that its total
domination number is 8, its domination number is 5, the number of components
of the leaf-support induced subgraph is 2, and its smallest degree mode is 1.
Thus the proposed bound reads 8 <= 2 + 1 * 5, which is false.

Upper bounds use explicit dominating sets. Lower bounds use the manuscript's
eight disjoint open neighborhoods and five disjoint closed neighborhoods.
Finite `decide` proofs verify only the explicit graph, its sets, and label
properties; arbitrary dominating sets are handled by injections from those
packings. No powerset enumeration of 22-vertex sets is required.

`WOWII340Certificate.lean` checks the exact imported target and rejects every
transitive axiom other than `propext`, `Classical.choice`, and `Quot.sound`.
The built-in `sorryAx` is checked as a rejected negative control. There is no
`native_decide` or compiler-trust axiom in the certificate.

## Reproduce

Use the committed `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake --wfail build FormalConjectures.WrittenOnTheWallII.GraphConjecture340
sha256sum -c Proofs/WOWII340-SHA256SUMS
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Proofs/WOWII340Proof.olean Proofs/WOWII340Proof.lean
lake env lean -DwarningAsError=true Proofs/WOWII340Certificate.lean
```

## Sources and scope

The construction and packings are Theorem 4.3 of Jonas J. Gebendorfer,
*Double brooms refute Graffiti.pc Conjecture 340 on total domination in trees*,
October 17, 2026. The supplied eight-page manuscript has SHA-256
`9ba256a81e9c76a15dbee66e44b28d8015bc430634b04b73413bac8ca811f869`.
It credits Claude assistance for the mathematical work and drafting.
OpenAI Codex assisted with this source audit and new Lean formalization.

The archived original row and definitions 45, 46, 49, 94, and 100 were read
directly. Definition 45 explicitly selects the smallest mode in a tie;
degree 1 and degree 2 each occur ten times in D(5,5).
The retained gzip capture bytes have SHA-256
`39d7169f65521a3968a7b6fbb683e482b8bda7ab50e039b3ffa808f1e6c0a4fa`
(row collection) and
`e8a9ef48c603a34813ebc432224dd7b632e17b9baa97b7f27b6ff140848430d3`
(definitions). The capture date is July 23, 2026; its open marker describes
that historical snapshot, not current curator acceptance.

This is a complete refutation of the conjecture. The certificate does not
formalize the entire double-broom family, the one-ended families, the
unbounded-deficit theorem, or the census and minimality claim. The analytic
arguments in the supplied manuscript were checked on paper. Its separate
reproducibility ZIP was not supplied, so its exhaustive census was not
replayed in this audit. No worldwide priority or independent human review is
claimed.
