# Two classical Erdős 617 certificates

This package formalizes two existing declarations without changing their quantifiers:

* `Erdos617ThreeProof.r_eq_3`: every three-colouring of the unordered pairs of an arbitrary ten-element type has a four-element subset missing a colour.
* `Erdos617AffineProof.r2`: infinitely many parameters admit an r-colouring on r² vertices for which every (r+1)-element subset contains every colour.

Both results are due to Paul Erdős and András Gyárfás, *Split and balanced colorings of complete graphs*, Discrete Mathematics 200 (1999), 79–86. The [author-hosted primary source](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf) gives the affine construction on p.80 and the three-colour result in Lemma1, pp.84–85. No new research solution or priority claim is made.

The three-colour argument chooses a colour graph with at most15 edges. Assuming every four-set sees every colour rules out independent four-sets and five-edge diamonds. The elementary core proves minimum degree at least3. Degree counting then gives maximum degree3; Brooks' theorem yields a three-colouring and hence an independent four-set, a contradiction.

`Proofs/ZajacBrooks.lean` reuses the previously published Lean4.33.1 adaptation of Nick Winter's formalization of Mariusz Zając's Brooks proof. Its attribution is retained in the source. Original formalization: `nwinter/erdos-617-r5`, commit `32f1bfe6759299ef3a1c6e8b4c3c637528a9881b`, `lean617/Lean617/R6/Brooks.lean`. This inherited component is not counted as a new proof. The adaptation was previously published in this fork at `443db1e29bebcef2b4f9f16c753cb509ca59d9a6`. Relative to that file, this copy generalizes the vertex-type binders from `Type` to `Type*` in three places; the proof bodies are unchanged and are rechecked here.

The affine construction uses points in `ZMod p × ZMod p`, for prime p, with the slope as colour; vertical pairs receive colour0. For each colour k, the intercept map `(x,y) ↦ y-kx` has p values. Pigeonhole on a (p+1)-set yields a distinct pair of slope k. Infinitely many primes suffice for the exact infinitely-many-parameters target.

The new formalization, source checks and exact statement bridges were developed with OpenAI Codex assistance. The r=5 and r=6 certificates already linked in PR7223 retain their separate provenance. The general all-r conjecture remains open; no new certificate for r=4 is supplied here.

## Reproduction

Use this immutable commit's `lean-toolchain` and `lake-manifest.json` (Lean4.33.1). From the repository root:

```sh
lake exe cache get
lake --wfail build 'FormalConjectures.ErdosProblems.«617»'
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Proofs/Erdos617AffineProof.olean Proofs/Erdos617AffineProof.lean
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Proofs/Erdos617ThreeCore.olean Proofs/Erdos617ThreeCore.lean
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Proofs/ZajacBrooks.olean Proofs/ZajacBrooks.lean
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Proofs/Erdos617ThreeProof.olean Proofs/Erdos617ThreeProof.lean
lake env lean -DwarningAsError=true Proofs/Erdos617Round9Certificate.lean
```

The last command checks both exact proposition shapes and rejects any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. It includes an explicit `sorryAx` rejection control. Its success marker is `ERDOS617_R3_R2_EXACT_CERTIFICATE_PASS`. The imported repository statements retain their conventional placeholders; the external end-theorem axiom closures must not depend on them. Kernel checking, repository CI, maintainer acceptance and mathematical originality are separate claims.
