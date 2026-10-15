# Download

[Complete reproducible package](Gebendorfer_RG_Algebraic_Reductions_Lean_2026-10-15.zip). SHA-256: `31017ce83a3941382353e2e07795dbecc64f519b2ebf801132ca93f76d8167bf`.

# RG algebraic reductions: checked partial formalization

Jonas J. Gebendorfer, with OpenAI Codex assistance. 15 October 2026.

**This package does not prove the global Radenković–Gutman conjecture or universal strict pendant-path fusion. It must not be cited as a full RG Lean certificate.**

## Checked statements

The eleven-module source closure includes the earlier all-length path determinant/resolvent bridge and seven new modules.

- `CoreQuotient`: the rank-two determinant lemma and exact one-arm/two-arm formulas for any finite core matrix, with invertibility proved where needed.
- `GraphJoin`: the matrices are attached to actual simple-graph Laplacians, using disjoint graph sums and the specified added edges. A temporary instance-selection change is restored before the module ends; it imposes no mathematical hypothesis.
- `FusionQuotient.normalized_resolvent_quotient`: for every finite simple core graph, every root, every pair of positive arm lengths, and every nonreal complex parameter, the characteristic determinant ratio is exactly the singleton-normalized endpoint-resolvent expression in Lemma 2.2 of the manuscript. No tree classification, numerical premise or energy inequality is assumed. The source is the core with two separate paths. The fused graph is defined as the core joined to one combined path; the explicit isomorphism to a delete/add operation on the original labelled vertex set remains outside this package.
- `ResolventDisk.hermitian_resolvent_disk`: the genuine inverse of every finite Hermitian shift satisfies the quadratic-form disk bound. The proof uses Cauchy–Schwarz and the imaginary resolvent identity, rather than assuming a spectral-measure representation. `schur_complement_disk` gives the associated Schur scalar disk and its upper-half-plane bound.
- `PathEnclosure.all_long_arms`: the invariant rational interval for every real recurrence index corresponding to arm length at least five, including its exact width.
- `ArmBridge.all_long_path_resolvents`: that interval applies to actual complex path endpoint inverses at `z=2+iy`, `y>0`, at every length at least five.
- `ReductionsAudit.exact_graph_quotient` writes out the actual graph Laplacians again. `normalization_negative_control` proves that the unnormalized path determinant prefactor is not identically one. The earlier singleton and wrong-endpoint-degree controls are retained.

The construction uses `p+1` and `q+1` as the positive arm lengths. It covers all such lengths. The combined arm has length `p+q+2`.

## What remains unformalized

There is no closed Lean theorem asserting `LE(P_n) ≤ LE(T)` for all trees. The outstanding chain includes the graph-root/principal-minor and reciprocal-disk bridges, the linear-fractional disk minimum, the logarithmic integral identity and its endpoint controls, the spectral-count gap and threshold transport, sound formal acceptance of the Bernstein and finite Sturm/integration certificates together with exhaustive coverage, and the strict fusion/global graph reduction. The existing written proof, Python/Arb reconstruction and private correspondence are separate evidence; they are neither discarded nor substituted for these Lean obligations.

No `formal_proof` attribute for global RG is justified by this package. No new mathematical priority is claimed for the classical matrix, resolvent or continued-fraction identities.

## Reproduce

Install official Lean 4.33.1 using elan, extract the archive and run:

```sh
python3 verify.py
```

The verifier obtains Mathlib pinned to `0df444a360eaa60ab8c11dca51a86af692955474` and its official cache. It then rebuilds every supplied local module from source, in order, with warnings as errors and both implicit-variable options disabled. It rejects proof placeholders, custom axioms, `native_decide`, or any printed axiom outside `propext`, `Classical.choice`, `Quot.sound`.

An already configured project at the exact pin can be reused read-only:

```sh
python3 verify.py --mathlib-project /absolute/path/to/project
```

A conventional target is also available:

```sh
lake --wfail build Proofs.RadenkovicGutmanReductionsAudit
```

The delivered source copies were freshly rebuilt on 15 October 2026: eleven modules passed; 41 printed axiom profiles contain only the three standard axioms or subsets. Some profiles are repeated exact-type audits; these are not 41 new conjecture solutions. The direct source rebuild took 33.485 seconds after dependencies were available. Executed logs and the receipt are in `AUDIT_LOGS/`. No local precompiled proof objects are shipped.

This execution sandbox needed the previously documented narrow process-readlink adapter, mapping only `/proc/<own-pid>/exe` to `/proc/self/exe`. Neither the official compiler binary nor its kernel was modified. Normal installations do not need that adapter.

## Sources and credit

Jonas J. Gebendorfer, *Laplacian energy of trees and pendant-path fusion*, 5 September 2026, DOI https://doi.org/10.5281/zenodo.22342611, especially Sections 2 and 3. The algebraic statements here are formalized independently from the numerical certificate evaluators. Mathlib supplies its determinant, adjugate, Hermitian spectral and inner-product theorems; its contributors retain their credit and licenses. AI assistance covers derivation, implementation and auditing; AI systems are not authors. Source code: Apache 2.0.
