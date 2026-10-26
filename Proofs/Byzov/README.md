# Complete Byzov–Pushkarev Conjecture 8

The exact declaration in PR7403 is proved for every n ≥ 2. The relation is the nine-block circulant family of Equation (17) in arXiv:2603.07707v2. The group uses the original augmentation subgroup and positive cyclic-shift action.

Immutable proof: a0a4a998ac81abeb7af3105046be608594db721b, Full.lean line15. All nine Lean files at this commit were publicly read back and match the strict locally checked files byte for byte.

Modules, in order: Cyclic, Shape, Model, Source, Automorphisms, NormalForm, Group, Full, ExactAudit. The certificate derives exact twin classes from the submitted adjacency definition, proves rotation rigidity of their tournament quotient, reconstructs the remaining vertices using exact neighborhood profiles, proves the full unique normal form, and constructs a bijective homomorphism from the stated group. Translation by -a matches the original positive-shift semidirect-product law. The odd binary sum separates the constant and augmentation parts.

## Local verification

Lean4.33.1, Mathlib0df444a360eaa60ab8c11dca51a86af692955474. All nine modules passed with warningAsError=true, autoImplicit=false, relaxedAutoImplicit=false. The local statement overlay replaces only the umbrella import by the following pinned imports and removes the category/AMS attribute:

- Mathlib.GroupTheory.SemidirectProduct
- Mathlib.Algebra.Order.Group.End
- Mathlib.Data.Fin.VecNotation
- Mathlib.Data.ZMod.Basic
- Mathlib.Algebra.BigOperators.Group.Finset.Basic
- Mathlib.Tactic.Ext

Every mathematical source character is unchanged. Source/Automorphisms/NormalForm/Group/Full/ExactAudit import this copy; this is a complete local proof check with the documented import boundary, not a completed untouched-original-import CI check.

ExactAudit uses rigid shared universe parameters and definitional type equality against the complete original theorem. An unrelated proposition is rejected. The full certificate and three structural bridges use only propext, Classical.choice, Quot.sound; the original admitted theorem has sorryAx and serves as a negative control. No proof module uses sorry, a custom axiom, or native evaluation.

## Reproduction with original imports

Check out this proof branch and its pinned lake-manifest/toolchain, obtain Mathlib cache, then build the original statement module. Compile the nine modules in the above order, placing each olean under .lake/build/lib/lean/Proofs/Byzov/, using lake env lean and the three strict flags. The bounded ci_loop.py records actual checked source SHA separately from the workflow event SHA, protects the original statement and dependency pins, and checks exact audit output.

Original-import verification run40405338433 is queued at this snapshot:
https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/40405338433

The upstream full project and Test scripts passed on submitted head2ad785550af2c59c7bb13d1272bc01162ab8eeb1:
https://github.com/google-deepmind/formal-conjectures/actions/runs/40405958837

The upstream build compiles the statement repository, separately from the external proof package. The original placeholder remains by repository policy, with an immutable formal_proof link. No merge, historical novelty or independent Lean reviewer replay is claimed.

Primary source: https://arxiv.org/html/2603.07707v2, Equation (17), Theorem7, Conjecture8. The complete written24July2026 structural proof was also read. Finite Python checks in its archive are supporting examples only; the Lean theorem is universal.
