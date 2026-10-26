# Kazemi Conjecture 6.1: full Lean certificate

The theorem `Kazemi.Hypercube.full_conjecture6_1` in [Full.lean](Full.lean) proves the exact statement submitted in upstream PR7383 for every natural n >= 2:

`totalDominatorChromaticNumber (SimpleGraph.hypercube (2^n+1)) = 2^(2^n-n+1)+2`.

There is no finite cutoff or additional hypothesis. The proper coloring is surjective, and total domination uses open neighborhoods.

## Proof structure

- Geometry and CubeCounting: flips, open/closed neighborhoods, common-neighbor capacity and equality in the independent-set matching bound.
- EvenBound: the even-dimensional domination bound by excess double counting.
- Parity and Prism: parity projection of each half of a total dominating set.
- Code: all nonzero binary syndrome columns plus two zero columns; an explicit kernel-times-syndrome equivalence counts the singleton colors. Both residual parity colors are nonempty.
- LowerColor: active-class representatives and capacity counting; the dimension-five equality case is handled without a finite search.
- Parameters, Coordinates and Full: symbolic arithmetic, transfer to the actual original graph, and the minimum over valid color counts.

## Verification boundary

All eleven modules passed strict local Lean4.33.1 with Mathlib0df444a360eaa60ab8c11dca51a86af692955474. Full and ExactAudit used an explicit source overlay: replace only `public import FormalConjecturesUtil` by `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Hypercube`, `Mathlib.Combinatorics.SimpleGraph.Coloring`, and `Mathlib.Order.Lattice.Nat`, and remove the category/AMS attribute. All mathematical source characters are identical. Other proof modules have their displayed imports unchanged.

ExactAudit confirms the complete original target type and transitive axioms `propext`, `Classical.choice`, `Quot.sound` only. The admitted original has `sorryAx` as a negative control. The certificate contains no sorry, custom axiom or native evaluation. See [local-verification.json](local-verification.json) for hashes and the actual audit output.

[Canonical CI40378804061](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/40378804061) checks the untouched original imports and protected source hashes. It is queued at this documentation checkpoint; no successful canonical CI is claimed here. Its actual checkout SHA is recorded separately from the workflow-event SHA.

The immutable proof source linked upstream is commit a1a7e2bff19e75f1d2587886ddddc4ed931961cd, Full.lean line20. Upstream statement commit fd32959ae33e7d2c787256555b4d573bcdbc2419 adds only the external proof attribute. The original placeholder is retained under the statement repository policy and is absent from the certificate dependency graph.

## Reproduce with original imports

Build `FormalConjectures.Paper.KazemiHypercube` using `lake --wfail build`. Then compile Geometry, CubeCounting, EvenBound, Parity, LowerColor, Prism, Code, Parameters, Coordinates, Full and ExactAudit in that order with `lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false`, writing each olean into `.lake/build/lib/lean/Proofs/Kazemi/`. The workflow and ci_loop.py contain the exact commands.

## Sources

Kazemi, Conjecture6.1, page10: https://shahindp.com/Contrib_Math/v13/CM26_v13_pp1-10.pdf . The dimension is 2^n+1, and this conjecture differs from Question6.1 in that paper.

Gebendorfer, Total dominator colorings of hypercubes of dimension 2^n+1,14October2026: https://github.com/user-attachments/files/33452211/Gebendorfer_New_Manuscripts_2026-10-14.zip .

This is a formal certificate, not a claim of historical novelty, independent reviewer replay or upstream acceptance. OpenAI Codex assisted with formalization and validation.
