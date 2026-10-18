# WOWII 412d – exact Lean proof ledger (18 October 2026)

## Verified, sorry-free

Pinned source: [WOWII412dBridge.lean](./WOWII412dBridge.lean), commit `9c11dae584796c00e85456a9cf1bf78db266a3bb`.

Exact-import CI: https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39112812308

- `WOWII412dBridge.criticalUnion_eq_corona`: the exact upstream `corona G = criticalUnion G` for every finite bipartite graph.
- `WOWII412dBridge.strictHall_excluded`: every nonempty set of vertices excluded from the upstream corona has at least one more neighbor in the core than its cardinality.
- `WOWII412dBridge.strengthened_of_core_cover`: the isolate-free strengthened target follows once the explicit core/excluded total cover exists, including the already closed empty-core case.
- Existing `WOWII412dCore` and `WOWII412dAssembly` files compile as dependencies.
- Axiom profiles: `propext`, `Classical.choice`, `Quot.sound` only. No `sorryAx` in the three new declarations.

## Not proved

For every finite isolate-free bipartite graph with nonempty core `F`, produce `D₀` with `|D₀| ≤ |F|` that totally dominates `F ∪ (V \\ corona)`.

The mathematical manuscript (11 October 2026) establishes this by two further universal lemmas that still require Lean formalization:

1. **Strict-Hall forest selection:** indexed sets `Eᵢ ⊆ F` satisfying `|⋃_{i∈X} Eᵢ| ≥ |X|+1` for nonempty `X` admit pair selections `xᵢ ≠ yᵢ ∈ Eᵢ` forming an acyclic indexed edge family. The proof requires tight-set contraction and the no-tight-set case, preserving labels and avoiding duplicate-edge collapse.
2. **Incidence-forest transversal–packing:** for an indexed incidence forest, minimum hitting-set size equals maximum disjoint-member packing size. Applied on both bipartition sides, it yields the total cover bound `|D₀| ≤ |F|`.

These obligations must be proved for arbitrary finite cardinalities, not replaced by finite enumeration, custom axioms, or `sorry`.

## Upstream

Statement PR: https://github.com/google-deepmind/formal-conjectures/pull/7376

The original connected theorem is now a Lean corollary of the isolate-free stronger statement. The stronger statement itself is **not** yet a kernel-certified theorem. Do not mark the main conjecture `formal_proof` until the cover-existence lemma is discharged and exact-import CI is green.
