# Graphical Bell certificates

This external proof uses the unchanged partition and quasi-complete graph definitions from PR #7385. `Full.lean` proves the coefficientwise target first and derives the Bell target by summing over the finite block-count range. Disconnected graphs are included; no uniqueness classification is claimed.

Canonical-original-import verification passed for proof source `62f9346442c8757cad34bc4c9b295f29260684d2` in [run 40201620527](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/40201620527), cycle 2. All 19 proof modules compiled strictly and the original statement module built successfully. Both rigid-universe target comparisons passed, and both full endpoint axiom sets are `propext`, `Classical.choice`, `Quot.sound`. The original admitted declarations contain `sorryAx` and are negative controls only.

The [immutable diagnostic receipt](https://github.com/RhudeJJJJ/formal-conjectures/blob/dae4939f80c45ac211c4ec3224803e762a378927/ProofDiagnostics/GraphicalBell/latest.json) records all source hashes and exits. Workflow event SHA `6e20145380ae7f8c3a8cf47ceb85a1abab074917` differs from the actual checked proof-source SHA above. The entry points are [full_coefficientwise](https://github.com/RhudeJJJJ/formal-conjectures/blob/62f9346442c8757cad34bc4c9b295f29260684d2/Proofs/GraphicalBell/Full.lean#L10) and [full_conjecture](https://github.com/RhudeJJJJ/formal-conjectures/blob/62f9346442c8757cad34bc4c9b295f29260684d2/Proofs/GraphicalBell/Full.lean#L18). This README update changes none of the audited proof sources.

Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Original statement SHA256: 05bab9c948efbf749153c59d6ef457d2b61c5b6734d1093e97cff55de1fe8790.

To replay from this repository checkout (Bash):

```sh
lake exe cache get
lake --wfail build FormalConjectures.Other.GraphicalBell
mkdir -p .lake/build/lib/lean/Proofs/GraphicalBell
for name in Vectors Partitions Recovery Base Insertion Deletion Simplicial Discrete QuasiGraph CountVectors Transport Parameters Model Degrees Universal BellBridge OriginalBridge Full ExactAudit; do
  lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o ".lake/build/lib/lean/Proofs/GraphicalBell/$name.olean" \
    "Proofs/GraphicalBell/$name.lean" || exit 1
done
```

Every command must exit zero. In the final audit, both full targets must have standard axioms only; both original placeholders must still report `sorryAx`. A build alone does not establish that distinction.

Proof layout: Vectors proves the integer coefficient identities; Partitions–Simplicial count vertex extensions; QuasiGraph–Model identify and compare the candidate; Degrees–Universal perform the finite-carrier induction; Transport, BellBridge and OriginalBridge identify the submitted definitions; Full composes the endpoints; ExactAudit checks the complete types using rigid universe parameters and prints transitive axioms.

The bounded CI driver records actual source SHA separately from workflow event SHA and protects the original statement, toolchain, manifest and shared utility bytes.
