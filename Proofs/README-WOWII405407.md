# Complete certificates for WOWII 405 and 407

The two declarations in `WOWII405407Proof.lean` prove the exact statements in
`FormalConjectures/WrittenOnTheWallII/GraphConjecture404To407.lean` at base commit
`9029187a7d1448f3dfb5c28dfdd8a9e088c12326`:

- `conjecture405`: for every finite simple tree of order greater than two,
  the private external-neighbor count of the maximum-critical union is at most
  twice the independence number after deleting the leaves.
- `conjecture407`: under the same hypotheses, that count is at most twice the
  vertex-disjoint path-cover number.

The new composition proves that the count is zero for **every finite bipartite
graph**, including the empty graph. The stated tree bounds follow directly.
The right sides and the original order hypotheses are preserved. No matching
number equation, unproved graph-class bridge or conjecture-specific hypothesis
is assumed.

## Dependencies and attribution

Written proof: Jonas J. Gebendorfer, *The Corona of a Graph Is 2-Dominating*,
31 August 2026, revision R2, Corollary 4.2 and its preceding theorems, in the
[source archive](https://github.com/user-attachments/files/33373103/Gebendorfer_WOWII_404_407_Intake_2026-10-13.zip).
The original WOWII rows and definitions are retained in that archive.

The critical-independent-set bridge is established literature, credited in the
manuscript to Larson, Levit–Mandrescu and Jarden–Levit–Mandrescu. This certificate
uses the direct bipartite mixed-independent-set route already proved in the
412d checkpoint; it does not formalize the full KE equivalence again.

Reused source files are byte-identical to the published versions:

| File | Source commit | Git blob |
|---|---|---|
| `WOWII412dCore.lean` | `a4e07d0a5b53345446859e852daf80efa518e7c6` | `9860f8a4c1931f5d33191fd5561783dc9ec7b1e4` |
| `CoronaTwoDominatingProof.lean` | `0d1f9d08f4fa49d8d319cfe429fa54b36a267724` | `6a17b67d160ca4bdbf92a88e419dd7492940ccac` |

The new work is the definition bridge, composition, two exact targets and
validation. The reused corona and bipartite lemmas are not counted as new
proofs. OpenAI Codex assisted with the formalization and checks.

## Reproduction

Use the repository's official Lean 4.33.1 toolchain and pinned Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. From the repository root:

```bash
lake exe cache get
bash Proofs/WOWII405407Validation/check.sh
```

The script builds the exact statement module, freshly exports all four local
proof/audit modules with warnings as errors and implicit-variable creation
disabled, and runs the transitive axiom guard. The two final axiom profiles
must contain only `propext`, `Classical.choice` and `Quot.sound`. The guard
rejects the placeholder axiom as a negative control.

The local sandbox requires an executable-path compatibility adapter: its
numeric `/proc/<current-pid>/exe` link is unavailable, while `/proc/self/exe`
works. `WOWII405407Validation/environment/process_path.c` retries only that failed current-process
lookup through its self alias. It changes no Lean binary, source, elaborator
or kernel rule. Ordinary systems do not need it.

## Scope

These certificates cover 405 and 407. The four-bound equality classification,
the full KE converse and the complete universal theorem for WOWII 412d are
outside this update. The existing KE and general-corona proofs retain their
own separate links. Repository admission and external mathematical review
remain separate from this kernel check.
