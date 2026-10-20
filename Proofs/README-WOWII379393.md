# Complete Lean certificates for WOWII 379 and 393a

This package closes the remaining 393a proof in PR #7380 and both universal
379 targets in PR #7379. It checks the exact existing statements. Definitions,
domains, hypotheses, rational fractions and matching parameters are unchanged.

| Target | Certificate |
|---|---|
| WOWII 393a, finite connected graphs of order greater than two | `WOWII393aProof.conjecture393a` |
| WOWII 379, all nontrivial finite trees | `WOWII379Proof.conjecture379` |
| Stronger 379 bound, every total dominating set, order at least three | `WOWII379Proof.conjecture379_strengthened` |

## Written sources and attribution

- Gebendorfer, *Simultaneous sharpness of three pendant-neighborhood bounds for
  2-domination*, [unchanged manuscript and source records](https://github.com/user-attachments/files/33373002/Gebendorfer_WOWII_393_Intake_2026-10-13.zip).
  The manuscript credits the matching/dominating-set ingredient and the precursor
  general bound to DeLaVina, Larson, Pepper and Waller (2010). No new first proof
  of that known general bound is claimed.
- Gebendorfer, *Maximum-degree components and degree diversity in totally
  dominated trees*, 14 October 2026, [manuscript archive](https://github.com/user-attachments/files/33452211/Gebendorfer_New_Manuscripts_2026-10-14.zip).
  The primary question is Conjecture 1 in Section 3, printed page 11, of
  [DeLaVina et al. (2009)](https://math1um.github.io/Research/r05.pdf).
  The formalization does not assert worldwide priority or journal acceptance.

The manuscript arguments were read before implementation. Exact source hashes
are in `WOWII379393Validation/source-receipt.json`. The 393 frozen source row and
definitions agree with the submitted literal neighborhoods. The actual induced
maximum-degree graph counts all components, including isolated vertices.

## Construction

`FiniteMatchingCover` chooses a maximum matching among the actual finite edge
sets. It excludes augmentations of lengths one and three. Selecting one endpoint
per matched edge then dominates every nonisolated vertex. The certificate is
converted to the repository's real-valued `matchingNumber`, defined through
actual matching subgraphs and a supremum; a surrogate matching invariant is
not substituted.

For 393a, set `P` to the pendants, `S=N(P)`, `R=N(S)`, `U=V\R`,
`W=S∩R`, and `A=R\(S∪P)`. Choose distinct pendant edges for `W`, disjoint
from a maximum matching on `A`. Their union is a genuine matching on `R`.
An endpoint cover `Q` on `A` gives the two-dominating set `U∪P∪W∪Q`.
An omitted nonisolated vertex of `A` receives distinct neighbors from `S` and
`Q`. An isolated vertex of `A` has all its ambient neighbors selected and has
ambient degree at least two. Only the lower bound on the combined matching is
needed; no unproved matching-decomposition equality is used.

`ForestCounting` proves edges plus components equals vertices by summing the
actual component trees, including empty graphs. `EdgePartitionCounts` proves
the induced and crossing edge identities. `TotalDominationForestBudget` then
establishes the exact budget outside one fixed total dominating set `D`:

```
e(V\D) + sum_{x outside D} (|N(x)∩D|-1) + 1 = components(T[D]).
```

This bounds the degree of each outside vertex. It also bounds the number of
components of maximum-degree vertices outside `D`. Components inside `D` are
charged injectively to distinct edges of `T[D]`. The final case split proves
`c(M)+1≤|D|` and `dd+2c(M)≤2|D|+1`. These imply the submitted rational
strengthening. The degree-two case uses the same budget without a separate
path classification. The original bound includes a direct two-vertex boundary
case; natural subtraction does not replace either rational target fraction.

The unchanged `WOWII412dCore`, `WOWII412dAssembly`, `CoronaExchange`, and
`PendantSupport` sources are inherited from certificate commit
`07027a2c73bfa6802c0acbc7ab51788214b4ef78`. Only the already proved
adjacent-leaf exclusion in `PendantSupport` is needed by 393a. These foundations
are included in the fresh replay and input hash manifest.

## Verification

Official Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` are pinned by the repository.
The check script builds both statement modules with warnings as errors and
freshly exports eleven proof/audit modules with warnings as errors and implicit
variables disabled. `WOWII379393Audit` checks all three exact target types and
twelve transitive axiom sets. The only allowed axioms are `propext`,
`Classical.choice`, and `Quot.sound`; a `sorryAx` negative control must fail
that whitelist. No native-evaluation axiom is accepted.

From this certificate checkout, with the official toolchain and Mathlib cache:

```bash
bash Proofs/WOWII379393Validation/check.sh
```

The recorded sandbox run sets `LD_PRELOAD` to a small executable-path adapter.
Its complete source and hash are included. It only retries the failed
`readlink(/proc/<current-pid>/exe)` as `/proc/self/exe`; it does not replace or
patch Lean, the kernel, source files or proof terms. A normal environment does
not need this adapter. Empty module logs mean successful warning-free exports.

Long proofs remain external under `PROOFS.md`. Statement files retain the
required `by sorry` bodies and link to complete external certificates.
Kernel verification, upstream CI, human review and repository admission are
separate statuses. No new human approval or merge is claimed by these logs.

Written sources: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization,
the shortened counting routes, validation and submission preparation.
