# Complete Lean certificates for WOWII 412a, 412b and 412e

This package completes the two existing submissions #7374 and #7375. It proves
all six exact submitted targets, with their original definitions and hypotheses:

| Target | Certificate in `WOWII412FamilyProof` |
|---|---|
| Literal-neighborhood WOWII 412e | `conjecture412e` |
| Stronger external-neighborhood 412e | `conjecture412e_external` |
| Original bipartite WOWII 412a | `conjecture412a` |
| Original bipartite WOWII 412b | `conjecture412b` |
| General corona strengthening of 412a | `conjecture412a_corona` |
| General corona strengthening of 412b | `conjecture412b_corona` |

Literal neighborhoods may meet their input set. External neighborhoods subtract
that set. The maximum critical union uses greatest cardinality among independent
integer-difference maximizers. The largest-component invariant counts vertices
and has value zero on the empty induced graph. No rounding, extra connectivity
assumption or substituted domination parameter is introduced.

## Sources and reused foundations

Written sources: Jonas J. Gebendorfer, both dated 1 September 2026:

- [A neighborhood-exchange bound for maximum critical independent sets](https://github.com/user-attachments/files/33373335/Gebendorfer_WOWII_412e_Intake_2026-10-13.zip), Theorems 3.1 and 4.1.
- [Pendant-Support Inequalities for Graph Coronas and Resolutions of WOWII 412a and 412b](https://github.com/user-attachments/files/33356703/Jonas_Gebendorfer_WOWII_412ab_submission_R1_2026-09-01.zip), the paired corona theorem and its bipartite consequences.

Both manuscripts, their source locks and the frozen WOWII rows/definitions were
read. Frozen source hashes are `8af2a12bcad483e4577963585b8bfc12abe1fca2521e1137ff827e8e8d647d59`
for the HTML and `695b7262acbf4398a88530e7375715912e4a1ac628ad9be2e56ecd122023a703`
for the definition script. The source's standard critical-set characterization
remains credited to Larson, Levit–Mandrescu and Jarden–Levit–Mandrescu. No new
literature-priority or expert-review claim is made.

Two existing files are reused unchanged:

- `WOWII412dCore.lean`, blob `9860f8a4c1931f5d33191fd5561783dc9ec7b1e4`,
  supplies finite maximum independent sets and the bipartite critical-union bridge.
- `WOWII412dAssembly.lean`, blob `ed327805d4d1c4bc487e28ab6c098ec0a65a12f8`,
  supplies the bipartition existence wrapper. Its other, historically partial
  412d reductions are not substituted for a proof of any target here.

The adjacent-leaf exclusion in `PendantSupport.lean` reuses the argument already
certified in `WOWII404406Proof.leaf_neighbor_not_leaf` at commit
`243826dd990147445ee0023b90ce064ffec7c724`. It is restated in the minimal helper
module so these certificates do not import unrelated 404–407 statement files.
The existing 412d total-domination certificate is a separate completed package.

## Formal construction

`CoronaExchange.lean` proves leaf exchanges and strict Hall for an independent
set outside the corona in an arbitrary graph. Its reservation lemma needs only
a cardinality bound, so strict Hall is applied to that entire set, rather than
constructing the manuscript's full matching. If the reserved corona set has at
most one vertex, the strict surplus pays for it. If it has no edges into the
outside set, its cardinality is added as a disjoint summand.

`SupportComponentBounds.lean` selects distinct pendants for the supports in a
component and pays for the component with those reserved vertices. For 412a,
the independent set lies outside the supports' neighborhood. For 412b, a local
exchange puts every degree-two support adjacent to another support into the
corona, removing the only obstruction. The component supremum is handled with
its actual connected-component type, including the empty case.

`WOWII412eBounds.lean` proves both neighborhood conventions. In the literal
case, every vertex of the twice-nested set has a pendant outside its induced
neighborhood; reserve it. In the external case, the pendants and the induced
neighbor set form a disjoint independent union. With at most one pendant the
twice-nested set is independent, so the induced maximum degree is zero; the
bipartite independence lower bound handles that boundary.

`WOWII412FamilyProof.lean` identifies the exact submitted definitions, including
instance-independent degrees, and derives all six targets. The audit restates
the actual PR target types and checks their transitive axiom closures.

OpenAI Codex assisted with the cardinality reservation route, formalization and
validation. Reused lemmas and repository dependency builds are not counted as
newly proved conjectures.

## Reproduction

Use official Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
The certificate is based on statement commit `97e88b93ad62d7518b7d400d90773cfbd40f0e48`
and includes the exact 412a/b file from `9c8d760f4c40fb54a734751d3371d8097febf9ed`.

```bash
lake exe cache get
bash Proofs/WOWII412FamilyValidation/check.sh
```

All nine proof/audit modules are freshly exported with warnings as errors and
implicit variables disabled. Ten axiom checks, including all six final targets,
allow only `propext`, `Classical.choice` and `Quot.sound`. A negative control
confirms rejection of `sorryAx`. The statement repository retains its normal
external-proof placeholders; those placeholders do not enter these certificates.

Validation logs, checksums and metadata are in `WOWII412FamilyValidation/`.
The disclosed `environment/process_path.c` adapter retries only a failed numeric
lookup of the current process executable through `/proc/self/exe`. The sandbox
needs it; ordinary systems do not. Official Lean binaries, kernel rules and
mathematical axioms are unchanged.

The accompanying submission audit records the live PR and CI states **before**
these two certificate updates. Proof compilation, successful CI, human review
and upstream admission remain distinct statuses. The package does not assert
new equality classifications, a nonbipartite critical-union theorem, or curator
acceptance.
