# WOWII 252: full finite counterexample certificate

The theorem `WOWII252Proof.conjecture252` negates the complete universal
statement on connected finite simple graphs without isolated vertices.
The explicit isolation condition ensures that total domination is defined;
it prevents Lean's empty-infimum default from creating a spurious singleton case. The supplied manuscript by
Jonas J. Gebendorfer specifies the actual 30-vertex witness and all its edges.
Intake: https://github.com/google-deepmind/formal-conjectures/issues/7262

The graph has no four-cycle, including noninduced four-cycles. Its unique
modal degree is 7 and its total domination number is exactly 6.

Connectivity uses an actual decreasing-depth parent certificate. The minimum
total domination number uses six pairwise disjoint open neighborhoods,
an injective choice argument for an arbitrary dominating set, and a matching
six-vertex upper certificate. There is no exponential subset enumeration.

`WOWIIModalDefinitions.lean` proves that `modeMin` is the least maximizer of
degree frequency over ALL natural degree values, not a frequency or an
unjustified bounded surrogate. The four-cycle predicate excludes arbitrary
length-four cycle walks; extra chords do not affect it. The separate audit
checks every degree frequency and rejects a damaged dominating set.

Ordinary kernel reduction checks the finite adjacency, degree, parent and
common-neighborhood tables. No native evaluation or extra axioms are used.
Official Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
All proof and audit modules compile with warnings as errors and implicit
variables disabled. Printed axiom profiles contain only propext,
Classical.choice, Quot.sound. The actual checked logs are included.

Run `sh Proofs/check-WOWII252.sh` in the pinned Formal Conjectures project.

No minimum-order, infinite-family, external review or exclusive priority
claim is made. OpenAI Codex assisted with formalization.
