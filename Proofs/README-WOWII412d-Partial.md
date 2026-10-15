# WOWII 412d: partial Lean development

This is NOT a complete proof of WOWII 412d. There is no global target theorem
or `formal_proof` claim. Source: Jonas J. Gebendorfer's 11 October 2026 paper,
https://github.com/google-deepmind/formal-conjectures/issues/7226

`WOWII412dCore.lean` proves the following universal finite-graph results:

- explicit independent, maximum, critical and maximum-cardinality critical
  predicates, with open-neighborhood difference over integers;
- existence and domination of a maximum independent set;
- in a bipartite graph, maximum critical sets are exactly maximum independent
  sets, and consequently their unions agree;
- closure under the two bipartition lattice operations and the extremal sets
  consisting of the A-side corona and complement-side core;
- the complement of the corona equals the open neighborhood of the core;
- for every nonempty X outside the corona, |N(X) intersect core| >= |X|+1;
- every vertex of corona minus core has a neighbor in that same remainder.

The criticality step uses two mixed independent sets directly, avoiding a
separate formalization of matching/cover equality. The remainder argument
also avoids the perfect-matching step. Both are explicit kernel-checked proofs.

`WOWII412dAssembly.lean` bridges Mathlib's `IsBipartite` to the finite
bipartition representation, proves the complete empty-core case, and assembles
the bound GIVEN a core/excluded total cover of size at most the core. That
cover is an explicit theorem hypothesis, not an axiom and not established in
the nonempty-core case.

Still missing: the strict-Hall forest-selection construction and the forest
covering/packing argument that supply the nonempty-core cover. No finite
computation is substituted for these universal obligations.

Official Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Both files compile with warnings as errors and implicit variables disabled.
The nine printed axiom profiles use only propext, Classical.choice, Quot.sound.
Run `sh Proofs/check-WOWII412d-Partial.sh` in the pinned project.
OpenAI Codex assisted with formalization. This checkpoint is not counted as
an additional solved conjecture or a complete submission.
