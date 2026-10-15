# WOWII 433-M: full 52-vertex counterexample certificate

This certificate refutes precisely the reconstructed maximum-degree / upper
reading in issue https://github.com/google-deepmind/formal-conjectures/issues/7274
The primary row declares pendants P but displays M, has a missing comparison
sign, and lies under a lower-bound heading. No historical intent is recovered.
The source is Jonas J. Gebendorfer's manuscript of 6 September 2026.

The actual graph is the supplied 52-vertex split graph: a clique on thirteen
points, three copies of each translate of {0,1,3,9} modulo thirteen, and the
extra edge c0--x_(1,0). The audit matches every adjacency entry to this constructor.
Its proof establishes independent domination number exactly 27 and RHS exactly 25.

Every independent dominating set is handled explicitly: either it contains a
clique vertex c, forcing c and every outer nonneighbor into the set; or it
contains no clique vertex, forcing every outer vertex. The cardinality lower
bounds are checked for all thirteen clique cases. A 27-vertex independent
dominating set proves the matching upper bound. There is no 2^52 subset search.

Actual walks of length at most two show that Mathlib's distance-defined graph
square is K52. Thus every square degree is 51. The maximum-degree set is {c0}
and its OPEN neighborhood has size 25. The sum of reciprocal square degrees is
52/51, the floor of twice that sum is 2, and the rational RHS is (25/2)*2=25.
The audit checks the distinct closed-neighborhood count 26 and the extra edge
that breaks independence of {c0,x_(1,0)}.

The theorem `WOWII433Proof.conjecture433_upper_M` negates the entire specified
universal statement on connected finite simple graphs with more than three
vertices. The additional family, connectivity-four and minimum-order-within-
family results of the manuscript are not claimed as formalized.

Official Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Complete proof and audit compile with warnings as errors and implicit variables
disabled. No sorry, custom axioms or native evaluation. All printed profiles use
only propext, Classical.choice, Quot.sound. Run `sh Proofs/check-WOWII433.sh` in
the pinned Formal Conjectures project. Actual checked logs are included.
OpenAI Codex assisted with formalization. No external-review or priority claim.
