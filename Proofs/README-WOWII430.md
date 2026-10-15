# WOWII 430c: complete upper/M and upper/center certificates

These files refute the two explicitly reconstructed upper-bound readings in
https://github.com/google-deepmind/formal-conjectures/issues/7273
The primary row declares C but displays M, omits the comparison glyph and lies
under a lower-bound heading. Historical intent is not claimed. The written
source is Jonas J. Gebendorfer, 7 September 2026. Codex assisted with formalization.

The witness is the source's 105-vertex split graph: 21 clique points and four
independent copies of every translate of {0,1,4,14,16} modulo 21. The audit
matches every adjacency entry to that construction. Actual short walks prove
connectedness and identify its distance-defined square with K105.

Every independent dominating set is covered by the clique-vertex / no-clique
case distinction. This gives independent domination number exactly 65, with
an explicit matching set. No enumeration of all 2^105 subsets is used.

Every independent set in any open neighborhood has size at most 20. The proof
handles a possible clique vertex and bounds the forced remaining outer set,
then transports arbitrary maximum independent sets of the induced neighborhood.
Thus Mathlib's maxLocalIndependence is at most 20. This is local independence,
not an eigenvalue. Every induced subgraph has maximum degree at most 40.

The actual Havel–Hakimi residue of the square is 1. A general induction proves
residueAux(replicate (n+1) n)=1: each step transforms the complete-graph degree
sequence into the next smaller one. The sorted degree multiset is explicitly
identified with the constant list. This uses the existing residue definition.

Consequently, for EVERY vertex subset S the proposed RHS is at most 60 < 65.
This simultaneously refutes the M and center readings, with their actual
maximum-degree and standard eccentricity/radius center definitions. The audit
proves that the finite center agrees with Mathlib's center. No exact RHS 40
for M, full counterfamily or source-wide historical-intent claim is made here.

Official Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
The complete sources compile with warnings as errors and implicit variables
disabled. No sorry, native evaluation or custom axioms. The printed profiles
use only propext, Classical.choice and Quot.sound. Run sh Proofs/check-WOWII430.sh
in the pinned Formal Conjectures project. Actual proof/audit logs are included.
The upstream statement remains separate under PROOFS.md. No external review or
upstream merge is claimed.
