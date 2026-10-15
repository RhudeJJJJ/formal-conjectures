# WOWII 422d-U — complete finite counterexample

Jonas J. Gebendorfer, 15 October 2026. OpenAI Codex assisted with formalization.
Source: Gebendorfer, *WOWII 422d: ein Gegenbeispiel auf zwölf Knoten und eine
unbeschränkte Lücke*, 7 September 2026, and submission
https://github.com/google-deepmind/formal-conjectures/issues/7271

This certifies the explicitly reconstructed UPPER reading with NONPROPER
closed-neighborhood containment. The historical comparison glyph is missing;
the containing source heading says lower bounds. This is a documented variant,
not a recovery of the historical intent.

`WOWII422dProof.conjecture422d_upper` refutes the universal upper reading on
connected finite simple graphs of order greater than three. Define D to contain
v if N[u] is a subset of N[v] for some u different from v, admitting true twins.
The claimed bound is i(G) <= alpha(G[V minus D]) + floor((edges(G[D])+1)/3).

The actual 12-vertex graph has i(G)=4 and right side 3. Its adjacency is explicit;
connectedness is proved by paths to a root. D is exactly vertices 4 through 11;
the induced D graph has four edges, and the residual independence number is two.
The lower domination bound is a kernel-checked exhaustive certificate over all
4096 candidate vertex sets, and {0,1,8,10} attains four. Standard repository
definitions of independent domination and independence are used.

The separate audit identifies the predicate with nonproper containment of
closed neighbor SETS, proves that the strict-containment D is empty on this
same graph, and rejects the two damaged candidate sets from the manuscript.
The infinite family, unbounded deficit, strict-reading repair theorem, and
minimum counterexample order are not claimed as formalized by this certificate.

## Reproduce

Use official Lean 4.33.1 and pinned Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
Run `bash Proofs/check-WOWII422d.sh` from the repository root.
Both proof and audit compiled with warnings as errors and implicit variables
disabled. All printed final/audit theorems use only `propext`, `Classical.choice`,
and `Quot.sound`. There is no `sorry`, custom axiom, or `native_decide`.
Local successful output is `WOWII422d-checked.log`.
The hosted executable-path readlink adapter described in README-WOWII363.md
was used; the official Lean binary and kernel were unchanged.
