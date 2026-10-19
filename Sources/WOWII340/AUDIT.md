# Source and proof audit, October 19, 2026

The supplied eight-page manuscript was read in full. Pages 2–5 were also
rendered and visually inspected, including the double-broom figure, the
sets, the packing certificates, and the real-number estimates.

Theorem 4.3 has a valid direct construction: its eight open neighborhoods
and five closed neighborhoods are pairwise disjoint. The explicit upper
bound sets meet every required neighborhood. The leaf-support subgraph is
two stars, and the degree frequencies give the stated smallest mode.
The one-ended family and the estimates in Lemma 5.4 and Theorems 5.5–5.6
were checked on paper, including the negative-alpha case. No gap was
identified in those analytic arguments.

The exact original row 340 and all five needed definitions were read from
the retained Internet Archive capture bytes after gzip decompression.
In particular, definition 45 explicitly chooses the smaller mode in a tie.
The archived open marker is historical evidence only.

The Lean target is the negation of the original universal statement, with
all finite simple trees of order greater than two quantified. The explicit
D(5,5) witness suffices to decide it. The exact invariants are the repository's
domination and total-domination numbers, quotient connected components of
the induced leaf-support subgraph, and a finite-frequency definition of the
smallest degree mode.

The general families, the unbounded deficit, the coefficient question, and
the census are not claimed as Lean-certified. The separate reproducibility
ZIP was not supplied; the census and its global minimality claim have not
been replayed here. Finite controls independently reconstruct D(5,5),
D(5,6) (unique mode), and D(4,5) (below the mode threshold). These controls
check explicit sets and packings, not all trees.

The local Lean import attempt was explicitly cancelled after 156.58 seconds
because the system drive had roughly 250 MB free; it produced no proof
result. The definitive validation is the exact pinned Linux CI run, whose
completed status and axiom output must be inspected separately.
