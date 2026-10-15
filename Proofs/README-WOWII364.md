# WOWII 364: complete P4 certificate

The theorem `WOWII364Proof.conjecture364` refutes the explicitly transcribed
half-edge statement for every finite simple tree of order greater than two.
The half factor applies only to the induced degree-two edge count.

The actual four-vertex path has two supports, one induced degree-two edge and
total domination number exactly two. Its proposed lower bound is 5/2.
`WOWII364Audit` checks the leaf/support predicate, all degrees, a damaged total
dominating set, and the full universal target type. The P4 witness satisfies
the distinct strengthened bracketed inequality; that inequality is not refuted.

The P4 counterexample was already publicly reported by Siddhant Dubey:
https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa
The supplied undated manuscript by Jonas J. Gebendorfer gives further family
and repair results, which are not claimed as formalized here. Original intake:
https://github.com/google-deepmind/formal-conjectures/issues/7275

The supplied source freeze omits the historical fraction glyph in its HTML
rendering. The manuscript's archive-evidence record and the public Kuber
transcription explicitly state 1/2. This certificate fixes that version; it
does not recover unavailable historical program output or curatorial intent.

Checked with official Lean 4.33.1 and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. Complete proof files have no `sorry`,
custom axioms or native evaluation. Printed axiom profiles contain only
propext, Classical.choice, Quot.sound. See the actual checked logs.
Run `sh Proofs/check-WOWII364.sh` in the pinned Formal Conjectures project.
OpenAI Codex assisted with formalization. No new mathematical priority claimed.
