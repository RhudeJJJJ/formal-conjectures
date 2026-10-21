# Exact original correlated-escape algebraic reduction

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**PROVEN: exact factored identities for the same original directed and full-reserve expressions. The original integer-table clearing identities remain OPEN.**

For the same quadratic coefficients a,bx,bt,c and Schur center (2-d)+i*(y+r), let H0 be its value at 2+i*y, X=4*a+bx, Delta=2*a*y+bt and U=H0+a*d^2-d*X. The checked translation identities are

    directed = 4*a*(U+r*Delta+2*a*r^2),
    reserve = 16*a^2*(U^2+2*U*r*Delta+r^2*(4*a*H0-X^2)).

In particular the r^4 and r^3 terms cancel exactly before the large denominator-clearing calculation. The exact original cubic weight is retained, with errorWeight(t)=-t*(1-t/2+t^2/6)=cubic(t)-1. Its factored leading coefficient, anchor value and horizontal/vertical offsets are proved from the original Focus A,B,N0,D0 coefficients. The same original directed and full-reserve functions are rewritten; no sign condition, parameter box, graph pair, original coefficient or squared term is replaced.

[Run 39521603103](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39521603103), job 118966501821, succeeds at [source 5b4a0563f1a57199fe2f21b7c141644cf7e5d144](https://github.com/RhudeJJJJ/formal-conjectures/tree/5b4a0563f1a57199fe2f21b7c141644cf7e5d144/Proofs/RG_Lean_20261019). The completed 64-module closure has one fresh algebraic module and 63 explicitly verified prior-job imports. The additional 176 collected records include unused imports and do not enlarge the endpoint. Source, full dependency-closure and object hashes and original artifact digests are checked before reuse. Official Lean 4.33.1, pinned Mathlib, warnings as errors and standard axioms only are used.

These functional algebraic identities do not establish that the large stored integer tables equal the positively cleared functions. Those original table-to-form equalities are separate ongoing checks. The first directed run was interrupted by runner shutdown (exit143); the first reserve repair reached its 3600-second module limit. Neither event is a mathematical counterexample. Both targets and all table coefficients are retained in the new proof attempts.

All seven complete OriginalAssembly.Inputs families and the universal Lean theorem remain OPEN. The separate written computer-assisted theorem is unchanged. Aletheion was untouched under the user's instruction.
