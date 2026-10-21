# Original low-strip directed conditions discharged

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**PROVEN: the original directed condition for every physical arm pair at root degree at least four, in both the tangent and constant strips. Together with the proved outside condition, only the original complete reserve families remain in these two strips. The correlated-escape signs remain separate.**

From the same original Focus coefficients, put k=c^2/4, Aneg=4+2*(P^2+Q^2)+y*(P+Q)*(P*Q+1), Bneg=(P+Q-y)*(y*(P*Q-1)+2*(P+Q)). The checked coefficient identity is bx=-2*(Aneg-k*Bneg). For y>0, P,Q>=y and c in [0,1], the exact identity

    Aneg-Bneg/4 = 4+(3/2)*(P-Q)^2+2*P*Q+(3/4)*y*(P+Q)*P*Q
                  +(7/4)*y*(P+Q-2*y)+(13/4)*y^2+(1/4)*y^2*P*Q

proves bx<=0. At the original anchor 2+i*y, H0=(1-k)*(4+y^2)*(P*Q+1)^2>=0. For d>=4 and leading coefficient a>=0,

    U=H0+a*d^2-d*(4*a+bx)=H0+a*d*(d-4)-d*bx>=0.

The already proved offset Delta=2*a*y+bt is nonnegative. The exact same original directed expression equals 4*a*(U+r*Delta+2*a*r^2), hence is nonnegative. The original tangent and constant leading coefficients are strictly positive, giving `actual_tangent_directed` and `actual_constant_directed` for every physical arm pair p+1,q+1. No parity or ordinate relation is required for this sign itself.

`HighDegreeInputFromReserves.normalized_target_of_reserve_families` now proves the exact original degree-46 target **2/47 < normalizedIntegral C u p q 2** from the original tangent and constant **full reserve** families and original correlated-escape signs. The same C,u, arms, Schur disk and target are retained. The outside and directed conditions are proved, rather than deleted from the convex criterion.

[Run 39524674991](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39524674991), job 118976437384, succeeds at [source 82f9e827634780546d5a5de69fe58ba3fd14a89d](https://github.com/RhudeJJJJ/formal-conjectures/tree/82f9e827634780546d5a5de69fe58ba3fd14a89d/Proofs/RG_Lean_20261019). Its completed endpoint has **77 modules: thirteen fresh exports and 64 explicitly verified prior-job exports**. The 189 individual collected records include unused restored modules and do not enlarge the endpoint. Official Lean 4.33.1, pinned Mathlib, warnings as errors and standard axioms only are used. All imported source, complete local dependency-closure and object hashes and original artifact digests are checked. This is not one fresh global replay.

The low-strip and constant-strip full reserve squares, both original escape table-clearing equalities, final graph escape specialization, other degree ranges and finite census completeness remain separate work. This convex directed result does not discharge the concave correlated-escape directed condition. All seven complete OriginalAssembly.Inputs families and the universal Lean path-minimum/equality theorem remain OPEN. The written computer-assisted theorem remains separate. Aletheion was untouched under the user's instruction.
