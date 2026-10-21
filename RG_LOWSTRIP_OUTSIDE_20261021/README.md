# Original low-strip outside condition discharged

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**PROVEN: the original outside condition for every physical arm pair, in both the tangent and constant strips. The original directed and full-reserve conditions remain OPEN.**

Write a=LowStripGeometry.lead and bt=LowStripGeometry.bt. From exactly the original Focus coefficients, `LowStripOutside.vertical_offset_identity` proves

    2*a*y+bt = 2*(1-c^2/4)*(P*Q+1)*(y*(P*Q-1)+2*(P+Q)).

For y>0, P,Q>=y and 0<=c<=1 this offset is nonnegative. When a>=0 and d>=0, the Schur radius r=d/(2*y) is nonnegative, and the imaginary gradient at the same original center is 2*a*r plus this offset. Squaring proves the same original outside inequality gradientSq-4*(a*r)^2>=0. The tangent and constant leading coefficients are already strictly positive. `actual_tangent_outside` and `actual_constant_outside` specialize this result to the same C,u and actual physical arms p+1,q+1 for every y>0. No original outside premise, parity sample, different graph or different disk is introduced.

This one universal geometric condition covers all three physical parity boxes. Their separate directed and complete full-reserve conditions remain distinct obligations. The original outside test is proved rather than removed from the convex criterion. The singular endpoint y=0 is handled by the separate checked integrability argument; it is not part of this pointwise claim.

`HighDegreeInputFromTwoSigns.normalized_target_of_two_sign_families` proves the exact original `OriginalAssembly.Inputs.degreeGeFortysix` target, 2/47 < normalizedIntegral C u p q 2, from the remaining original tangent and constant directed/full-reserve families and the original correlated-escape signs. Thus the same target and physical graph pair are preserved. No complete Input field is inhabited.

## Verification

[Run 39520270649](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39520270649), job 118962141068, succeeded at [source aa598c0e60c1f3d4141a778007da2b42262a1e7e](https://github.com/RhudeJJJJ/formal-conjectures/tree/aa598c0e60c1f3d4141a778007da2b42262a1e7e/Proofs/RG_Lean_20261019). Its completed endpoint contains **74 modules, with eleven fresh exports and 63 explicitly identified prior-job exports**. This is a different endpoint from the earlier 74-module fresh LowStripCombined job; the counts are not added or conflated. The 186 individual records collected include unused earlier exports and do not enlarge the completed endpoint.

Source, full local dependency-closure and object hashes are checked before reuse, with the immutable original job and complete artifact digest retained. Official Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, warnings as errors and standard axioms only are used. All 87 predecessor sources are byte-identical.

## Exact remaining scope

The original low-strip directed and complete reserve signs, constant-strip chart signs, both original correlated-escape clearing identities and the final actual graph escape assembly remain separate work. The original odd/odd outside table and its positive clearing identity also succeeded independently in run 39518879837, but that narrower route is not needed to prove this universal outside condition.

All seven complete OriginalAssembly.Inputs families, remaining degree ranges, finite rooted-core census completeness and the universal Lean minimum/equality theorem remain OPEN. The written computer-assisted theorem remains separate. The current user's exclusion of Aletheion was respected: this insight is retained locally and in these research artifacts, without a central import.
