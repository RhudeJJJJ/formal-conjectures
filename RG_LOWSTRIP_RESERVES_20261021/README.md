# Exact symmetric full-reserve components

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

The checked full reserve has the exact factorization R=16*a^2*inner, where a is the original leading coefficient. With original anchor H0, horizontal X, vertical offset Delta and U=H0+a*d^2-d*X,

    inner=U^2+2*U*r*Delta+r^2*(4*a*H0-X^2).

This retains the complete squared reserve. No original directed or reserve term is dropped.

For nonnegative arm increments s=P-y,t=Q-y use the exact symmetric quantities N=s*t, W=(s-t)^2 and M=s+t. The new mixed-domain checker uses power coefficients in these unbounded nonnegative quantities and Bernstein coefficients only in bounded coordinates. Its soundness is proved, and its finite acceptance computations use the Lean kernel.

For the original constant target c=1, write d=8/(3*y)+v. The complete reduced polynomial has 2,550 coefficients with unbounded nonnegative v,N,W,M and bounded Y=2*y. Its positive scale is 84934656. The exact equality

    eval(data,[v,s*t,(s-t)^2,s+t,2*y])
      =84934656*y^4*inner(8/(3*y)+v,y,y+s,y+t,1)

and original_inner_nonneg are both proved for every v>=0, 0<y<=1/2 and P,Q>=y. The same original full reserve translation is proved from the Focus coefficients. The explicit combined transfer to the original graph strip ranges is also checked in the subsequent assembly endpoint below.

For the tangent curve y=4*c*h/(1-c^2), 0<h<=1/46, 0<c<=1/2, the complete reduced symmetric polynomial has 16,830 coefficients in N,W,M,H=46*h,C=2*c and positive integer scale 1685719115165366705018091480285184. Its complete polynomial nonnegativity and exact definitional evaluation are proved. Its exact equality to scale*h^4*c^2*(1-c^2)^12*inner(1/h,y,P,Q,c) and original_inner_nonneg are also proved.

The same actual core C, root u and physical arms p+1,q+1 are used in LowStripReserves and HighDegreeInputFromEscape.normalized_target_of_escape_signs. Both original full-reserve families are discharged on the original tangent relation and constant interval for every root degree>=46. Together with the independently proved original outside and directed conditions, the exact original target 2/47 < normalizedIntegral C u p q 2 now requires only the original correlated-escape Signs. The subsequent exact degree46 assembly discharges those same original escape signs and supplies degreeGeFortysix without additional proof hypotheses.

## Verification

- [Run 39527783221](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39527783221), job 118986382063, source 0bb9e7bf55f35d132f396205b29eb07d1ef8f2b2: 75 endpoint modules, 3 fresh and 72 explicitly verified prior exports.
- [Run 39526376712](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39526376712), job 118981866160, source 365f4a1a20e645cf7a572d2cfd5f6fb50e8c42e5: 13 endpoint modules, 2 fresh and 11 explicitly verified prior exports.
- [Run 39528286100](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39528286100), job 118987987405, source 8fb2b2980f6ad1fe329f189cf34d25e64c0e7bc8: 75 endpoint modules, 2 fresh and 73 explicitly verified prior exports.
- [Run 39529790803](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39529790803), job 118992800617, source abd4bb594e650df9e08c7202c94a18f7aee57e55: 86 endpoint modules, 2 fresh and 84 explicitly verified prior exports.

The collections of individual records contain unused restored modules and do not enlarge an endpoint. Official Lean 4.33.1, pinned Mathlib, warnings as errors and standard axioms only are used. Source, complete local dependency-closure, object and original artifact hashes are checked before reuse. Distinct receipts are not one fresh global build.

The exact original degreeGeFortysix family is proved in the subsequent assembly. The other six complete OriginalAssembly.Inputs families and the universal Lean theorem remain OPEN. Other degree ranges and finite census completeness remain separate work. The original escape signs are proved on their complete original box. The written computer-assisted theorem is separate. Aletheion was untouched under the user's instruction.
