# Smaller exact original correlated-escape certificates

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

The same original cubic payment 42/(25*d*(1+x^2)), complete parameter box d>=46, 653/2000<=x<=10 and both arm parameters in [0,1] are retained. Exact factorizations of the unchanged original directed and full-reserve expressions are checked:

    directed=4*factorLead*directedCore,
    reserve=16*factorLead^2*reserveInner.

The complete squared reserve is retained. No different graph, independent numerator/denominator extrema, sampled arms, weakened sign or cutoff is used.

The new directed-core polynomial has 1,989 coefficients with degrees [12,16,2,2]. Its complete unit-box nonnegativity and exact functional clearing identity are both proved. With x=653/2000+(19347/2000)*U,

    eval(data,[46*h,U,a,b])=scale*h^5*x^6*(1+x^2)^3
       *directedCore(1/h,x/h,x/h+a*h/x,x/h+b*h/x,payment(1/h,x)),

where scale=4488115083677761740800000000000000000000000000000000000000000000000000. The normalized affine denominator, its square and the shifted positive denominator are proved nonzero before clearing. The original full-box data and target identity are unchanged.

The smaller full-reserve inner polynomial has 18,125 coefficients with degrees [24,28,4,4]. Its exact functional clearing and final original-sign assembly require their own completed endpoints; status is recorded in OBLIGATIONS.json. A runner shutdown after a kernel completion is not treated as a durable export, an original graph bound or a mathematical counterexample. Completed module records are now emitted individually, and the reserve certificate is exported before its identity check.

The two older large-table clearing identities remain separate historical work. They are not claimed established by these smaller exact identities. The objective remains the same original graph escape inequalities and exact normalized degree-46 margin.

## Verification

- [Run 39529425234](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39529425234), job 118991652054, source eb637b5c869b5a25277f2faeb3843e8924f3c282: 68 endpoint modules, 1 fresh and 67 explicitly verified prior exports.
- [Run 39530082786](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39530082786), job 118993712998, source 6ff4c0f904b122e5a6cefa6dbb52663eca547740: 12 endpoint modules, 1 fresh and 11 explicitly verified prior exports.
- [Run 39536480031](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39536480031), job 119014196559, source 95948e19c46f7f398cd11494db78ea1edde4924b: 98 endpoint modules, 28 fresh and 70 explicitly verified prior exports.
- [Run 39537952223](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39537952223), job 119018871409, source 7eb092e3530840c5074d7f0aeb20f74ecf28bc04: 125 endpoint modules, 4 fresh and 121 explicitly verified prior exports.

The full smaller reserve clearing identity is now proved. Its exact raw-coordinate polynomial is checked against the balanced original reserve, and twenty-five separate exact coefficient identities establish the complete affine transformation. Each row retains the corresponding power of 1/46. Recursive trailing-zero normalization preserves evaluation universally; altered-coefficient and rational-substitution controls accompany the checker. No sampled identity is used. The resulting equality has the unchanged original positive scale, h^10*x^8*(1+x^2)^6 and reserveInner target.

The subsequent explicit endpoint proves the unchanged original correlated directed and full-reserve signs throughout d>=46, 653/2000<=x<=10 and both arm parameters in [0,1]. Combined with the checked actual tangent and constant strips and tail, OriginalDegreeGeFortysix.normalized_lower proves 2/47 < normalizedIntegral C u p q 2 for every actual root degree>=46 and every physical arm pair. Its input_family supplies exactly the original seventh field, and strict_fusion proves the original energy decrease for tree sources. RemainingSixAssembly retains all original quantifiers of the other six complete fields. Those six fields and the universal Lean conclusion remain OPEN.

Unused imported records do not enlarge an endpoint. Official Lean 4.33.1, pinned Mathlib, warnings as errors and standard axioms only are used. Source, complete local dependency-closure, object and original artifact hashes are checked before reuse. Distinct receipts are not one fresh global replay. The universal Lean theorem remains OPEN; the written computer-assisted theorem is separate. Aletheion was untouched.
