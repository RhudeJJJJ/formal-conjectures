# Original Radenkovic-Gutman low-strip calculus

This partial Lean continuation proves the singular scalar integral used by the original degree-at-least-46 low-strip payment. It does not prove the pointwise graph comparisons or the complete degree family.

For every real s>0, P(s)=s*log(2+sqrt(s^2+4))-s*log(s)+2*arsinh(s/2) equals s*arsinh(2/s)+2*arsinh(s/2), and P'(s)=arsinh(2/s). The extension has P(0)=0 and is continuous at zero. For every B>0, arsinh(2/s) is integrable on (0,B], and its integral from 0 to B is P(B). In particular,

    integral from 0 to 8/3 of arsinh(2/s) ds = (8/3)*log(2)+2*log(3).

The integrability proof bounds arsinh(x), for x>=0, by log(2)+(1/2)*log(1+x^2) and uses the already proved scalar logarithmic kernel. No singular endpoint is omitted.

The exact three-module closure was freshly exported with Lean 4.33.1, warnings as errors, no sorry/admit/native_decide or new axioms. Printed axiom profiles contain only propext, Classical.choice and Quot.sound. Mathlib is pinned to 0df444a360eaa60ab8c11dca51a86af692955474. All 87 predecessor Lean sources at baseline 658a1eff4995058c71f0873f623ac48f50448136 are byte-identical.

The original target for 0<s=d*y<=8/3 is log modulus >=-arsinh(2/s)-log(2); the subsequent strip uses >=-log(2). Substituting the checked integral gives the original proposed payment (-(8/3)*log(2)-2*log(3))/d-log(2)/2. That graph payment still needs its original pointwise comparisons and scaling/interval assembly. The tangent outside/directed/full-reserve certificates in all three physical parity cases and the constant-strip chart signs remain OPEN. The physical arm boxes and tangent leading positivity are retained separately.

All seven complete OriginalAssembly.Inputs fields, the uniform strict-fusion theorem from source order five, and the universal Lean minimum/equality conclusion remain OPEN. The written computer-assisted theorem is a separate result. No full 1302-witness replay, full-paper reading, review acceptance or merge is claimed.

Verification source: e10830073a90a1a88103706ebc8b71bd33bdf60e; run 39505370942, job 118912838144. This receipt proves the stated calculus closure only. The concurrent correlated-escape coefficient and symbolic-identity work has its own receipts and is not inferred from this one. Aletheion was left untouched under the current user instruction.

The original convex disk criterion is also checked, in a separate fresh 51-module closure at source ba4dfb71755803218e8630cb34635b46fda837e4, run 39505653814, job 118913781380. For a strictly convex real quadratic H(z)=a*normSq(z)+bx*re(z)+bt*im(z)+c on the same disk of centre g and radius r>=0, the three original conditions outside>=0, directed>=0 and full reserve>=0 imply H(z)>=0 throughout the disk. The outside term is gradientSq-4*(a*r)^2; the full reserve is directed^2-16*(a*r)^2*gradientSq. The criterion retains all three conditions. It does not assert the required tangent-strip polynomial signs. The two receipts concern distinct explicit closures; their counts are not added as one job.

The joint 68-module closure at source 015d9111af0836604ee8edf81c87e4a2699074e9, run 39509661477, job 118927240676 freshly checks the complete scalar calculus, convex disk criterion and their actual-graph bridges in one job. LowStripPrimitive.original_graph_lowstrip_lower proves the exact original integral payment under the two original pointwise graph comparisons on (0,8/(3*d)] and [8/(3*d),1/2]. The singular endpoint is handled by integrability, and the intervals leave no gap. LowStripGeometry.tangent_graph_lower_of_actual_signs proves the actual quotient lower bound for the original c coordinate satisfying d*y=4*c/(1-c^2), under the original outside, directed and full-reserve signs. This includes an exact symbolic identity for the source Apollonius quadratic. The same C,u and physical arms p+1,q+1 are retained. The pointwise sign families, coordinate coverage and original constant-strip charts are separate remaining obligations; no complete Input field is obtained.
