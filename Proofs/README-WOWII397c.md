# Complete Lean certificate: WOWII 397c

The certificate proves the full universal original bound gamma_2(G) <= |V minus N(P)| + gamma(G^2) for every finite simple connected graph with more than two vertices. Supports are the union of open neighborhoods of all degree-one vertices. The square joins distinct vertices linked by one or two original edges; the audit additionally proves its equivalence to existence of an original walk of length at most two.

The argument is constructive at the set level. Map selected leaves to their unique neighbors, keep selected nonleaves, and adjoin the complement of the support set. Every omitted support has its own selected leaf and a distinct selected original neighbor. A separate proof derives the absence of adjacent leaves from connectedness and order greater than two; it is not an extra assumption on the original conjecture. A minimum square dominator dominates the original support set.

Written source: Jonas J. Gebendorfer, 2-domination and domination of the square: a constructive proof of Written on the Wall II 397c, 14 October 2026; intake https://github.com/google-deepmind/formal-conjectures/issues/7331 . The retained source row cites definitions 90/46/66/49/75. K2 really violates the bound. The certificate covers the universal conjecture and transport cost bound; it does not formalize the manuscript's corona equality families, refined restricted-input cost, algorithmic runtime, or coefficient optimality.

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with source comparison, formalization, execution, and submission. The complete proofs use no sorry, custom axiom, native_decide, compiler-trust evaluation, or upstream placeholder theorem. Ordinary decide is reduced by Lean's kernel.

Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 are pinned by lean-toolchain and lake-manifest.json. Check out this certificate commit and obtain the pinned Mathlib cache before running the commands below. The separate audit repeats the definitions and exact quantified statement in another namespace, checking agreement and printing all relevant axiom dependencies. The plucking audit proves agreement of the recursive parent paths and polynomial by induction.

The supplied manuscript archive is attached to the intake issues: https://github.com/user-attachments/files/33452211/Gebendorfer_New_Manuscripts_2026-10-14.zip . Original authoring supplements mentioned inside those PDFs were not supplied in this batch. The archive clearly labels its fresh bounded Python checks separately. A source's historical open marker is not a fresh curator decision. No exclusive priority or independent external peer review is asserted.

The hosted audit runtime required a narrow readlink compatibility shim: only a failed /proc/own-pid/exe lookup was retried at /proc/self/exe. The official Lean binary and kernel were unchanged. The official archive SHA256 is 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Ordinary installations do not require the shim.

The upstream contribution is a statement module with a formal_proof link to this complete external proof, as PROOFS.md requests. An upstream by sorry placeholder is not claimed to be a proof; the external files and exact-statement audit have no such dependency. Formalization strengthens evidence for an existing written result and does not constitute an additional conjecture closure.

## Reproduce

```sh
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Proofs/WOWII397cProof.olean Proofs/WOWII397cProof.lean
lake env lean -DwarningAsError=true Proofs/WOWII397cAudit.lean
```

The printed reports must contain only propext, Classical.choice and Quot.sound, or fewer. A successful build alone is not sufficient; inspect the exact theorem and these axiom reports.

