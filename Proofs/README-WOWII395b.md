# Complete Lean certificate: WOWII 395b

The certificate refutes the original upper bound on a connected fifteen-vertex graph: gamma_2 = 6 and proposed bound = 5. The bound uses the smallest modal degree class, the induced minimum degree after deleting the original minimum-degree vertices, and the number of vertices of ambient degree below three. The remainder is required nonempty, so no empty induced minimum-degree convention enters the disproof.

Three clique blocks each contain two private vertices. The proof forces two selections in each block and exhibits a matching six-vertex set. Connectivity is proved using an explicit strictly descending spanning-parent certificate. Degree calculations, the unique modal degree six and the induced minimum degree one are exact finite kernel reductions. The audit specifies all thirty-eight edges separately from the proof's clique constructor and proves that the two graph inputs coincide.

Written source and precise notation: Jonas J. Gebendorfer, A fifteen-vertex counterexample to Written on the Wall II Conjecture 395b, 14 October 2026; intake https://github.com/google-deepmind/formal-conjectures/issues/7330 . Source row 395b links to definitions 90/45/100/56/66; the Symbol-font d is minimum degree. The witness has a unique mode. The manuscript's unbounded connector family is not formalized here.

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with source comparison, formalization, execution, and submission. The complete proofs use no sorry, custom axiom, native_decide, compiler-trust evaluation, or upstream placeholder theorem. Ordinary decide is reduced by Lean's kernel.

Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 are pinned by lean-toolchain and lake-manifest.json. Check out this certificate commit and obtain the pinned Mathlib cache before running the commands below. The separate audit repeats the definitions and exact quantified statement in another namespace, checking agreement and printing all relevant axiom dependencies. The plucking audit proves agreement of the recursive parent paths and polynomial by induction.

The supplied manuscript archive is attached to the intake issues: https://github.com/user-attachments/files/33452211/Gebendorfer_New_Manuscripts_2026-10-14.zip . Original authoring supplements mentioned inside those PDFs were not supplied in this batch. The archive clearly labels its fresh bounded Python checks separately. A source's historical open marker is not a fresh curator decision. No exclusive priority or independent external peer review is asserted.

The hosted audit runtime required a narrow readlink compatibility shim: only a failed /proc/own-pid/exe lookup was retried at /proc/self/exe. The official Lean binary and kernel were unchanged. The official archive SHA256 is 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Ordinary installations do not require the shim.

The upstream contribution is a statement module with a formal_proof link to this complete external proof, as PROOFS.md requests. An upstream by sorry placeholder is not claimed to be a proof; the external files and exact-statement audit have no such dependency. Formalization strengthens evidence for an existing written result and does not constitute an additional conjecture closure.

## Reproduce

```sh
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Proofs/WOWII395bProof.olean Proofs/WOWII395bProof.lean
lake env lean -DwarningAsError=true Proofs/WOWII395bAudit.lean
```

The printed reports must contain only propext, Classical.choice and Quot.sound, or fewer. A successful build alone is not sufficient; inspect the exact theorem and these axiom reports.

