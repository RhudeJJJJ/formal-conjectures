# Complete Lean certificate: delayed plucking Open Problem 4.2

The certificate gives the negative answer to the general plane-rooted-tree formulation of Open Problem 4.2 in Ibarra, Landry, Montoya-Vega and Przytycki, arXiv:2311.18059v1, https://arxiv.org/html/2311.18059v1 . It does not contradict their anti-unimodal star theorem or the separately formalized binary-delay star Conjecture 4.1.

The plane rooted tree is represented by its ordered nonroot vertices with an implicit root. Each parent is either the root or a smaller vertex; this ensures finite parent chains and a unique path to the root. Children are ordered by labels, and the proved PreorderLabels condition makes the increasing leaf order the actual planar order. The witness parent array, with indices one less than the manuscript's nonroot labels, is [none,0,none,2,3,3,5,5]. The four initial leaves are [1,4,6,7], with delays [1,1,2,3].

RightOf counts incoming edges in sibling branches strictly right of the selected root path, using both actual parent paths. The polynomial is defined by the operational recurrence, not by a closed coefficient formula or removal-order reconstruction. Surviving old leaves decrement with floor one; newly exposed leaves receive one. The exact-cardinality recurrence is proved, so fuel n is sufficient for the n nonroot vertices. A general coefficient bridge to Polynomial Int is proved by induction. Kernel reductions yield coefficients 9,8,9 at degrees 10,11,12. These rule out every possible unimodal peak.

Definition 1.7 contains an ambiguous isolated zero-initial-condition phrase. As in the source's displayed recursion, examples and Proposition 2.5, this formalization uses zero when the eligible-leaf sum is empty. It does not use the incompatible reading that any delayed leaf forces zero despite an eligible one. Anti-unimodality uses weak inequalities and allows an endpoint minimum; the sorted witness therefore satisfies it.

Written source: Jonas J. Gebendorfer, Nonunimodal plucking polynomials with anti-unimodal delays, 14 October 2026; intake https://github.com/google-deepmind/formal-conjectures/issues/7332 . The certificate proves the finite eight-edge disproof and the general negative answer. The manuscript's larger nonmonotone-delay family and its full thirteen-term expansion are not claimed formalized; the fresh Python check reproduces that expansion separately.

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with source comparison, formalization, execution, and submission. The complete proofs use no sorry, custom axiom, native_decide, compiler-trust evaluation, or upstream placeholder theorem. Ordinary decide is reduced by Lean's kernel.

Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 are pinned by lean-toolchain and lake-manifest.json. Check out this certificate commit and obtain the pinned Mathlib cache before running the commands below. The separate audit repeats the definitions and exact quantified statement in another namespace, checking agreement and printing all relevant axiom dependencies. The plucking audit proves agreement of the recursive parent paths and polynomial by induction.

The supplied manuscript archive is attached to the intake issues: https://github.com/user-attachments/files/33452211/Gebendorfer_New_Manuscripts_2026-10-14.zip . Original authoring supplements mentioned inside those PDFs were not supplied in this batch. The archive clearly labels its fresh bounded Python checks separately. A source's historical open marker is not a fresh curator decision. No exclusive priority or independent external peer review is asserted.

The hosted audit runtime required a narrow readlink compatibility shim: only a failed /proc/own-pid/exe lookup was retried at /proc/self/exe. The official Lean binary and kernel were unchanged. The official archive SHA256 is 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Ordinary installations do not require the shim.

The upstream contribution is a statement module with a formal_proof link to this complete external proof, as PROOFS.md requests. An upstream by sorry placeholder is not claimed to be a proof; the external files and exact-statement audit have no such dependency. Formalization strengthens evidence for an existing written result and does not constitute an additional conjecture closure.

## Reproduce

```sh
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Proofs/PluckingAntiUnimodalProof.olean Proofs/PluckingAntiUnimodalProof.lean
lake env lean -DwarningAsError=true Proofs/PluckingAntiUnimodalAudit.lean
```

The printed reports must contain only propext, Classical.choice and Quot.sound, or fewer. A successful build alone is not sufficient; inspect the exact theorem and these axiom reports.

