# Complete Lean certificate: WOWII 416

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization, source comparison, execution and submission.

The printed inequality and its strengthening without minus two are proved for every finite simple connected graph of order greater than two with all pairwise distances at most two. Neighborhoods are unions of open vertex neighborhoods; isolates are tested in the induced graph. The proof shows each relevant isolate is a leaf and proves the leaf-union exchange from the exact largest-critical definition. It does not formalize the manuscript's complete universal-vertex/disjoint-union family classification or the unresolved diameter-free printed inequality.

## Source and reproducibility

The written manuscript and frozen WOWII HTML/JavaScript are attached to [the existing intake](https://github.com/google-deepmind/formal-conjectures/issues/7270). The archive's historical O labels are not a new live-status or priority claim. Neighborhood definition46 is the union of open neighborhoods and may meet its argument. Critical difference is integer subtraction; maximum critical means maximum cardinality among difference maximizers, including the empty-set boundary case.

Pinned Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, as in this repository's lean-toolchain and lake-manifest.json. After checking out this certificate commit and obtaining the pinned Mathlib cache:

```sh
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/CriticalIndependentProof.olean Proofs/CriticalIndependentProof.lean
lake env lean -o .lake/build/lib/lean/Proofs/WOWII416Proof.olean Proofs/WOWII416Proof.lean
lake env lean Proofs/WOWII416Audit.lean
```

The separate audit rewrites the source target and imports complete proof files only; no upstream placeholder theorem is used. All printed axiom reports contain only propext, Classical.choice and Quot.sound (or fewer). No sorry, custom axioms or native_decide occur in these certificates. Ordinary decide steps are kernel-reduced finite facts; large candidate independent-dominating sets are treated structurally, not enumerated.

On the hosted audit machine, a narrow readlink compatibility shim replaced only a failed /proc/own-pid/exe lookup by /proc/self/exe. The official Lean executable, elaborator and kernel were unchanged. The verified official toolchain archive SHA256 was 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Normal installations do not need this shim.

Upstream is a statement repository: its body remains by sorry, with formal_proof pointing to the immutable complete external certificate. A successful local proof audit or CI build is not an independent peer review or a merge. These formalizations strengthen the evidence for existing written results and are not additional discovered conjecture closures.
