# Complete Lean certificate: WOWII 420

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization, source comparison, execution and submission.

Both reconstructed universal upper bounds are disproved by W8 on 36 vertices. The independent domination number is exactly10: a structural injection into any independent dominating set supplies the lower bound, and an explicit 10-element set supplies the upper bound. The residual is empty, the closed minimum-degree neighborhood has 3 edges and precisely 2 vertices minimize incident triangles, so the right sides are 8 and 4. TriangleCountProof proves an actual bijection with the repository's incident 3-clique invariant. The external-neighborhood variants, all-parameter counterfamily and minimality claims are not part of these formal targets. Missing source comparison glyphs are disclosed; the intended <= direction is determined by the source's triangle-free note.

## Source and reproducibility

The written manuscript and frozen WOWII HTML/JavaScript are attached to [the existing intake](https://github.com/google-deepmind/formal-conjectures/issues/7234). The archive's historical O labels are not a new live-status or priority claim. Neighborhood definition46 is the union of open neighborhoods and may meet its argument. Critical difference is integer subtraction; maximum critical means maximum cardinality among difference maximizers, including the empty-set boundary case.

Pinned Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, as in this repository's lean-toolchain and lake-manifest.json. After checking out this certificate commit and obtaining the pinned Mathlib cache:

```sh
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/TriangleCountProof.olean Proofs/TriangleCountProof.lean
lake env lean -o .lake/build/lib/lean/Proofs/WOWII420Proof.olean Proofs/WOWII420Proof.lean
lake env lean Proofs/WOWII420Audit.lean
```

The separate audit rewrites the source target and imports complete proof files only; no upstream placeholder theorem is used. All printed axiom reports contain only propext, Classical.choice and Quot.sound (or fewer). No sorry, custom axioms or native_decide occur in these certificates. Ordinary decide steps are kernel-reduced finite facts; large candidate independent-dominating sets are treated structurally, not enumerated.

On the hosted audit machine, a narrow readlink compatibility shim replaced only a failed /proc/own-pid/exe lookup by /proc/self/exe. The official Lean executable, elaborator and kernel were unchanged. The verified official toolchain archive SHA256 was 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Normal installations do not need this shim.

Upstream is a statement repository: its body remains by sorry, with formal_proof pointing to the immutable complete external certificate. A successful local proof audit or CI build is not an independent peer review or a merge. These formalizations strengthen the evidence for existing written results and are not additional discovered conjecture closures.
