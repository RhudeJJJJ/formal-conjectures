# Radenković–Gutman Lean formalization

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

Status on 26 October 2026: **incomplete; no full Lean proof has been submitted**.
The written computer-assisted proof and the original statement submission are distinct from completion of this Lean project.

The target is the two statements in [PR #7399](https://github.com/google-deepmind/formal-conjectures/pull/7399), at statement commit `3654bf2bddc5217f904b7b85207b1091e833de49`: for every positive order and every tree on `Fin n`, the path minimizes actual Laplacian energy, with equality exactly for a graph isomorphic to the path. Energy is centered at the actual mean degree `2m/n`.

[SubmissionStatement](Proofs/RadenkovicGutmanSubmissionStatement.lean) copies that energy definition exactly and proves the statement bridge from `GlobalAssembly.Conclusion`. Its independent kernel control is queued separately. [CompleteOriginalProof](Proofs/RadenkovicGutmanCompleteOriginalProof.lean) contains the intended unconditional `path_minimum` and `path_equality` declarations. That endpoint has **not** passed the full kernel check. Its presence in source is not a proof-completion claim.

The exact seven required inputs are in [OriginalAssembly](Proofs/RadenkovicGutmanOriginalAssembly.lean). Three have complete original kernel-object and current source-closure audits: degree one through order13, degree at least four through order12 (all247 actual-tree comparisons and coverage), and degree at least46. Four remain open in this formalization: degree one at orders14–52, degree one from order53, degree two or three, and degrees4–45 from order13.

Within the degree-one large-order input,14 of15 arm classes are closed. The remaining class has the original122 interval trees and1,754 leaf positions; alternate proof routes preserve each position and its original payment. Original analytic anchors, their actual-tree predicates, individual repair leaves, complete arm classes, and complete input families are counted separately. Successful partial certificates do not close a larger range.

The project pins Lean4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The kernel verifier enforces source and dependency hashes, strict warnings, authenticated original object outputs including module sidecars, and axiom profiles contained in `{propext, Classical.choice, Quot.sound}`. Native computation proposes exact witnesses; the kernel must check every required identity and certificate.

The CI workflows under `.github/workflows/rg-*.yml` materialize the explicitly selected numerical sources from pinned packets, restore independently audited parents, and bound each fresh kernel frontier. The independent exact-statement control is `rg-exact-submission-statement-bridge.yml`. The complete endpoint must additionally pass after every original input family has closed.

The upstream PR remains a statement contribution with its two statement placeholders. No `formal_proof` attribute or complete-proof claim may be added on the strength of these partial results. Final submission requires the exact two target declarations, a full successful source-bound kernel receipt, and their standard-axiom profiles.
