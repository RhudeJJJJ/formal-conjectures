# Graphical Stirling and Bell minima

This self-contained source snapshot is the first pair in the migration of
formal-conjectures PR7385 from its legacy proof-link exemption to a genuine
Palomar record. It is not registered merely by existing or passing preflight.

`Challenge.lean` states both original mathematical targets with standalone
copies of the ordinary definitions and only canonical Mathlib imports.
`Solution.lean` imports the complete18-module proof. Comparator compares
`PHOEG.GraphicalBell.full_coefficientwise` first and
`PHOEG.GraphicalBell.full_conjecture` second, permitting only propext,
Classical.choice and Quot.sound. Its separate Challenge is deliberately
admitted; the Solution proof dependencies must contain no sorryAx.

The statement counts partitions into nonempty independent unlabeled blocks.
It applies to every finite simple graph of order at least1, with no
connectedness assumption. The Bell claim follows by summing the proved
coefficientwise inequalities. No first-priority claim, ordinary monomial
coefficient comparison, or uniqueness classification is made. The graph
colouring and extremal-enumeration audience is the one identified by the
PHOEG fixed-order/fixed-size problem; novelty has not been independently
established by this port.

The complete substantive source is included here under Apache-2.0, ported
from commit62f9346442c8757cad34bc4c9b295f29260684d2. Its18 proof modules gain
module and visibility declarations, warnings as errors, and the Lean4.35
replacements if_pos/if_neg -> ite_eq_left/ite_eq_right. The statement
definitions are retained; unused admitted targets, repository linter
attributes and the old negative-control audit module are omitted. The small
Challenge spells the same endpoint types; Comparator must test that claim.
Any later compatibility fixes are recorded as source changes rather than
attributed to the old checked bytes.

Earlier proof evidence:
https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/40201620527
This is historical Lean4.33.1 evidence, not proof that the new port passed.
Original statement PR: https://github.com/google-deepmind/formal-conjectures/pull/7385

Current toolchain: leanprover/lean4:v4.35.0.
Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679 (canonicalv4.35.0 release).
Palomar reusable verifier: 14aa8d6b3c2f14a8540605e37144560b9a00e7e7, modefull, palomar-standard-v1.
The current source requirement minimum isv4.35.0-rc2; the old certificate's
toolchain cannot be submitted as a new result unchanged.

The exact mathematical source references, AI production role, review limits
and human responsibility are in formalization.yaml. This repository contains
the full proof development and does not import the old formal-conjectures
fork. A new isolated branch keeps all existing submission branches intact.

Run `lake exe cache get`, then `lake build`. The complete pinned Palomar
workflow performs the stronger Challenge/Solution comparison, dependency
audit and independent kernel checks. Passing it remains a preflight; final
registration follows verification, the actual editorial review and the
user's decision about publishing that review and immutable record.
