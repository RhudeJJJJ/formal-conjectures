# Graphical Bell proof development — NOT YET CERTIFIED
This branch develops complete proofs of the two unchanged endpoints in PR7385.
Full.lean composes coefficientwise first and then the Bell corollary without using
the original admitted theorem values as proof dependencies.
The dependency chain and exact target/axiom audit are still under verification.
No complete endpoint certificate or formal_proof claim is made before all checks pass.
Locally checked so far: integer coefficient operators and both comparison identities;
finite-carrier stable partitions, deletion/extension, reconstruction; empty/counting base.
The operator axiom check reports only propext and Quot.sound.
Original statement file SHA256:
05bab9c948efbf749153c59d6ef457d2b61c5b6734d1093e97cff55de1fe8790.
Lean4.33.1 and pinned Mathlib0df444a360eaa60ab8c11dca51a86af692955474 are retained.
The bounded CI controller records actual source SHA separately from workflow event SHA,
protects original statement and pin bytes, and writes diagnostics only to this fork's
dedicated diagnostics branch. Up to6 source versions and600s repair waits,65min job limit.
Every source module must compile strictly; both complete original types must match;
transitive axioms must be standard only; both original admitted controls must be rejected.
BellBridge alone is a conditional derivation; it does not certify either original target.
