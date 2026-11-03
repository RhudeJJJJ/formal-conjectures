/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Mathlib.Tactic.FinCases
import Proofs.RadenkovicGutmanIntegerHybridBernsteinRows
import Proofs.RadenkovicGutmanEscapeReducedReserveRow00
import Proofs.RadenkovicGutmanEscapeReducedReserveRow01
import Proofs.RadenkovicGutmanEscapeReducedReserveRow02
import Proofs.RadenkovicGutmanEscapeReducedReserveRow03
import Proofs.RadenkovicGutmanEscapeReducedReserveRow04
import Proofs.RadenkovicGutmanEscapeReducedReserveRow05
import Proofs.RadenkovicGutmanEscapeReducedReserveRow06
import Proofs.RadenkovicGutmanEscapeReducedReserveRow07
import Proofs.RadenkovicGutmanEscapeReducedReserveRow08
import Proofs.RadenkovicGutmanEscapeReducedReserveRow09
import Proofs.RadenkovicGutmanEscapeReducedReserveRow10
import Proofs.RadenkovicGutmanEscapeReducedReserveRow11
import Proofs.RadenkovicGutmanEscapeReducedReserveRow12
import Proofs.RadenkovicGutmanEscapeReducedReserveRow13
import Proofs.RadenkovicGutmanEscapeReducedReserveRow14
import Proofs.RadenkovicGutmanEscapeReducedReserveRow15
import Proofs.RadenkovicGutmanEscapeReducedReserveRow16
import Proofs.RadenkovicGutmanEscapeReducedReserveRow17
import Proofs.RadenkovicGutmanEscapeReducedReserveRow18
import Proofs.RadenkovicGutmanEscapeReducedReserveRow19
import Proofs.RadenkovicGutmanEscapeReducedReserveRow20
import Proofs.RadenkovicGutmanEscapeReducedReserveRow21
import Proofs.RadenkovicGutmanEscapeReducedReserveRow22
import Proofs.RadenkovicGutmanEscapeReducedReserveRow23
import Proofs.RadenkovicGutmanEscapeReducedReserveRow24

/-!
# Original escape reserve acceptance

The complete four-dimensional Hybrid acceptance conclusion follows from all 25 exact outer Bernstein coefficient certificates.

Source: [original escape reserve polynomial and statements](https://github.com/RhudeJJJJ/formal-conjectures/blob/4ab5802ec7da33fcb4a54633e2e7c9863c974244/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanEscapeReducedReserve.lean).
-/

namespace Gebendorfer.RadenkovicGutman.EscapeReducedReserve
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private noncomputable def bernsteinRows : Fin 25 → NestedInteger.Poly 3 := ![Rows.Row00.data,Rows.Row01.data,Rows.Row02.data,Rows.Row03.data,Rows.Row04.data,Rows.Row05.data,Rows.Row06.data,Rows.Row07.data,Rows.Row08.data,Rows.Row09.data,Rows.Row10.data,Rows.Row11.data,Rows.Row12.data,Rows.Row13.data,Rows.Row14.data,Rows.Row15.data,Rows.Row16.data,Rows.Row17.data,Rows.Row18.data,Rows.Row19.data,Rows.Row20.data,Rows.Row21.data,Rows.Row22.data,Rows.Row23.data,Rows.Row24.data]

private theorem bernsteinRows_identity (j : Fin 25) :
    bernsteinRows j = NestedInteger.coefficientFrom 24 j.val 0 data := by
  fin_cases j
  · exact Rows.Row00.row_identity
  · exact Rows.Row01.row_identity
  · exact Rows.Row02.row_identity
  · exact Rows.Row03.row_identity
  · exact Rows.Row04.row_identity
  · exact Rows.Row05.row_identity
  · exact Rows.Row06.row_identity
  · exact Rows.Row07.row_identity
  · exact Rows.Row08.row_identity
  · exact Rows.Row09.row_identity
  · exact Rows.Row10.row_identity
  · exact Rows.Row11.row_identity
  · exact Rows.Row12.row_identity
  · exact Rows.Row13.row_identity
  · exact Rows.Row14.row_identity
  · exact Rows.Row15.row_identity
  · exact Rows.Row16.row_identity
  · exact Rows.Row17.row_identity
  · exact Rows.Row18.row_identity
  · exact Rows.Row19.row_identity
  · exact Rows.Row20.row_identity
  · exact Rows.Row21.row_identity
  · exact Rows.Row22.row_identity
  · exact Rows.Row23.row_identity
  · exact Rows.Row24.row_identity

private theorem bernsteinRows_accepted (j : Fin 25) :
    NestedIntegerHybrid.accepts 3 (fun i : Fin 3 => degrees i.succ) (bernsteinRows j) = true := by
  fin_cases j
  · exact Rows.Row00.accepted
  · exact Rows.Row01.accepted
  · exact Rows.Row02.accepted
  · exact Rows.Row03.accepted
  · exact Rows.Row04.accepted
  · exact Rows.Row05.accepted
  · exact Rows.Row06.accepted
  · exact Rows.Row07.accepted
  · exact Rows.Row08.accepted
  · exact Rows.Row09.accepted
  · exact Rows.Row10.accepted
  · exact Rows.Row11.accepted
  · exact Rows.Row12.accepted
  · exact Rows.Row13.accepted
  · exact Rows.Row14.accepted
  · exact Rows.Row15.accepted
  · exact Rows.Row16.accepted
  · exact Rows.Row17.accepted
  · exact Rows.Row18.accepted
  · exact Rows.Row19.accepted
  · exact Rows.Row20.accepted
  · exact Rows.Row21.accepted
  · exact Rows.Row22.accepted
  · exact Rows.Row23.accepted
  · exact Rows.Row24.accepted

theorem accepted : NestedIntegerHybrid.accepts 4 degrees data = true := by
  apply IntegerHybridBernsteinRows.checked (n := 3) degrees data bernsteinRows
  · decide +kernel
  · intro j
    exact bernsteinRows_identity j
  · intro j
    exact bernsteinRows_accepted j

#print axioms accepted
end
end Gebendorfer.RadenkovicGutman.EscapeReducedReserve
