/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode030
import Proofs.RadenkovicGutmanD39Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e042 : NestedArithmetic.Expr 3 := .times e030 e028
noncomputable def p042 : NestedHorner.Poly 3 := [[[0],[0]],[[0,117],[117]],[[0,0],[0]],[[2106,507],[507]],[[0,0],[0]],[[14742,624],[624]],[[0,0],[0]],[[40716,273],[273]],[[0,0],[0]],[[59046,39],[39]],[[0]],[[49608]],[[0]],[[24882]],[[0]],[[7332]],[[0]],[[1170]],[[0]],[[78]]]
theorem step042 : p042=NestedArithmetic.mul p030 p028 := by decide +kernel
#print axioms step042
theorem h042 : NestedArithmetic.compile e042=p042 := StagedExprCompile.compile_times e042 e030 e028 p030 p028 p042 rfl h030 h028 step042
#print axioms h042
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
