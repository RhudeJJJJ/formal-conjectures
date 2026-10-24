/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode168
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e168 e120
noncomputable def p177 : NestedHorner.Poly 3 := [[[2],[]],[[0,0],[0]],[[30,0],[0]],[[0,0],[0]],[[188,0],[0]],[[0,0],[0]],[[638,0],[0]],[[0,0],[0]],[[1272,0],[0]],[[0,0],[0]],[[1514,1],[1]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step177 : p177=NestedArithmetic.mul p168 p120 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e168 e120 p168 p120 p177 rfl h168 h120 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
