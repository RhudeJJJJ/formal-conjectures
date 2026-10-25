/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode167
import Proofs.RadenkovicGutmanD7Long00CompositionalNode169
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e170 : NestedArithmetic.Expr 3 := .plus e167 e169
noncomputable def p170 : NestedHorner.Poly 3 := [[[2],[]],[[0,0],[0]],[[30,0],[0]],[[0,0],[0]],[[188,0],[0]],[[0,0],[0]],[[638,0],[0]],[[0,0],[0]],[[1272,0],[0]],[[0,0],[0]],[[1514,1],[1]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step170 : p170=NestedHorner.add p167 p169 := by decide +kernel
#print axioms step170
theorem h170 : NestedArithmetic.compile e170=p170 := StagedExprCompile.compile_plus e170 e167 e169 p167 p169 p170 rfl h167 h169 step170
#print axioms h170
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
