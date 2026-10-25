/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode030
import Proofs.RadenkovicGutmanD26Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[52],[0]],[[0,0],[0]],[[780,0],[0]],[[0,0],[0]],[[4888,0],[0]],[[0,0],[0]],[[16588,0],[0]],[[0,0],[0]],[[33072,0],[0]],[[0,0],[0]],[[39364,26],[26]],[[0,0],[0]],[[27144,182],[182]],[[0,0],[0]],[[9828,416],[416]],[[0,0],[0]],[[1404,338],[338]],[[0,0],[0]],[[0,78],[78]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
