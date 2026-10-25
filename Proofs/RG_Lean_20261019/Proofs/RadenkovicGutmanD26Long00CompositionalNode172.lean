/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode171
import Proofs.RadenkovicGutmanD26Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[52,0],[0]],[[0,0],[0]],[[780,0],[0]],[[0,0],[0]],[[4888,0],[0]],[[0,0],[0]],[[16588,0],[0]],[[0,0],[0]],[[33072,0],[0]],[[0,0],[0]],[[39364,26],[26]],[[0,0],[0]],[[27144,182],[182]],[[0,0],[0]],[[9828,416],[416]],[[0,0],[0]],[[1404,338],[338]],[[0,0],[0]],[[0,78],[78]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
