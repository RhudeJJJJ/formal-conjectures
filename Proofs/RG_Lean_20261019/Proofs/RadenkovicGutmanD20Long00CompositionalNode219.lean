/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode065
import Proofs.RadenkovicGutmanD20Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[20],[0]],[[0,0],[0]],[[320,0],[0]],[[0,0],[0]],[[2140,0],[0]],[[0,0],[0]],[[7760,0],[0]],[[0,0],[0]],[[16560,0],[0]],[[0,0],[0]],[[21120,20],[20]],[[0,0],[0]],[[15580,140],[140]],[[0,0],[0]],[[6000,320],[320]],[[0,0],[0]],[[900,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
