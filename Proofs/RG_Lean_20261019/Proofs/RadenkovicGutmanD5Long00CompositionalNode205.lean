/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode204
import Proofs.RadenkovicGutmanD5Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[10,0],[0]],[[0,0],[0]],[[160,0],[0]],[[0,0],[0]],[[1070,0],[0]],[[0,0],[0]],[[3880,0],[0]],[[0,0],[0]],[[8280,0],[0]],[[0,0],[0]],[[10560,10],[10]],[[0,0],[0]],[[7790,70],[70]],[[0,0],[0]],[[3000,160],[160]],[[0,0],[0]],[[450,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
