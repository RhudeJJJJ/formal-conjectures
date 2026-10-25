/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode204
import Proofs.RadenkovicGutmanD10Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[20,0],[0]],[[0,0],[0]],[[320,0],[0]],[[0,0],[0]],[[2140,0],[0]],[[0,0],[0]],[[7760,0],[0]],[[0,0],[0]],[[16560,0],[0]],[[0,0],[0]],[[21120,20],[20]],[[0,0],[0]],[[15580,140],[140]],[[0,0],[0]],[[6000,320],[320]],[[0,0],[0]],[[900,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
