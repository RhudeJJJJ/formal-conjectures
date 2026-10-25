/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode030
import Proofs.RadenkovicGutmanD20Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[20],[0]],[[0,0],[0]],[[320,0],[0]],[[0,0],[0]],[[2140,0],[0]],[[0,0],[0]],[[7760,0],[0]],[[0,0],[0]],[[16560,0],[0]],[[0,0],[0]],[[21120,20],[20]],[[0,0],[0]],[[15580,140],[140]],[[0,0],[0]],[[6000,320],[320]],[[0,0],[0]],[[900,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
