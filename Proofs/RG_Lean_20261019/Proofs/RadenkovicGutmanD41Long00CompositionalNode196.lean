/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode195
import Proofs.RadenkovicGutmanD41Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[164,0],[0]],[[0,0],[0]],[[2460,0],[0]],[[0,0],[0]],[[15416,0],[0]],[[0,0],[0]],[[52316,0],[0]],[[0,0],[0]],[[104304,0],[0]],[[0,0],[0]],[[124148,82],[82]],[[0,0],[0]],[[85608,574],[574]],[[0,0],[0]],[[30996,1312],[1312]],[[0,0],[0]],[[4428,1066],[1066]],[[0,0],[0]],[[0,246],[246]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
