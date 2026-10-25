/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode184
import Proofs.RadenkovicGutmanD23Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[23,0],[0]],[[0,0],[0]],[[368,0],[0]],[[0,0],[0]],[[2461,0],[0]],[[0,0],[0]],[[8924,0],[0]],[[0,0],[0]],[[19044,0],[0]],[[0,0],[0]],[[24288,23],[23]],[[0,0],[0]],[[17917,161],[161]],[[0,0],[0]],[[6900,368],[368]],[[0,0],[0]],[[1035,299],[299]],[[0,0],[0]],[[0,69],[69]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
