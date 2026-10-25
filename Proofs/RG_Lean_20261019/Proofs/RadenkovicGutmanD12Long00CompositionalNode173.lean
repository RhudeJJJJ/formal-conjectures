/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode165
import Proofs.RadenkovicGutmanD12Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-268,0],[0,0]],[[0,0],[0,0]],[[-1408,0],[0,0]],[[0,0],[0,0]],[[-3476,0],[0,0]],[[0,0],[0,0]],[[-3064,0],[0,0]],[[0,0],[0,0]],[[3696,-20],[-20,0]],[[0,0],[0,0]],[[11552,-148],[-148,0]],[[0,0],[0,0]],[[11308,-356],[-356,0]],[[0,0],[0,0]],[[5100,-288],[-288,0]],[[0,0],[0,0]],[[900,-24],[-24,0]],[[0,0],[0,0]],[[0,36],[36,-20]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
