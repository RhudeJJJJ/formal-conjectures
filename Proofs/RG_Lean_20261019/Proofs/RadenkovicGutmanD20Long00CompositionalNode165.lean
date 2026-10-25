/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode164
import Proofs.RadenkovicGutmanD20Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-532,0],[0,0]],[[0,0],[0,0]],[[-3272,0],[0,0]],[[0,0],[0,0]],[[-10836,0],[0,0]],[[0,0],[0,0]],[[-20896,0],[0,0]],[[0,0],[0,0]],[[-23664,-36],[-36,0]],[[0,0],[0,0]],[[-14840,-288],[-288,0]],[[0,0],[0,0]],[[-3892,-792],[-792,0]],[[0,0],[0,0]],[[516,-864],[-864,0]],[[0,0],[0,0]],[[396,-324],[-324,0]],[[0],[0,0]],[[0],[0,-36]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
