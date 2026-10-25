/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode119
import Proofs.RadenkovicGutmanD20Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-532,0],[0,0]],[[0,0],[0,0]],[[-3272,0],[0,0]],[[0,0],[0,0]],[[-10836,0],[0,0]],[[0,0],[0,0]],[[-20896,0],[0,0]],[[0,0],[0,0]],[[-23664,-36],[-36,0]],[[0,0],[0,0]],[[-14840,-288],[-288,0]],[[0,0],[0,0]],[[-3892,-792],[-792,0]],[[0,0],[0,0]],[[516,-864],[-864,0]],[[0,0],[0,0]],[[396,-324],[-324,0]],[[0],[0,0]],[[0],[0,-36]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
