/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode119
import Proofs.RadenkovicGutmanD7Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-142,0],[0,0]],[[0,0],[0,0]],[[-828,0],[0,0]],[[0,0],[0,0]],[[-2542,0],[0,0]],[[0,0],[0,0]],[[-4360,0],[0,0]],[[0,0],[0,0]],[[-4008,-10],[-10,0]],[[0,0],[0,0]],[[-1476,-80],[-80,0]],[[0,0],[0,0]],[[450,-220],[-220,0]],[[0,0],[0,0]],[[594,-240],[-240,0]],[[0,0],[0,0]],[[162,-90],[-90,0]],[[0],[0,0]],[[0],[0,-10]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
