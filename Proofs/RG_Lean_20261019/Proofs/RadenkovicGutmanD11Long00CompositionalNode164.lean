/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode119
import Proofs.RadenkovicGutmanD11Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-262,0],[0,0]],[[0,0],[0,0]],[[-1580,0],[0,0]],[[0,0],[0,0]],[[-5094,0],[0,0]],[[0,0],[0,0]],[[-9448,0],[0,0]],[[0,0],[0,0]],[[-10056,-18],[-18,0]],[[0,0],[0,0]],[[-5588,-144],[-144,0]],[[0,0],[0,0]],[[-886,-396],[-396,0]],[[0,0],[0,0]],[[570,-432],[-432,0]],[[0,0],[0,0]],[[234,-162],[-162,0]],[[0],[0,0]],[[0],[0,-18]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
