/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode178
import Proofs.RadenkovicGutmanD15Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-427,0],[0,0]],[[0,0],[0,0]],[[-2932,0],[0,0]],[[0,0],[0,0]],[[-10901,0],[0,0]],[[0,0],[0,0]],[[-23716,0],[0,0]],[[0,0],[0,0]],[[-30324,-26],[-26,0]],[[0,0],[0,0]],[[-21340,-193],[-193,0]],[[0,0],[0,0]],[[-6437,-467],[-467,0]],[[0,0],[0,0]],[[366,-384],[-384,0]],[[0,0],[0,0]],[[441,-39],[-39,0]],[[0,0],[0,0]],[[0,45],[45,-26]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
